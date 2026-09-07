import KanEvmProofs.Syntax
import KanEvmProofs.Check
import KanEvmProofs.Subst

/-! # Reduction of the finite fragment

This module mirrors `reduce` at lib/finite_term.ml lines 162 to 225.
It also mirrors `normalize` at lib/finite_term.ml lines 227 to 229.
Decision S2-D6 gives `reduce` a structural gas parameter, since a substituted body is no subterm.
This module holds definitions alone. It states no theorem and it holds no example.
It never imports KanEvmProofs.Typing, so the typing rules reach no definition here.
-/

/-- `reduceFields` mirrors `reduce_fields` at lib/finite_term.ml lines 211 to 216.
It walks the aligned field list of a `section` node and it keeps the label order of that list.
Each field reduces at the fiber type of its own label, as line 214 shows.
It threads one budget through the whole list, and it holds no charge point of its own.
`step` is the reduction of one field, and `reduce` supplies `reduce gasPred` at each call site.
The gas of `step` is the same for every element of the list, as decision S2-D6 asks of this helper.
The step parameter stands in place of a gas parameter of the same value.
A gas parameter here makes the recursion well founded, since a gas that stays the same is no measure, and
Lean then marks `reduce` irreducible and no example of the module reaches a value.
Probed at Lean v4.33.1. The step form compiles through `Nat.brecOn` and an example closes with `rfl`.
-/
def reduceFields (step : Nat → Term → Ty → Res (Term × Nat)) (fuel : Nat)
    (fields : List (String × Ty × Term)) : Res (List (String × Term) × Nat) :=
  match fields with
  | [] => .ok ([], fuel)
  | (label, fiber, field) :: rest =>
      step fuel field fiber >>= fun head =>
        reduceFields step head.2 rest >>= fun tail =>
          .ok ((label, head.1) :: tail.1, tail.2)

/-- `reduceBranches` mirrors `reduce_branches` at lib/finite_term.ml lines 219 to 225.
It walks the aligned branch list of a neutral `case` node and it keeps the label order.
Each body reduces at the expected type of the whole node, as line 223 shows.
The aligned fiber binds the payload at index zero and it directs no step, as lines 217 and 218 state.
It threads one budget through the whole list, and it holds no charge point of its own.
`step` is the reduction of one body, and `reduce` supplies `reduce gasPred` at the one call site.
The gas of `step` is the same for every element of the list, as decision S2-D6 asks of this helper.
The docstring of `reduceFields` records why the step parameter stands in place of a gas parameter.
-/
def reduceBranches (step : Nat → Term → Ty → Res (Term × Nat)) (fuel : Nat)
    (fields : List (String × Ty × Term)) (expected : Ty) : Res (List (String × Term) × Nat) :=
  match fields with
  | [] => .ok ([], fuel)
  | (label, _fiber, body) :: rest =>
      step fuel body expected >>= fun head =>
        reduceBranches step head.2 rest expected >>= fun tail =>
          .ok ((label, head.1) :: tail.1, tail.2)

/-- `reduce` mirrors the OCaml `reduce` at lib/finite_term.ml lines 162 to 225.
It ticks once for one entered node, as line 163 does, and that tick runs ahead of every nested call.
Decision S2-D6 puts the structural gas parameter ahead of the budget.
An empty gas returns `Err.resourceExhausted`, and each nested call of this function gets `gas - 1`.
A `case` of a `tag` substitutes the payload into the branch body, as lines 187 to 190 show.
That body is no subterm of the input, which is the reason for the gas parameter.
The two list helpers take the step `reduce gasPred`, so one list walk runs at one gas value.
The expected type and the annotations direct every step, so reduction needs no context.
The comment at lines 158 to 161 states that last rule.
The `checkCore` block of Check.lean and `reduce` hold the two gas disciplines, per decisions
S2-D5 and S2-D6.
-/
def reduce (gas fuel : Nat) (t : Term) (expected : Ty) : Res (Term × Nat) :=
  match gas with
  | 0 => .error .resourceExhausted
  | gasPred + 1 =>
      tick fuel >>= fun fuel =>
        match t with
        | .var index =>
            .ok (Term.var index, fuel)
        | .atom label =>
            .ok (Term.atom label, fuel)
        | .tag label payload =>
            match expected with
            | .lan fibers =>
                lookup label fibers >>= fun fiber =>
                  reduce gasPred fuel payload fiber >>= fun result =>
                    .ok (Term.tag label result.1, result.2)
            | .atoms .. => .error .expectedLan
            | .ran .. => .error .expectedLan
        | .«section» entries =>
            match expected with
            | .ran fibers =>
                canonicalEntries entries >>= fun sorted =>
                  align fibers sorted >>= fun fields =>
                    reduceFields (fun f x a => reduce gasPred f x a) fuel fields >>= fun result =>
                      .ok (Term.«section» result.1, result.2)
            | .atoms .. => .error .expectedRan
            | .lan .. => .error .expectedRan
        | .«case» scrutinee scrutineeType branches =>
            match scrutineeType with
            | .lan fibers =>
                canonicalEntries branches >>= fun sorted =>
                  reduce gasPred fuel scrutinee scrutineeType >>= fun head =>
                    match head.1 with
                    | .tag label payload =>
                        lookup label sorted >>= fun body =>
                          substituteCore head.2 payload body >>= fun opened =>
                            reduce gasPred opened.2 opened.1 expected
                    | .var index =>
                        align fibers sorted >>= fun fields =>
                          reduceBranches (fun f x a => reduce gasPred f x a) head.2 fields expected
                            >>= fun rest =>
                              .ok (Term.«case» (Term.var index) scrutineeType rest.1, rest.2)
                    | .«case» inner innerType innerBranches =>
                        align fibers sorted >>= fun fields =>
                          reduceBranches (fun f x a => reduce gasPred f x a) head.2 fields expected
                            >>= fun rest =>
                              .ok (Term.«case» (Term.«case» inner innerType innerBranches)
                                scrutineeType rest.1, rest.2)
                    | .project inner innerType innerLabel =>
                        align fibers sorted >>= fun fields =>
                          reduceBranches (fun f x a => reduce gasPred f x a) head.2 fields expected
                            >>= fun rest =>
                              .ok (Term.«case» (Term.project inner innerType innerLabel)
                                scrutineeType rest.1, rest.2)
                    | .atom .. => .error .expectedLan
                    | .«section» .. => .error .expectedLan
            | .atoms .. => .error .expectedLan
            | .ran .. => .error .expectedLan
        | .project field sectionType label =>
            match sectionType with
            | .ran fibers =>
                lookup label fibers >>= fun actual =>
                  if actual == expected then
                    reduce gasPred fuel field sectionType >>= fun head =>
                      match head.1 with
                      | .«section» entries =>
                          lookup label entries >>= fun found => .ok (found, head.2)
                      | .var index =>
                          .ok (Term.project (Term.var index) sectionType label, head.2)
                      | .«case» inner innerType innerBranches =>
                          .ok (Term.project (Term.«case» inner innerType innerBranches)
                            sectionType label, head.2)
                      | .project inner innerType innerLabel =>
                          .ok (Term.project (Term.project inner innerType innerLabel)
                            sectionType label, head.2)
                      | .atom .. => .error .expectedRan
                      | .tag .. => .error .expectedRan
                  else .error .typeMismatch
            | .atoms .. => .error .expectedRan
            | .lan .. => .error .expectedRan

/-- `normalize` mirrors the OCaml `normalize` at lib/finite_term.ml lines 227 to 229.
It checks the term at the expected type, as line 228 does, then it reduces it, as line 229 does.
The two steps thread one budget, and this function adds no charge point, per decision S2-D4.
The gas of `checkCore` is `2 * fuel + 2`, which mirrors `check` at line 108.
The gas of `reduce` is one unit above the budget that the check leaves, per decision S2-D6.
That setting is enough, since one nested call of `reduce` drops the gas one unit.
`normalize` carries no gas parameter, and it supplies the gas of `checkCore` and of `reduce`.
It drops the remaining budget and it returns the reduced term alone, as line 229 does.
-/
def normalize (fuel : Nat) (ctx : List Ty) (t : Term) (expected : Ty) : Res Term :=
  checkCore (2 * fuel + 2) fuel ctx t expected >>= fun fuel =>
    reduce (fuel + 1) fuel t expected >>= fun result => .ok result.1
