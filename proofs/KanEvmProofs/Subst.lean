import KanEvmProofs.Syntax
import KanEvmProofs.Check

/-! # Substitution of the finite fragment

This module mirrors `map_variables`, `map_entries`, `substitute_core` and `substitute` at lib/finite_term.ml lines 112 to 156.
Decision S2-D5 replaces the higher order `map_variables` with two first order structural pairs.
`shift` with `shiftEntries` is the first pair, and `sub` with `subEntries` is the second one.
Decision S2-D8 fixes the cutoff rule of both pairs. Each pair spends one unit of the budget for one term node, as lib/finite_term.ml line 113 does.
-/

mutual
/-- `shift` mirrors the raising instance of `map_variables` at lib/finite_term.ml lines 112 to 135.
The callback is the inner one at lines 147 and 148.
`c` is the cutoff and `d` is the raise, and `fuel` is the budget that the walk threads.
An index below the cutoff stays, and an index at the cutoff or above it rises `d` units.
Decision S2-D5 makes this pair first order, and decision S2-D8 fixes the cutoff rule.
The cutoff rises one unit inside each `case` branch and nowhere else, as line 125 shows.
`tick` runs once for one term node, as line 113 does, so this function adds no charge point.
-/
def shift (c d : Nat) (fuel : Nat) (t : Term) : Res (Term × Nat) :=
  tick fuel >>= fun fuel =>
    match t with
    | .var index =>
        .ok (Term.var (if index < c then index else index + d), fuel)
    | .atom label =>
        .ok (Term.atom label, fuel)
    | .tag label payload =>
        shift c d fuel payload >>= fun result =>
          .ok (Term.tag label result.1, result.2)
    | .«section» fields =>
        shiftEntries c d fuel fields >>= fun result =>
          .ok (Term.«section» result.1, result.2)
    | .«case» scrutinee scrutineeType branches =>
        shift c d fuel scrutinee >>= fun head =>
          shiftEntries (c + 1) d head.2 branches >>= fun rest =>
            .ok (Term.«case» head.1 scrutineeType rest.1, rest.2)
    | .project field sectionType label =>
        shift c d fuel field >>= fun result =>
          .ok (Term.project result.1 sectionType label, result.2)

/-- `shiftEntries` mirrors `map_entries` at lib/finite_term.ml lines 130 to 135.
It walks the field list of a `section` node or the branch list of a `case` node.
It keeps the source order of the labels, and it threads one budget through the whole list.
`shiftEntries` holds no charge point, since `shift` holds the only one, as line 113 shows.
-/
def shiftEntries (c d : Nat) (fuel : Nat) (entries : List (String × Term)) :
    Res (List (String × Term) × Nat) :=
  match entries with
  | [] => .ok ([], fuel)
  | (label, field) :: rest =>
      shift c d fuel field >>= fun head =>
        shiftEntries c d head.2 rest >>= fun tail =>
          .ok ((label, head.1) :: tail.1, tail.2)
end

mutual
/-- `sub` mirrors the replacing instance of `map_variables` at lib/finite_term.ml lines 112 to 151.
The callback is the outer one at lines 140 to 149.
`d` is the binder depth, `r` is the replacement term, and `fuel` is the threaded budget.
An index below the depth stays, as line 141 shows.
An index above the depth drops one unit, as line 142 shows.
An index equal to the depth becomes the replacement, raised `d` units through `shift`.
That raise mirrors lines 146 to 149, and it calls another function, so it needs no gas.
Decision S2-D8 fixes the cutoff rule, and the depth rises one unit inside each `case` branch.
`tick` runs once for one term node, as line 113 does, so this function adds no charge point.
-/
def sub (d : Nat) (r : Term) (fuel : Nat) (t : Term) : Res (Term × Nat) :=
  tick fuel >>= fun fuel =>
    match t with
    | .var index =>
        if index < d then .ok (Term.var index, fuel)
        else if d < index then .ok (Term.var (index - 1), fuel)
        else shift 0 d fuel r
    | .atom label =>
        .ok (Term.atom label, fuel)
    | .tag label payload =>
        sub d r fuel payload >>= fun result =>
          .ok (Term.tag label result.1, result.2)
    | .«section» fields =>
        subEntries d r fuel fields >>= fun result =>
          .ok (Term.«section» result.1, result.2)
    | .«case» scrutinee scrutineeType branches =>
        sub d r fuel scrutinee >>= fun head =>
          subEntries (d + 1) r head.2 branches >>= fun rest =>
            .ok (Term.«case» head.1 scrutineeType rest.1, rest.2)
    | .project field sectionType label =>
        sub d r fuel field >>= fun result =>
          .ok (Term.project result.1 sectionType label, result.2)

/-- `subEntries` mirrors `map_entries` at lib/finite_term.ml lines 130 to 135.
It walks the field list of a `section` node or the branch list of a `case` node.
It keeps the source order of the labels, and it threads one budget through the whole list.
`subEntries` holds no charge point, since `sub` holds the only one, as line 113 shows.
-/
def subEntries (d : Nat) (r : Term) (fuel : Nat) (entries : List (String × Term)) :
    Res (List (String × Term) × Nat) :=
  match entries with
  | [] => .ok ([], fuel)
  | (label, field) :: rest =>
      sub d r fuel field >>= fun head =>
        subEntries d r head.2 rest >>= fun tail =>
          .ok ((label, head.1) :: tail.1, tail.2)
end

mutual
/-- `occurrences` counts the free uses of one variable inside a term.
It counts each `var d` node that sits at binder depth `d`, per decision S2-D5.
The depth rises one unit inside each `case` branch, which mirrors lib/finite_term.ml line 125.
That rule is the one of decision S2-D8, so this count agrees with the walk of `sub`.
Row Lemma2b of the theorem inventory reads `occurrences 0 body` for the cost of a case of a tag.
Row Theorem3-C2 reads `occurrences 0 b` for the fuel that `substitute` needs.
-/
def occurrences (d : Nat) (t : Term) : Nat :=
  match t with
  | .var index => if index = d then 1 else 0
  | .atom .. => 0
  | .tag _label payload => occurrences d payload
  | .«section» fields => occurrencesEntries d fields
  | .«case» scrutinee _scrutineeType branches =>
      occurrences d scrutinee + occurrencesEntries (d + 1) branches
  | .project field .. => occurrences d field

/-- `occurrencesEntries` counts the free uses of one variable inside an entry list.
`occurrencesEntries` is the list partner of `occurrences` for the nested inductive of S2-D1.
The depth reaches each entry unchanged, since `occurrences` raises it at the `case` node.
`occurrencesEntries` has no image in lib/finite_term.ml, and it carries the occurrence count `n` of claim C2 of docs/metatheory.md lines 213 to 216.
-/
def occurrencesEntries (d : Nat) (entries : List (String × Term)) : Nat :=
  match entries with
  | [] => 0
  | (_label, field) :: rest => occurrences d field + occurrencesEntries d rest
end

/-- `substituteCore` mirrors `substitute_core` at lib/finite_term.ml lines 139 to 151.
It puts the replacement term at index zero of the body, and it checks nothing.
The OCaml form builds a callback and hands it to `map_variables` at line 151.
The Lean form is one call of `sub` at depth zero, per decision S2-D5.
It returns the new term together with the remaining budget, as line 151 does.
-/
def substituteCore (fuel : Nat) (replacement body : Term) : Res (Term × Nat) :=
  sub 0 replacement fuel body

/-- `substitute` mirrors the OCaml `substitute` at lib/finite_term.ml lines 153 to 156.
It checks the replacement at its own type, as line 154 does.
It then checks the body at the extended context, as line 155 does.
It then runs `substituteCore` on the budget that the two checks leave, as line 156 does.
The three steps thread one budget, and this function adds no charge point, per decision S2-D4.
The gas of each `checkCore` call is `2 * fuel + 2`, which mirrors `check` at line 108.
It drops the remaining budget and it returns the new term alone.
-/
def substitute (fuel : Nat) (ctx : List Ty) (replacement : Term) (replacementType : Ty)
    (body : Term) (expected : Ty) : Res Term :=
  checkCore (2 * fuel + 2) fuel ctx replacement replacementType >>= fun fuel =>
    checkCore (2 * fuel + 2) fuel (replacementType :: ctx) body expected >>= fun fuel =>
      substituteCore fuel replacement body >>= fun result => .ok result.1
