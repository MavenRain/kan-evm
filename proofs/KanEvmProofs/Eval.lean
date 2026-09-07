import KanEvmProofs.Syntax
import KanEvmProofs.Check

/-! # Evaluation of the finite fragment

This module mirrors the evaluator at lib/finite_term.ml lines 231 to 270.
It holds the value type, the mutual structural triple of decision S2-D5 and the entry point `run`.
It also holds `quote` of docs/metatheory.md lines 383 to 386, which Theorem6-11.5 needs.
Decision S2-D4 keeps `tick` as the only charge point, and no definition here carries gas.
-/

/-- `Value` mirrors the OCaml type `value` at lib/finite_term.ml lines 231 to 234.
`atom` holds one atom name. `tag` holds one label and one payload value.
`section` holds one field list in the ascending label order of `canonicalEntries`.
The name `section` is a Lean keyword, so that constructor takes the guillemet form.
Decision S2-D1 keeps the `List` nesting, so this is a nested inductive.
-/
inductive Value where
  | atom (name : String)
  | tag (label : String) (payload : Value)
  | «section» (fields : List (String × Value))
  deriving Repr

mutual
/-- `evaluate` mirrors the OCaml `evaluate` at lib/finite_term.ml lines 236 to 260.
It ticks once, per decision S2-D4, then it reads the term and the environment.
Decision S2-D5 makes this function the head of a mutual structural triple.
The OCaml case arm at lines 252 and 253 recurses on a branch body that is no subterm, so `evaluateBranch` walks the syntactic branch list of the same
`case` node instead. The variable arm mirrors `variable` at lines 43 to 45 over a value list, since the
`variable` of Check.lean reads a context of types. The section arm mirrors line 245 and it differs in one point.
The OCaml arm sorts the field terms first and it evaluates in that order.
This arm evaluates in source order and it sorts the field values, which returns the same value and the same remaining budget on every success.
The two arms can report a different error when two fields fail with different errors.
`evaluate` is no exported name of lib/finite_term.mli, and `run` at lines 268 to 270 checks the term first, so the reachable difference is one
`resourceExhausted` report, which both orders return alike.
-/
def evaluate (fuel : Nat) (rho : List Value) (t : Term) : Res (Value × Nat) :=
  tick fuel >>= fun fuel =>
    match t with
    | .var index =>
        (rho[index]?).elim (.error (.invalidVariable index)) (fun value => .ok (value, fuel))
    | .atom name => .ok (.atom name, fuel)
    | .tag label payload =>
        evaluate fuel rho payload >>= fun result =>
          .ok (.tag label result.1, result.2)
    | .«section» entries =>
        canonicalEntries entries >>= fun (_sorted : List (String × Term)) =>
          evaluateEntries fuel rho entries >>= fun result =>
            .ok (.«section» (sortEntries result.1), result.2)
    | .«case» scrutinee _ branches =>
        evaluate fuel rho scrutinee >>= fun result =>
          match result.1 with
          | .tag label payload => evaluateBranch result.2 rho label payload branches
          | .atom .. => .error .expectedLan
          | .«section» .. => .error .expectedLan
    | .project field _ label =>
        evaluate fuel rho field >>= fun result =>
          match result.1 with
          | .«section» entries =>
              lookup label entries >>= fun value => .ok (value, result.2)
          | .atom .. => .error .expectedRan
          | .tag .. => .error .expectedRan

/-- `evaluateEntries` mirrors the OCaml `evaluate_entries` at lib/finite_term.ml lines 261 to 266.
It walks one field list, it threads the single budget of decision S2-D4 and it keeps each label.
`evaluateEntries` is the list partner of `evaluate` for the nested inductive of decision S2-D1.
-/
def evaluateEntries (fuel : Nat) (rho : List Value) (entries : List (String × Term)) :
    Res (List (String × Value) × Nat) :=
  match entries with
  | [] => .ok ([], fuel)
  | (label, field) :: rest =>
      evaluate fuel rho field >>= fun result =>
        evaluateEntries result.2 rho rest >>= fun tail =>
          .ok ((label, result.1) :: tail.1, tail.2)

/-- `evaluateBranch` replaces the OCaml branch lookup at lib/finite_term.ml lines 252 and 253.
Decision S2-D5 makes it walk the syntactic branch list of one `case` node, since the body that
`lookup` returns is no subterm of that node.
It takes the first label match, as `List.assoc_opt` at line 41 does, and an empty list reports
`Err.unexpectedLabel`, which mirrors `lookup` at lines 40 and 41.
It never ticks and it needs no gas, so the charge count stays the OCaml one.
The body runs at the environment that the payload value extends, as line 253 states.
-/
def evaluateBranch (fuel : Nat) (rho : List Value) (label : String) (payload : Value)
    (branches : List (String × Term)) : Res (Value × Nat) :=
  match branches with
  | [] => .error (.unexpectedLabel label)
  | (key, body) :: rest =>
      if key == label then evaluate fuel (payload :: rho) body
      else evaluateBranch fuel rho label payload rest
end

/-- `run` mirrors the OCaml `run` at lib/finite_term.ml lines 268 to 270.
It checks the term at the empty context, then it evaluates at the empty environment.
Decision S2-D4 gives one budget to both steps and it adds no charge point here.
The gas of `checkCore` is `2 * fuel + 2`, per decision S2-D5.
The remaining budget of the evaluation drops, as line 270 shows.
-/
def run (fuel : Nat) (t : Term) (a : Ty) : Res Value :=
  checkCore (2 * fuel + 2) fuel [] t a >>= fun fuel =>
    evaluate fuel [] t >>= fun result => .ok result.1

mutual
/-- `quote` maps one value back to a term, as docs/metatheory.md lines 383 to 386 states.
The OCaml module holds no counterpart, and Theorem6-11.5 relates a normal form to a value here.
The nested list of decision S2-D1 needs the list partner `quoteEntries` for the section arm.
-/
def quote : Value → Term
  | .atom name => .atom name
  | .tag label payload => .tag label (quote payload)
  | .«section» fields => .«section» (quoteEntries fields)

/-- `quoteEntries` maps one field list of values to one field list of terms.
`quoteEntries` is the list partner of `quote` for the `map` of docs/metatheory.md line 385.
-/
def quoteEntries : List (String × Value) → List (String × Term)
  | [] => []
  | (label, value) :: rest => (label, quote value) :: quoteEntries rest
end
