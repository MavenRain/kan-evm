import KanEvmProofs.Syntax
import KanEvmProofs.Check
import KanEvmProofs.Eval

/-! # Typing of the finite fragment

This module holds the three inductive relations of decision S2-D7.
`HasType` states the checking rules of docs/metatheory.md lines 40 to 51.
`ValueHasType` states the value rules of docs/metatheory.md lines 67 to 70.
`EnvHasType` states the environment rule of docs/metatheory.md lines 75 to 77.
No relation here carries fuel, as docs/metatheory.md line 38 states.
Theorem4 needs the last two relations, and Theorem4-C3 needs the value rules to stay exhaustive.
This module holds no theorem and no example, per the wave 5 assignment of S2-S0.
-/

mutual
/-- `HasType` mirrors the checking rules of docs/metatheory.md lines 40 to 51.
Each rule mirrors one arm of `check_term` at lib/finite_term.ml lines 62 to 105.
The relation carries no fuel, per decision S2-D7 and docs/metatheory.md line 38.
No rule carries a `Ty.Canonical` side condition. Decision S2-D7 asked for one on every type a rule reads, and the stage review of 2026-09-06 found that such a side condition refutes
Theorem1 of the stage brief: `checkCore` at lib/finite_term.ml lines 62 to 105 sends no annotation through
`canonical` and tests no context entry for canonicity, so a successful `check` states no canonicity fact, while
Theorem1 states `check fuel g t a = ok ()` implies `HasType g t a` with no canonicity hypothesis.
Each rule here therefore states exactly what the checker tests.
Canonicity stays a hypothesis of each theorem that needs it, as the Theorem4 row of the stage brief already writes it, and
Lemma0 relates the structural comparison of lines 67 and 100 to equality on canonical types where a proof needs that step.
-/
inductive HasType : List Ty → Term → Ty → Prop where
  /-- The var rule states VAR of docs/metatheory.md line 40 and mirrors lib/finite_term.ml lines 65 to 67.
  `variable` of Check.lean reads the context and reports a miss as an error, so a successful read states both parts of the
  OCaml guard at lines 43 to 45.
  -/
  | var (ctx : List Ty) (index : Nat) (a : Ty) :
      «variable» index ctx = .ok a → HasType ctx (.var index) a
  /-- The atom rule states ATOM of docs/metatheory.md line 41 and mirrors lib/finite_term.ml lines 68 to 72.
  The rule reads a label list and no fiber list, so it needs no side condition.
  -/
  | atom (ctx : List Ty) (name : String) (labels : List String) :
      labels.contains name = true → HasType ctx (.atom name) (.atoms labels)
  /-- The tag rule states TAG of docs/metatheory.md lines 42 and 43 and mirrors lib/finite_term.ml lines 73 to 77.
  `lookup` of Check.lean finds the fiber of the label, as lib/finite_term.ml lines 40 and 41 do.
  -/
  | tag (ctx : List Ty) (label : String) (payload : Term)
      (fibers : List (String × Ty)) (fiber : Ty) :
      lookup label fibers = .ok fiber →
      HasType ctx payload fiber → HasType ctx (.tag label payload) (.lan fibers)
  /-- The section rule states SECTION of docs/metatheory.md lines 44 to 46 and mirrors lib/finite_term.ml lines 78 to 85.
  The two premises `canonicalEntries` and `align` state the key alignment of docs/metatheory.md lines 53 to 59, which asks for no repeated label and for one sorted label sequence that equals the fiber label sequence element for element.
  -/
  | «section» (ctx : List Ty) (entries : List (String × Term)) (fibers : List (String × Ty))
      (sorted : List (String × Term)) (pairs : List (String × Ty × Term)) :
      canonicalEntries entries = .ok sorted →
      align fibers sorted = .ok pairs → HasTypeEntries ctx pairs .none →
      HasType ctx (.«section» entries) (.ran fibers)
  /-- The case rule states CASE of docs/metatheory.md lines 47 to 49 and mirrors lib/finite_term.ml lines 86 to 95.
  The scrutinee type is the type the rule reads, and the two premises `canonicalEntries` and `align` state that its fiber labels hold the ascending order of the canonicalized branch list.
  The branch premise extends the context with the fiber type of the label, as lib/finite_term.ml lines 92 and 93 do, and it holds for every branch, including a branch that no evaluation selects, as docs/metatheory.md lines 59 and 60 state.
  -/
  | «case» (ctx : List Ty) (scrutinee : Term) (fibers : List (String × Ty))
      (branches : List (String × Term)) (sorted : List (String × Term))
      (pairs : List (String × Ty × Term)) (expected : Ty) :
      canonicalEntries branches = .ok sorted →
      align fibers sorted = .ok pairs → HasType ctx scrutinee (.lan fibers) →
      HasTypeEntries ctx pairs (.some expected) →
      HasType ctx (.«case» scrutinee (.lan fibers) branches) expected
  /-- The project rule states PROJECT of docs/metatheory.md lines 50 and 51 and mirrors lib/finite_term.ml lines 96 to 102.
  The section type is the type the rule reads, and `lookup` gives the result type at the label, as the OCaml arm at line 100 does.
  -/
  | project (ctx : List Ty) (sectionTerm : Term) (fibers : List (String × Ty))
      (label : String) (a : Ty) :
      lookup label fibers = .ok a →
      HasType ctx sectionTerm (.ran fibers) →
      HasType ctx (.project sectionTerm (.ran fibers) label) a

/-- `HasTypeEntries` is the entry list companion of `HasType`, per decision S2-D7.
It covers the field list of the section rule and the branch list of the case rule, which are the two lists that
`check_many` of lib/finite_term.ml lines 103 to 105 walks. The entry list is the aligned triple list that
`align` returns, so each entry holds one label, one fiber type and one term.
The third argument names the mode. `Option.none` is the field mode, and each field runs at the fiber type of its own label and at the unchanged context, as lib/finite_term.ml line 84 does.
`Option.some a` is the branch mode, and each body runs at the type `a` and at the context that the fiber type extends, as lib/finite_term.ml lines 92 and 93 do.
One relation covers both lists, so the mode replaces a second companion relation.
`checkFields` and `checkBranches` of Check.lean are the two functions that mirror these modes.
-/
inductive HasTypeEntries : List Ty → List (String × Ty × Term) → Option Ty → Prop where
  /-- The empty entry list holds in each mode, as lib/finite_term.ml line 104 states. -/
  | nil (ctx : List Ty) (mode : Option Ty) : HasTypeEntries ctx [] mode
  /-- One field runs at the fiber type of its own label and at the unchanged context. -/
  | field (ctx : List Ty) (label : String) (fiber : Ty) (fieldTerm : Term)
      (rest : List (String × Ty × Term)) :
      HasType ctx fieldTerm fiber → HasTypeEntries ctx rest .none →
      HasTypeEntries ctx ((label, fiber, fieldTerm) :: rest) .none
  /-- One branch body runs at the expected type and at the extended context. -/
  | branch (ctx : List Ty) (label : String) (payloadType : Ty) (body : Term)
      (rest : List (String × Ty × Term)) (expected : Ty) :
      HasType (payloadType :: ctx) body expected → HasTypeEntries ctx rest (.some expected) →
      HasTypeEntries ctx ((label, payloadType, body) :: rest) (.some expected)
end

mutual
/-- `ValueHasType` states the value rules V-ATOM, V-TAG and V-SECTION of docs/metatheory.md lines 67 to 70, per decision
S2-D7. `Value` of Eval.lean mirrors the OCaml type `value` at lib/finite_term.ml lines 231 to 234.
Value typing needs no context, since a value holds no variable, as docs/metatheory.md line 74 states, and the relation carries no fuel.
The three rules are exhaustive over the three value shapes and over the three type shapes, which Theorem4-C3 needs.
V-TAG is the one rule at a `lan` type and V-SECTION is the one rule at a `ran` type, as docs/metatheory.md lines 240 and 241 record.
-/
inductive ValueHasType : Value → Ty → Prop where
  /-- V-ATOM of docs/metatheory.md line 67 holds when the atom name is a label of the type.
  The evaluator returns this value at lib/finite_term.ml line 240, and the checker tests the same membership at lib/finite_term.ml line 70.
  -/
  | atom (name : String) (labels : List String) :
      labels.contains name = true → ValueHasType (.atom name) (.atoms labels)
  /-- V-TAG of docs/metatheory.md line 68 holds when the payload value has the fiber type of the label.
  The evaluator builds this value at lib/finite_term.ml lines 241 to 243, and `lookup` of Check.lean finds the fiber, as lib/finite_term.ml lines 40 and 41 do.
  -/
  | tag (label : String) (payload : Value) (fibers : List (String × Ty)) (fiber : Ty) :
      lookup label fibers = .ok fiber → ValueHasType payload fiber →
      ValueHasType (.tag label payload) (.lan fibers)
  /-- V-SECTION of docs/metatheory.md lines 69 and 70 holds when the field list and the fiber list carry one shared label sequence and each field value has the fiber type of its label.
  The evaluator builds a section value only from `canonical entries` at lib/finite_term.ml lines 244 to 247, so the field list holds the ascending label order that
  V-SECTION demands, as docs/metatheory.md lines 72 to 74 record.
  -/
  | «section» (fields : List (String × Value)) (fibers : List (String × Ty)) :
      ValueHasTypeEntries fields fibers → ValueHasType (.«section» fields) (.ran fibers)

/-- `ValueHasTypeEntries` is the field list companion of `ValueHasType`, per decision S2-D7.
It walks the field list and the fiber list together, so it states the two parts of `keys(e) = keys(F)` of docs/metatheory.md line 69.
The two lists have one length, and the label of each field equals the label of the fiber at the same position, element for element.
Each field value has the fiber type of its own label. The two lists hold the ascending label order of
`canonical` at lib/finite_term.ml lines 20 to 23, so one walk of both lists needs no sort and no search.
-/
inductive ValueHasTypeEntries : List (String × Value) → List (String × Ty) → Prop where
  /-- The empty field list matches the empty fiber list alone. -/
  | nil : ValueHasTypeEntries [] []
  /-- One field and one fiber share a label, and the field value has the fiber type. -/
  | cons (label : String) (value : Value) (fiber : Ty) (fields : List (String × Value))
      (fibers : List (String × Ty)) :
      ValueHasType value fiber → ValueHasTypeEntries fields fibers →
      ValueHasTypeEntries ((label, value) :: fields) ((label, fiber) :: fibers)
end

/-- `EnvHasType` states the environment rule of docs/metatheory.md lines 75 to 77.
Environment typing is pointwise. The walk of both lists gives the length equality `length rho = length G` and gives
`rho(i) : G(i)` at every index in range. `run` at lib/finite_term.ml lines 268 to 270 uses the empty environment against the empty context, which is the
`nil` rule here. `evaluate` at lib/finite_term.ml lines 250 to 253 extends the environment with one payload value at the same position at which the case rule of
`HasType` extends the context with one fiber type, so the `cons` rule pairs those two extensions.
The relation carries no fuel, per decision S2-D7, and Theorem4 needs it.
-/
inductive EnvHasType : List Value → List Ty → Prop where
  /-- The empty environment matches the empty context alone. -/
  | nil : EnvHasType [] []
  /-- One value and one type at the head, and the two tails match at every later index. -/
  | cons (value : Value) (a : Ty) (rho : List Value) (ctx : List Ty) :
      ValueHasType value a → EnvHasType rho ctx → EnvHasType (value :: rho) (a :: ctx)
