import KanEvmProofs.Syntax
import KanEvmProofs.Check
import KanEvmProofs.Eval
import KanEvmProofs.Typing
import KanEvmProofs.Canonical
import KanEvmProofs.Budget
import KanEvmProofs.Checker
import KanEvmProofs.Weakening

/-! # Preservation for evaluation

This module holds row Theorem4, row Theorem4-C3 and row Theorem4-C4 of the stage brief.
`evaluate_preserves_type` states docs/metatheory.md lines 217 to 236.
`run_never_expected_shape` states claim C3 of docs/metatheory.md lines 237 to 243.
`run_budget_two_size` states claim C4 of docs/metatheory.md lines 244 to 250.
`evaluate` of Eval.lean mirrors `evaluate` at lib/finite_term.ml lines 236 to 266, and `run` of Eval.lean mirrors
`run` at lib/finite_term.ml lines 268 to 270. The proofs recurse on the typing derivation of Typing.lean, as row
Lemma0 of the brief asks, and they reuse the cost lemmas of Budget.lean and the soundness lemmas of
Checker.lean.
-/

namespace Evaluation

/-- `boolCases` reads one `Bool` in the two ways it can stand.
The label comparison at lib/finite_term.ml lines 67 and 253 returns a
`Bool`, and every proof of this module reads that comparison through this case reader.
-/
theorem boolCases {C : Prop} (b : Bool) (hfalse : b = false → C) (htrue : b = true → C) : C :=
  Bool.rec (motive := fun z => b = z → C) hfalse htrue b rfl

/-- `boolNot` turns a `false` comparison into the negation of the matching proposition.
The `if` of lib/finite_term.ml line 253 tests such a proposition, so the miss arm needs it.
-/
theorem boolNot {b : Bool} (h : b = false) : ¬(b = true) :=
  fun ht => Bool.noConfusion (h.symm.trans ht)

/-- `beqSymm` swaps the two sides of a true string comparison.
`evaluate` at lib/finite_term.ml line 253 compares the branch key with the tag label, and
`lookup` at lib/finite_term.ml lines 47 and 48 compares the tag label with the branch key.
-/
theorem beqSymm (a b : String) (h : (a == b) = true) : (b == a) = true :=
  (congrArg (fun z : String => (b == z)) (eq_of_beq h)).trans (beq_self_eq_true b)

/-- `beqFalseSymm` swaps the two sides of a false string comparison.
It serves the miss arm of the branch walk at lib/finite_term.ml lines 252 to 256.
-/
theorem beqFalseSymm (a b : String) (h : (a == b) = false) : (b == a) = false :=
  boolCases (b == a) (fun hf => hf) (fun ht => Bool.noConfusion (h.symm.trans (beqSymm b a ht)))

/-- `lookupHit` reads the head arm of `lookup` at lib/finite_term.ml lines 47 and 48.
A head that carries the wanted label returns the payload of that head.
-/
theorem lookupHit {α : Type} (label key : String) (value : α) (rest : List (String × α))
    (h : (label == key) = true) : lookup label ((key, value) :: rest) = .ok value :=
  congrArg
    (fun z : Bool =>
      (cond z (some value) (List.lookup label rest)).elim
        (Except.error (Err.unexpectedLabel label)) Except.ok)
    h

/-- `lookupMiss` reads the tail arm of `lookup` at lib/finite_term.ml lines 47 and 48.
A head that carries another label leaves the walk to the rest of the entries.
-/
theorem lookupMiss {α : Type} (label key : String) (value : α) (rest : List (String × α))
    (h : (label == key) = false) :
    lookup label ((key, value) :: rest) = lookup label rest :=
  congrArg
    (fun z : Bool =>
      (cond z (some value) (List.lookup label rest)).elim
        (Except.error (Err.unexpectedLabel label)) Except.ok)
    h

/-- `lookupNil` reads the empty arm of `lookup` at lib/finite_term.ml lines 47 and 48.
An empty entry list reports the label as unexpected.
-/
theorem lookupNil {α : Type} (label : String) :
    lookup label ([] : List (String × α)) = .error (.unexpectedLabel label) := rfl

/-- `labelNe` states that a false order test separates two labels.
The sort of lib/finite_term.ml lines 21 and 26 orders the labels, and a false test at line 26 tells the inserted label apart from the head label.
-/
theorem labelNe (a b : String) (h : labelLe a b = false) (heq : a = b) : False :=
  Bool.noConfusion
    (h.symm.trans
      (((congrArg (fun z : String => labelLe z a) heq).symm.trans
        (congrArg (fun z : String => labelLe a z) heq)).symm.trans (Canon.labelLe_swap a b h)))

/-- `valueCast` moves a value typing along one value equation and one type equation.
The value judgement of docs/metatheory.md lines 67 to 70 names both sides of the judgement.
-/
theorem valueCast {v w : Value} {x y : Ty} (hv : v = w) (hy : x = y)
    (h : ValueHasType v x) : ValueHasType w y :=
  Eq.mp (congrArg (fun z : Ty => ValueHasType w z) hy)
    (Eq.mp (congrArg (fun z : Value => ValueHasType z x) hv) h)

/-- `valueLan` inverts the value judgement at a `lan` type.
Rule V-TAG of docs/metatheory.md line 69 is the one rule of the judgement that reaches `lan`.
-/
theorem valueLan : ∀ (v : Value) (a : Ty), ValueHasType v a →
    ∀ (fibers : List (String × Ty)), a = .lan fibers →
      ∃ (label : String) (payload : Value) (fiber : Ty),
        v = .tag label payload ∧ lookup label fibers = .ok fiber ∧ ValueHasType payload fiber
  | _, _, .atom _name _labels _hm, _fibers, heq => Ty.noConfusion heq
  | _, _, .«section» _fields _fibers _hf, _fs, heq => Ty.noConfusion heq
  | _, _, .tag label payload fibers fiber hlookup hpayload, _fs, heq =>
      ⟨label, payload, fiber, rfl,
        Eq.mp (congrArg (fun z : List (String × Ty) => lookup label z = .ok fiber)
          (Ty.lan.inj heq)) hlookup,
        hpayload⟩

/-- `valueRan` inverts the value judgement at a `ran` type.
Rule V-SECTION of docs/metatheory.md line 70 is the one rule of the judgement that reaches `ran`.
-/
theorem valueRan : ∀ (v : Value) (a : Ty), ValueHasType v a →
    ∀ (fibers : List (String × Ty)), a = .ran fibers →
      ∃ fields : List (String × Value), v = .«section» fields ∧ ValueHasTypeEntries fields fibers
  | _, _, .atom _name _labels _hm, _fibers, heq => Ty.noConfusion heq
  | _, _, .tag _label _payload _fibers _fiber _hl _hp, _fs, heq => Ty.noConfusion heq
  | _, _, .«section» fields fibers hf, _fs, heq =>
      ⟨fields, rfl,
        Eq.mp (congrArg (fun z : List (String × Ty) => ValueHasTypeEntries fields z)
          (Ty.ran.inj heq)) hf⟩

/-- `noneNeSome` states that an absent option and a present option differ.
The variable arm at lib/finite_term.ml lines 237 and 238 reads an option, and the miss arm of
`lookup` at lib/finite_term.ml lines 40 and 41 reads the same option shape.
-/
theorem noneNeSome {α : Type} {o : Option α} {value : α} (hn : o = none)
    (h : o = some value) : False :=
  cast
    (congrArg (fun z : Option α => match z with | none => True | some _v => False)
      (hn.symm.trans h))
    True.intro

/-- `emptyGetNone` states that an empty environment reads no value at any index.
The variable arm at lib/finite_term.ml lines 237 and 238 reads the environment at one index, and the empty environment matches the empty context of docs/metatheory.md lines 75 to 77.
-/
theorem emptyGetNone (index : Nat) (value : Value)
    (h : ([] : List Value)[index]? = some value) : False :=
  noneNeSome List.getElem?_nil h

/-- `envLookup` reads one value of an environment that matches a context.
Environment typing of docs/metatheory.md lines 75 to 77 pairs the two lists at every index, and the variable arm at lib/finite_term.ml lines 237 and 238 reads the environment at one index.
-/
theorem envLookup : ∀ (rho : List Value) (ctx : List Ty), EnvHasType rho ctx →
    ∀ (index : Nat) (value : Value) (a : Ty), rho[index]? = some value →
      «variable» index ctx = .ok a → ValueHasType value a
  | _, _, .nil, 0, _value, _a, hr, _hv => (emptyGetNone 0 _value hr).elim
  | _, _, .nil, k + 1, _value, _a, hr, _hv => (emptyGetNone (k + 1) _value hr).elim
  | _, _, .cons v0 a0 _rho0 ctx0 hva _htail, 0, _value, a, hr, hv =>
      valueCast (Option.some.inj hr) (Weakening.headEq a0 a ctx0 hv) hva
  | _, _, .cons _v0 a0 rho0 ctx0 _hva htail, k + 1, value, a, hr, hv =>
      envLookup rho0 ctx0 htail k value a hr (Weakening.variableStepBack a0 ctx0 k a hv)

/-- `valueEntriesLookup` reads one field of a section value at one label.
V-SECTION of docs/metatheory.md lines 69 and 70 pairs the field list with the fiber list, and the project arm at lib/finite_term.ml lines 257 to 259 reads one field at one label.
-/
theorem valueEntriesLookup : ∀ (fields : List (String × Value)) (fibers : List (String × Ty)),
    ValueHasTypeEntries fields fibers → ∀ (label : String) (value : Value) (fiber : Ty),
      lookup label fields = .ok value → lookup label fibers = .ok fiber →
        ValueHasType value fiber
  | _, _, .nil, label, _value, _fiber, hf, _hb =>
      (res_error_ne_ok ((lookupNil label).symm.trans hf)).elim
  | _, _, .cons l0 v0 fib0 fields0 fibers0 hv htail, label, value, fiber, hf, hb =>
      boolCases (label == l0)
        (fun hfalse =>
          valueEntriesLookup fields0 fibers0 htail label value fiber
            ((lookupMiss label l0 v0 fields0 hfalse).symm.trans hf)
            ((lookupMiss label l0 fib0 fibers0 hfalse).symm.trans hb))
        (fun htrue =>
          valueCast
            (Except.ok.inj ((lookupHit label l0 v0 fields0 htrue).symm.trans hf))
            (Except.ok.inj ((lookupHit label l0 fib0 fibers0 htrue).symm.trans hb)) hv)

/-- `Paired` states that a value list and a term list share the label sequence and that each value is one successful evaluation of the term of the same label.
The section arm at lib/finite_term.ml lines 244 to 247 evaluates the fields, and the sort of lines 20 to 23 moves both lists together, so a relation over the two lists carries the sort.
-/
inductive Paired (rho : List Value) : List (String × Value) → List (String × Term) → Prop where
  /-- The empty value list pairs with the empty term list alone. -/
  | nil : Paired rho [] []
  /-- One head value is one successful evaluation of the head term at the shared label. -/
  | cons (label : String) (value : Value) (tm : Term) (values : List (String × Value))
      (terms : List (String × Term)) (fuel rest : Nat) :
      evaluate fuel rho tm = .ok (value, rest) → Paired rho values terms →
      Paired rho ((label, value) :: values) ((label, tm) :: terms)

/-- `pairedInsert` keeps the pairing through one insertion into both lists.
`insertEntry` of Check.lean mirrors the sort step at lib/finite_term.ml line 26, and the two insertions test the same label, so they take the same arm.
-/
theorem pairedInsert (rho : List Value) (label : String) (value : Value) (tm : Term)
    (fuel rest : Nat) (hev : evaluate fuel rho tm = .ok (value, rest)) :
    ∀ (values : List (String × Value)) (terms : List (String × Term)), Paired rho values terms →
      Paired rho (insertEntry (label, value) values) (insertEntry (label, tm) terms)
  | _, _, .nil => .cons label value tm [] [] fuel rest hev .nil
  | _, _, .cons l0 v0 t0 vs ts f0 r0 hev0 htail =>
      ite_case (c := labelLe label l0 = true)
        (P := fun (x : List (String × Value)) (y : List (String × Term)) => Paired rho x y)
        (fun _hc =>
          .cons label value tm ((l0, v0) :: vs) ((l0, t0) :: ts) fuel rest hev
            (.cons l0 v0 t0 vs ts f0 r0 hev0 htail))
        (fun _hn =>
          .cons l0 v0 t0 (insertEntry (label, value) vs) (insertEntry (label, tm) ts) f0 r0 hev0
            (pairedInsert rho label value tm fuel rest hev vs ts htail))

/-- `pairedSort` keeps the pairing through the sort of both lists.
`sortEntries` of Check.lean mirrors `List.sort` at lib/finite_term.ml line 21, and the section arm at lines 244 to 247 sorts the field terms while this module sorts the field values.
-/
theorem pairedSort (rho : List Value) :
    ∀ (values : List (String × Value)) (terms : List (String × Term)), Paired rho values terms →
      Paired rho (sortEntries values) (sortEntries terms)
  | _, _, .nil => .nil
  | _, _, .cons l0 v0 t0 vs ts f0 r0 hev0 htail =>
      pairedInsert rho l0 v0 t0 f0 r0 hev0 (sortEntries vs) (sortEntries ts)
        (pairedSort rho vs ts htail)

/-- `evalEntriesPaired` reads one successful field walk as a pairing.
`evaluateEntries` of Eval.lean mirrors `evaluate_entries` at lib/finite_term.ml lines 261 to 266, and it keeps the label of each field, so the two lists share the label sequence.
-/
theorem evalEntriesPaired : ∀ (entries : List (String × Term)) (fuel : Nat) (rho : List Value)
    (values : List (String × Value)) (rest : Nat),
    evaluateEntries fuel rho entries = .ok (values, rest) → Paired rho values entries
  | [], _fuel, rho, _values, _rest, h =>
      Eq.mp
        (congrArg (fun z : List (String × Value) => Paired rho z [])
          (congrArg Prod.fst (Except.ok.inj h))) .nil
  | (label, field) :: more, fuel, rho, _values, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              Eq.mp
                (congrArg
                  (fun z : List (String × Value) => Paired rho z ((label, field) :: more))
                  (congrArg Prod.fst (Except.ok.inj h3)))
                (.cons label head.1 field tail.1 more fuel head.2 hhead
                  (evalEntriesPaired more head.2 rho tail.1 tail.2 htail))


/-- `TermProp` states preservation for one term at one context and one type.
It is the statement of docs/metatheory.md lines 217 to 236 at one node, and it quantifies the environment and the budget, as the induction of lines 232 to 234 asks.
-/
def TermProp (ctx : List Ty) (t : Term) (a : Ty) : Prop :=
  ∀ (rho : List Value) (fuel : Nat) (value : Value) (rest : Nat),
    EnvHasType rho ctx → evaluate fuel rho t = .ok (value, rest) → ValueHasType value a

/-- `PairsProp` states preservation for one aligned entry list in one mode.
The field mode runs each term at the fiber of its own label, as lib/finite_term.ml line 84 does, and the branch mode runs each body at the extended context, as lines 92 and 93 do.
-/
def PairsProp (ctx : List Ty) : List (String × Ty × Term) → Option Ty → Prop
  | [], .none => True
  | [], .some _expected => True
  | (_label, fiber, tm) :: rest, .none => TermProp ctx tm fiber ∧ PairsProp ctx rest .none
  | (_label, fiber, tm) :: rest, .some expected =>
      TermProp (fiber :: ctx) tm expected ∧ PairsProp ctx rest (.some expected)

/-- `termCast` moves one preservation statement along one type equation and one term equation.
The aligned triple of lib/finite_term.ml lines 51 to 60 names both the fiber and the term.
-/
theorem termCast {ctx : List Ty} {fib fiber : Ty} {tm body : Term} {expected : Ty}
    (hf : fib = fiber) (ht : tm = body) (h : TermProp (fib :: ctx) tm expected) :
    TermProp (fiber :: ctx) body expected :=
  Eq.mp (congrArg (fun z : Term => TermProp (fiber :: ctx) z expected) ht)
    (Eq.mp (congrArg (fun z : Ty => TermProp (z :: ctx) tm expected) hf) h)

/-- `lookupInsertHit` reads the inserted entry back out of one sorted insertion.
`insertEntry` of Check.lean mirrors the sort step at lib/finite_term.ml line 26, and
`lookup` at lines 40 and 41 finds the first entry of the label.
-/
theorem lookupInsertHit {α : Type} (label : String) (entry : String × α)
    (h : (label == entry.1) = true) :
    ∀ entries : List (String × α), lookup label (insertEntry entry entries) = .ok entry.2
  | [] => lookupHit label entry.1 entry.2 [] h
  | (k0, v0) :: rest =>
      ite_elim (c := labelLe entry.1 k0 = true)
        (P := fun z : List (String × α) => lookup label z = .ok entry.2)
        (fun _hc => lookupHit label entry.1 entry.2 ((k0, v0) :: rest) h)
        (fun hn =>
          boolCases (label == k0)
            (fun hfalse =>
              (lookupMiss label k0 v0 (insertEntry entry rest) hfalse).trans
                (lookupInsertHit label entry h rest))
            (fun htrue =>
              (labelNe entry.1 k0 (Eq.mp (Bool.not_eq_true (labelLe entry.1 k0)) hn)
                ((eq_of_beq h).symm.trans (eq_of_beq htrue))).elim))

/-- `lookupInsertMiss` states that one sorted insertion changes no other label.
`insertEntry` of Check.lean mirrors the sort step at lib/finite_term.ml line 26.
-/
theorem lookupInsertMiss {α : Type} (label : String) (entry : String × α)
    (h : (label == entry.1) = false) :
    ∀ entries : List (String × α),
      lookup label (insertEntry entry entries) = lookup label entries
  | [] => lookupMiss label entry.1 entry.2 [] h
  | (k0, v0) :: rest =>
      ite_elim (c := labelLe entry.1 k0 = true)
        (P := fun z : List (String × α) => lookup label z = lookup label ((k0, v0) :: rest))
        (fun _hc => lookupMiss label entry.1 entry.2 ((k0, v0) :: rest) h)
        (fun _hn =>
          boolCases (label == k0)
            (fun hfalse =>
              ((lookupMiss label k0 v0 (insertEntry entry rest) hfalse).trans
                  (lookupInsertMiss label entry h rest)).trans
                (lookupMiss label k0 v0 rest hfalse).symm)
            (fun htrue =>
              (lookupHit label k0 v0 (insertEntry entry rest) htrue).trans
                (lookupHit label k0 v0 rest htrue).symm))

/-- `lookupSort` states that the sort keeps the result of every label read.
`sortEntries` of Check.lean mirrors `List.sort` at lib/finite_term.ml line 21, and the checker reads the sorted list at line 100 while the evaluator reads the source list at line 258.
-/
theorem lookupSort {α : Type} (label : String) :
    ∀ entries : List (String × α), lookup label (sortEntries entries) = lookup label entries
  | [] => rfl
  | (k0, v0) :: rest =>
      boolCases (label == k0)
        (fun hfalse =>
          ((lookupInsertMiss label (k0, v0) hfalse (sortEntries rest)).trans
              (lookupSort label rest)).trans (lookupMiss label k0 v0 rest hfalse).symm)
        (fun htrue =>
          (lookupInsertHit label (k0, v0) htrue (sortEntries rest)).trans
            (lookupHit label k0 v0 rest htrue).symm)

/-- `branchSelect` reads one successful branch walk as one label read and one body evaluation.
`evaluateBranch` of Eval.lean replaces the branch lookup at lib/finite_term.ml lines 252 and 253, and it takes the first branch of the label, as
`lookup` at lines 40 and 41 does.
-/
theorem branchSelect : ∀ (branches : List (String × Term)) (fuel : Nat) (rho : List Value)
    (label : String) (payload : Value) (value : Value) (rest : Nat),
    evaluateBranch fuel rho label payload branches = .ok (value, rest) →
      ∃ body : Term, lookup label branches = .ok body ∧
        evaluate fuel (payload :: rho) body = .ok (value, rest)
  | [], _fuel, _rho, _label, _payload, _value, _rest, h => (res_error_ne_ok h).elim
  | (key, body) :: more, fuel, rho, label, payload, value, rest, h =>
      boolCases (key == label)
        (fun hfalse =>
          match branchSelect more fuel rho label payload value rest
              ((Checker.ite_miss (boolNot hfalse)).symm.trans h) with
          | ⟨b, hlk, hev⟩ =>
              ⟨b, (lookupMiss label key body more (beqFalseSymm key label hfalse)).trans hlk, hev⟩)
        (fun htrue =>
          ⟨body, lookupHit label key body more (beqSymm key label htrue),
            (Checker.ite_hit htrue).symm.trans h⟩)


/-- `alignCons` inverts one successful alignment at one head of both lists.
`align` at lib/finite_term.ml lines 51 to 60 pairs the two heads when the labels are equal, and it reports an error at the two other orders.
-/
theorem alignCons (k l : String) (fib : Ty) (fs : List (String × Ty)) (tm : Term)
    (ts : List (String × Term)) (pairs : List (String × Ty × Term))
    (h : align ((k, fib) :: fs) ((l, tm) :: ts) = .ok pairs) :
    k = l ∧ ∃ tailPairs : List (String × Ty × Term),
      align fs ts = .ok tailPairs ∧ pairs = (k, fib, tm) :: tailPairs :=
  match hc : compare k l, (align_cons k fib fs l tm ts).symm.trans h with
  | .lt, hh => (res_error_ne_ok hh).elim
  | .gt, hh => (res_error_ne_ok hh).elim
  | .eq, hh =>
      match res_bind_ok hh with
      | ⟨tailPairs, htail, hmk⟩ =>
          ⟨Std.LawfulEqCmp.eq_of_compare hc, tailPairs, htail, (Except.ok.inj hmk).symm⟩

/-- `alignProp` reads the branch statement of one aligned list at one label.
The case rule of docs/metatheory.md lines 47 to 49 aligns the fiber list with the sorted branch list, and the evaluator selects the branch of the tag label at lib/finite_term.ml lines 252 and 253, so one label read gives the body and its statement.
-/
theorem alignProp (ctx : List Ty) (expected : Ty) :
    ∀ (fibers : List (String × Ty)) (terms : List (String × Term))
      (pairs : List (String × Ty × Term)),
      align fibers terms = .ok pairs → PairsProp ctx pairs (.some expected) →
        ∀ (label : String) (fiber : Ty) (body : Term),
          lookup label fibers = .ok fiber → lookup label terms = .ok body →
            TermProp (fiber :: ctx) body expected
  | [], [], _pairs, _ha, _hp, label, _fiber, _body, hlf, _hlt =>
      (res_error_ne_ok ((lookupNil label).symm.trans hlf)).elim
  | (_k, _fib) :: _fs, [], _pairs, ha, _hp, _label, _fiber, _body, _hlf, _hlt =>
      (res_error_ne_ok ha).elim
  | [], (_l, _tm) :: _ts, _pairs, ha, _hp, _label, _fiber, _body, _hlf, _hlt =>
      (res_error_ne_ok ha).elim
  | (k, fib) :: fs, (l, tm) :: ts, pairs, ha, hp, label, fiber, body, hlf, hlt =>
      match alignCons k l fib fs tm ts pairs ha with
      | ⟨hkl, tailPairs, htail, hpairs⟩ =>
          match Eq.mp
            (congrArg (fun z : List (String × Ty × Term) => PairsProp ctx z (.some expected))
              hpairs) hp with
          | ⟨h1, h2⟩ =>
              boolCases (label == k)
                (fun hfalse =>
                  alignProp ctx expected fs ts tailPairs htail h2 label fiber body
                    ((lookupMiss label k fib fs hfalse).symm.trans hlf)
                    ((lookupMiss label l tm ts
                      ((congrArg (fun z : String => (label == z)) hkl).symm.trans hfalse)).symm.trans
                        hlt))
                (fun htrue =>
                  termCast
                    (Except.ok.inj ((lookupHit label k fib fs htrue).symm.trans hlf))
                    (Except.ok.inj
                      ((lookupHit label l tm ts
                        ((congrArg (fun z : String => (label == z)) hkl).symm.trans
                          htrue)).symm.trans hlt))
                    h1)

/-- `consNeNil` states that a list with one head differs from the empty list.
The field walk at lib/finite_term.ml lines 261 to 266 and the alignment at lines 51 to 60 read the two list shapes apart.
-/
theorem consNeNil {α : Type} {x : α} {xs : List α} (h : x :: xs = []) : False :=
  cast (congrArg (fun z : List α => match z with | [] => False | _y :: _ys => True) h) True.intro

/-- `nilNeCons` states that the empty list differs from a list with one head.
It is the mirror of `consNeNil` for the other order of the same equation.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem nilNeCons {α : Type} {x : α} {xs : List α} (h : ([] : List α) = x :: xs) : False :=
  cast (congrArg (fun z : List α => match z with | [] => True | _y :: _ys => False) h) True.intro

/-- `pairedNil` reads one pairing at an empty term list. The section arm at lib/finite_term.ml lines 244 to 247 walks the field list, and an empty field list returns an empty value list at lines 261 and 262.
-/
theorem pairedNil (rho : List Value) : ∀ (values : List (String × Value))
    (terms : List (String × Term)), Paired rho values terms → terms = [] → values = []
  | _, _, .nil, _heq => rfl
  | _, _, .cons _lbl _value _tm _vs _ts _fuel _rest _hev _htail, heq => (consNeNil heq).elim

/-- `pairedCons` reads one pairing at one head of the term list.
The field walk at lib/finite_term.ml lines 261 to 266 keeps the label of the head and it evaluates the head term, so the value list holds the same label at the head.
-/
theorem pairedCons (rho : List Value) : ∀ (values : List (String × Value))
    (terms : List (String × Term)), Paired rho values terms →
    ∀ (l : String) (tm : Term) (ts : List (String × Term)), terms = (l, tm) :: ts →
      ∃ (value : Value) (vs : List (String × Value)) (fuel rest : Nat),
        values = (l, value) :: vs ∧ evaluate fuel rho tm = .ok (value, rest) ∧ Paired rho vs ts
  | _, _, .nil, _l, _tm, _ts, heq => (nilNeCons heq).elim
  | _, _, .cons _lbl value tm0 vs ts0 fuel rest hev htail, _l, _tm, _ts, heq =>
      match List.cons.inj heq with
      | ⟨hhead, htails⟩ =>
          match Prod.mk.inj hhead with
          | ⟨hl, ht⟩ =>
              ⟨value, vs, fuel, rest, congrArg (fun z : String => (z, value) :: vs) hl,
                Eq.mp (congrArg (fun z : Term => evaluate fuel rho z = .ok (value, rest)) ht) hev,
                Eq.mp (congrArg (fun z : List (String × Term) => Paired rho vs z) htails) htail⟩

/-- `sectionValues` reads one field walk of a section as a value typing of the field list.
The section rule of docs/metatheory.md lines 44 to 46 aligns the fiber list with the sorted field list, and
V-SECTION of lines 69 and 70 asks for the same label sequence and one typing of each field value.
-/
theorem sectionValues (ctx : List Ty) (rho : List Value) (henv : EnvHasType rho ctx) :
    ∀ (fibers : List (String × Ty)) (terms : List (String × Term))
      (pairs : List (String × Ty × Term)) (values : List (String × Value)),
      align fibers terms = .ok pairs → PairsProp ctx pairs .none → Paired rho values terms →
        ValueHasTypeEntries values fibers
  | [], [], _pairs, values, _ha, _hp, hpaired =>
      Eq.mp
        (congrArg (fun z : List (String × Value) => ValueHasTypeEntries z [])
          (pairedNil rho values [] hpaired rfl).symm) .nil
  | (_k, _fib) :: _fs, [], _pairs, _values, ha, _hp, _hpaired => (res_error_ne_ok ha).elim
  | [], (_l, _tm) :: _ts, _pairs, _values, ha, _hp, _hpaired => (res_error_ne_ok ha).elim
  | (k, fib) :: fs, (l, tm) :: ts, pairs, values, ha, hp, hpaired =>
      match alignCons k l fib fs tm ts pairs ha,
          pairedCons rho values ((l, tm) :: ts) hpaired l tm ts rfl with
      | ⟨hkl, tailPairs, htailAlign, hpairs⟩, ⟨value, vs, fuel, rest, hvalues, hev, htail⟩ =>
          match Eq.mp
            (congrArg (fun z : List (String × Ty × Term) => PairsProp ctx z .none) hpairs) hp with
          | ⟨h1, h2⟩ =>
              Eq.mp
                (congrArg
                  (fun z : List (String × Value) => ValueHasTypeEntries z ((k, fib) :: fs))
                  hvalues.symm)
                (Eq.mp
                  (congrArg
                    (fun z : String =>
                      ValueHasTypeEntries ((l, value) :: vs) ((z, fib) :: fs)) hkl.symm)
                  (.cons l value fib vs fs (h1 rho fuel value rest henv hev)
                    (sectionValues ctx rho henv fs ts tailPairs vs htailAlign h2 htail)))


/-- `optionElimSome` inverts one successful option read of decision S2-D3.
The variable arm at lib/finite_term.ml lines 237 and 238 and `lookup` at lines 40 and 41 read one option and they report the absent case as an error.
-/
theorem optionElimSome {α β : Type} {o : Option α} {e : Err} {cont : α → Res β} {v : β}
    (h : o.elim (.error e) cont = .ok v) : ∃ x : α, o = some x ∧ cont x = .ok v :=
  match o with
  | none => (res_error_ne_ok h).elim
  | some x => ⟨x, rfl, h⟩

/-- `pairsNil` states the empty entry list of both modes.
`check_many` at lib/finite_term.ml lines 103 to 105 accepts the empty list in each mode.
-/
theorem pairsNil (ctx : List Ty) (mode : Option Ty) : PairsProp ctx [] mode :=
  match mode with
  | .none => True.intro
  | .some _expected => True.intro

/-- `valueTagFiber` reads the fiber of one tag value at a `lan` type.
V-TAG of docs/metatheory.md line 68 gives the fiber of the label, and the case arm at lib/finite_term.ml lines 252 and 253 needs it for the payload of the selected branch.
-/
theorem valueTagFiber (label : String) (payload : Value) (fibers : List (String × Ty))
    (h : ValueHasType (.tag label payload) (.lan fibers)) :
    ∃ fiber : Ty, lookup label fibers = .ok fiber ∧ ValueHasType payload fiber :=
  match valueLan (.tag label payload) (.lan fibers) h fibers rfl with
  | ⟨_l2, _p2, fib, heq, hlk, hp⟩ =>
      match Value.tag.inj heq with
      | ⟨hl, hp2⟩ =>
          ⟨fib, Eq.mp (congrArg (fun z : String => lookup z fibers = .ok fib) hl.symm) hlk,
            Eq.mp (congrArg (fun z : Value => ValueHasType z fib) hp2.symm) hp⟩

/-- `valueSectionFields` reads the field typing of one section value at a `ran` type.
V-SECTION of docs/metatheory.md lines 69 and 70 pairs the field list with the fiber list, and the project arm at lib/finite_term.ml lines 257 to 259 reads one field of that list.
-/
theorem valueSectionFields (fields : List (String × Value)) (fibers : List (String × Ty))
    (h : ValueHasType (.«section» fields) (.ran fibers)) : ValueHasTypeEntries fields fibers :=
  match valueRan (.«section» fields) (.ran fibers) h fibers rfl with
  | ⟨_fs2, heq, hf⟩ =>
      Eq.mp
        (congrArg (fun z : List (String × Value) => ValueHasTypeEntries z fibers)
          (Value.«section».inj heq).symm) hf


mutual
/-- `evalPure` states preservation at every node of one typing derivation, per row Theorem4.
It states docs/metatheory.md lines 217 to 236, and the recursion runs on the derivation of
`HasType`, as line 232 asks, with the environment and the budget quantified.
`evaluate` at lib/finite_term.ml lines 236 to 260 reads the same node shapes.
-/
theorem evalPure : ∀ (g : List Ty) (t : Term) (a : Ty), HasType g t a → TermProp g t a
  | _, _, _, .var g index a hvar =>
      fun rho _fuel value _rest henv hev =>
        match res_bind_ok hev with
        | ⟨_f, _htick, h2⟩ =>
            match optionElimSome h2 with
            | ⟨_w, hsome, hk⟩ =>
                envLookup rho g henv index value a
                  (Eq.mp
                    (congrArg (fun z : Value => rho[index]? = some z)
                      (congrArg Prod.fst (Except.ok.inj hk))) hsome)
                  hvar
  | _, _, _, .atom _g name labels hmem =>
      fun _rho _fuel _value _rest _henv hev =>
        match res_bind_ok hev with
        | ⟨_f, _htick, h2⟩ =>
            Eq.mp
              (congrArg (fun z : Value => ValueHasType z (.atoms labels))
                (congrArg Prod.fst (Except.ok.inj h2))) (.atom name labels hmem)
  | _, _, _, .tag g label payload fibers fiber hlookup hpayload =>
      fun rho _fuel _value _rest henv hev =>
        match res_bind_ok hev with
        | ⟨f, _htick, h2⟩ =>
            match res_bind_ok h2 with
            | ⟨r, hr, h3⟩ =>
                Eq.mp
                  (congrArg (fun z : Value => ValueHasType z (.lan fibers))
                    (congrArg Prod.fst (Except.ok.inj h3)))
                  (.tag label r.1 fibers fiber hlookup
                    (evalPure g payload fiber hpayload rho f r.1 r.2 henv hr))
  | _, _, _, .«section» g entries fibers sorted pairs hcanon halign hentries =>
      fun rho _fuel _value _rest henv hev =>
        match res_bind_ok hev with
        | ⟨f, _htick, h2⟩ =>
            match res_bind_ok h2 with
            | ⟨_s, _hs, h3⟩ =>
                match res_bind_ok h3 with
                | ⟨r, hr, h4⟩ =>
                    Eq.mp
                      (congrArg (fun z : Value => ValueHasType z (.ran fibers))
                        (congrArg Prod.fst (Except.ok.inj h4)))
                      (.«section» (sortEntries r.1) fibers
                        (sectionValues g rho henv fibers sorted pairs (sortEntries r.1) halign
                          (evalPureEntries g pairs .none hentries)
                          (Eq.mp
                            (congrArg
                              (fun z : List (String × Term) => Paired rho (sortEntries r.1) z)
                              (canonical_sorted entries sorted hcanon).symm)
                            (pairedSort rho r.1 entries
                              (evalEntriesPaired entries f rho r.1 r.2 hr)))))
  | _, _, _, .«case» g scrutinee fibers branches sorted pairs expected hcanon halign hscr
      hbranch =>
      fun rho _fuel value rest henv hev =>
        match res_bind_ok hev with
        | ⟨f, _htick, h2⟩ =>
            match res_bind_ok h2 with
            | ⟨r, hr, h3⟩ =>
                match r.1, h3, evalPure g scrutinee (.lan fibers) hscr rho f r.1 r.2 henv hr with
                | .atom _name, hh, _hv => (res_error_ne_ok hh).elim
                | .«section» _fields, hh, _hv => (res_error_ne_ok hh).elim
                | .tag l p, hh, hv =>
                    match valueTagFiber l p fibers hv with
                    | ⟨fib, hlkFib, hpayload⟩ =>
                        match branchSelect branches r.2 rho l p value rest hh with
                        | ⟨body, hlkBody, hev2⟩ =>
                            alignProp g expected fibers sorted pairs halign
                              (evalPureEntries g pairs (.some expected) hbranch) l fib body hlkFib
                              (((congrArg (fun z : List (String × Term) => lookup l z)
                                    (canonical_sorted branches sorted hcanon)).trans
                                  (lookupSort l branches)).trans hlkBody)
                              (p :: rho) r.2 value rest (.cons p fib rho g hpayload henv) hev2
  | _, _, _, .project g sectionTerm fibers label a hlookup hsec =>
      fun rho _fuel _value _rest henv hev =>
        match res_bind_ok hev with
        | ⟨f, _htick, h2⟩ =>
            match res_bind_ok h2 with
            | ⟨r, hr, h3⟩ =>
                match r.1, h3,
                    evalPure g sectionTerm (.ran fibers) hsec rho f r.1 r.2 henv hr with
                | .atom _name, hh, _hv => (res_error_ne_ok hh).elim
                | .tag _l _p, hh, _hv => (res_error_ne_ok hh).elim
                | .«section» fields, hh, hv =>
                    match res_bind_ok hh with
                    | ⟨w, hw, h4⟩ =>
                        Eq.mp
                          (congrArg (fun z : Value => ValueHasType z a)
                            (congrArg Prod.fst (Except.ok.inj h4)))
                          (valueEntriesLookup fields fibers
                            (valueSectionFields fields fibers hv) label w a hw hlookup)

/-- `evalPureEntries` states preservation for one aligned entry list of either mode.
It is the list partner of `evalPure` for the field list of lib/finite_term.ml line 84 and for the branch list of lines 92 and 93, which decision
S2-D7 holds in one relation.
-/
theorem evalPureEntries : ∀ (g : List Ty) (pairs : List (String × Ty × Term))
    (mode : Option Ty), HasTypeEntries g pairs mode → PairsProp g pairs mode
  | _, _, _, .nil g mode => pairsNil g mode
  | _, _, _, .field g _label fiber fieldTerm rest hterm hrest =>
      ⟨evalPure g fieldTerm fiber hterm, evalPureEntries g rest .none hrest⟩
  | _, _, _, .branch g _label payloadType body rest expected hbody hrest =>
      ⟨evalPure (payloadType :: g) body expected hbody,
        evalPureEntries g rest (.some expected) hrest⟩
end

end Evaluation

open Evaluation in
/-- `evaluate_preserves_type` states row Theorem4 of the stage brief.
It states docs/metatheory.md lines 217 to 236, and `evaluate` at lib/finite_term.ml lines 236 to 260 returns one value and the remaining budget of a successful run.
The canonical hypothesis of the row rides the statement, and Checker.lean holds the step from the structural comparison to equality that a canonical type needs.
-/
theorem evaluate_preserves_type (g : List Ty) (t : Term) (a : Ty) (rho : List Value) (f : Nat)
    (v : Value) (rest : Nat) (d : HasType g t a) (_hcanonical : Ty.Canonical a)
    (henv : EnvHasType rho g) (hev : evaluate f rho t = .ok (v, rest)) : ValueHasType v a :=
  evalPure g t a d rho f v rest henv hev

namespace Evaluation

/-- `Shapeless` names the errors that report no shape mismatch.
`Err` of Syntax.lean mirrors the OCaml error type, and claim C3 of docs/metatheory.md lines 237 to 243 asks for the absence of the two shape errors of lib/finite_term.ml lines 254 and 260.
-/
def Shapeless : Err → Prop
  | .duplicateLabel _label => True
  | .missingLabel _label => True
  | .unexpectedLabel _label => True
  | .invalidVariable _index => True
  | .invalidAtom _name => True
  | .typeMismatch => True
  | .expectedLan => False
  | .expectedRan => False
  | .resourceExhausted => True

/-- `errShapeless` moves one shapeless error along one equation of results.
The error monad of decision S2-D3 carries the error value through each bind.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem errShapeless {α : Type} {e x : Err} (h : (Except.error e : Res α) = .error x)
    (hs : Shapeless e) : Shapeless x :=
  Eq.mp (congrArg Shapeless (Except.error.inj h)) hs

/-- `res_bind_error` inverts one failed bind of the error monad of decision S2-D3.
The failure comes from the head or from the continuation, as lib/finite_term.ml lines 62 to 105 and lines 236 to 266 chain them.
-/
theorem res_bind_error {α β : Type} {e : Res α} {cont : α → Res β} {x : Err}
    (h : e >>= cont = .error x) :
    e = .error x ∨ ∃ a : α, e = .ok a ∧ cont a = .error x :=
  match e with
  | .error _y => .inl (congrArg (fun z : Err => (Except.error z : Res α)) (Except.error.inj h))
  | .ok a => .inr ⟨a, rfl, h⟩

/-- `tickShapeless` states that the one charge point reports no shape error.
`tick` of Check.lean is the charge point of decision S2-D4 and it reports the exhausted budget.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem tickShapeless : ∀ (fuel : Nat) (x : Err), tick fuel = .error x → Shapeless x
  | 0, _x, h => errShapeless h True.intro
  | _k + 1, _x, h => (res_error_ne_ok h.symm).elim

/-- `optionElimShapeless` states when one option read reports no shape error.
The variable arm at lib/finite_term.ml lines 237 and 238 and `lookup` at lines 40 and 41 report the absent case, and the continuation covers the present case.
-/
theorem optionElimShapeless {α β : Type} {o : Option α} {e x : Err} {cont : α → Res β}
    (h : Option.elim o (Except.error e : Res β) cont = Except.error x) (hs : Shapeless e)
    (hcont : ∀ (z : α) (y : Err), cont z = Except.error y → Shapeless y) : Shapeless x :=
  match o with
  | none => errShapeless h hs
  | some v => hcont v x h

/-- `lookupShapeless` states that one label read reports no shape error.
`lookup` at lib/finite_term.ml lines 40 and 41 reports the absent label alone.
-/
theorem lookupShapeless {α : Type} (label : String) (entries : List (String × α)) (x : Err)
    (h : lookup label entries = .error x) : Shapeless x :=
  optionElimShapeless h True.intro (fun _z _y hh => (res_error_ne_ok hh.symm).elim)

/-- `variableShapeless` states that one context read reports no shape error.
The variable arm at lib/finite_term.ml lines 43 to 45 reports the invalid index alone.
-/
theorem variableShapeless (index : Nat) (entries : List Ty) (x : Err)
    (h : «variable» index entries = .error x) : Shapeless x :=
  optionElimShapeless h True.intro (fun _z _y hh => (res_error_ne_ok hh.symm).elim)

/-- `IsTag` names the value shape that a `lan` type carries.
V-TAG of docs/metatheory.md line 68 is the one value rule at a `lan` type.
-/
def IsTag : Value → Prop
  | .tag _label _payload => True
  | .atom _name => False
  | .«section» _fields => False

/-- `IsSection` names the value shape that a `ran` type carries.
V-SECTION of docs/metatheory.md lines 69 and 70 is the one value rule at a `ran` type.
-/
def IsSection : Value → Prop
  | .«section» _fields => True
  | .atom _name => False
  | .tag _label _payload => False

/-- `valueLanTag` states that a value of a `lan` type is a tag value.
The case arm at lib/finite_term.ml line 254 reports `Expected_lan` at the two other shapes, and docs/metatheory.md lines 240 and 241 record that those shapes never reach a
`lan` type.
-/
theorem valueLanTag (v : Value) (fibers : List (String × Ty))
    (h : ValueHasType v (.lan fibers)) : IsTag v :=
  match valueLan v (.lan fibers) h fibers rfl with
  | ⟨_l, _p, _fib, heq, _hlk, _hp⟩ => Eq.mp (congrArg IsTag heq).symm True.intro

/-- `valueRanSection` states that a value of a `ran` type is a section value.
The project arm at lib/finite_term.ml line 260 reports `Expected_ran` at the two other shapes.
-/
theorem valueRanSection (v : Value) (fibers : List (String × Ty))
    (h : ValueHasType v (.ran fibers)) : IsSection v :=
  match valueRan v (.ran fibers) h fibers rfl with
  | ⟨_fields, heq, _hf⟩ => Eq.mp (congrArg IsSection heq).symm True.intro

/-- `SafeProp` states claim C3 for one term at one context. It states that no run of `evaluate` at lib/finite_term.ml lines 236 to 260 reports a shape error when the environment matches the context.
-/
def SafeProp (g : List Ty) (t : Term) : Prop :=
  ∀ (rho : List Value) (fuel : Nat) (x : Err), EnvHasType rho g →
    evaluate fuel rho t = .error x → Shapeless x

/-- `SafeEntries` states claim C3 for every term of one entry list.
The field walk at lib/finite_term.ml lines 261 to 266 evaluates each field of the list.
-/
def SafeEntries (g : List Ty) : List (String × Term) → Prop
  | [] => True
  | entry :: rest => SafeProp g entry.2 ∧ SafeEntries g rest

/-- `SafePairs` states claim C3 for one aligned entry list in one mode.
The two modes of decision S2-D7 run a field at the unchanged context and a branch body at the context that the fiber type extends.
It states claim C3 of docs/metatheory.md lines 237 to 243 for one aligned entry list.
The two modes mirror the field arm of lib/finite_term.ml line 84 and the branch arm of lines 92 and 93.
-/
def SafePairs (g : List Ty) : List (String × Ty × Term) → Option Ty → Prop
  | [], .none => True
  | [], .some _expected => True
  | entry :: rest, .none => SafeProp g entry.2.2 ∧ SafePairs g rest .none
  | entry :: rest, .some expected =>
      SafeProp (entry.2.1 :: g) entry.2.2 ∧ SafePairs g rest (.some expected)

/-- `safePairsNil` states the empty aligned list of both modes.
`check_many` at lib/finite_term.ml lines 103 to 105 accepts the empty list in each mode.
-/
theorem safePairsNil (g : List Ty) (mode : Option Ty) : SafePairs g [] mode :=
  match mode with
  | .none => True.intro
  | .some _expected => True.intro

/-- `safeCast` moves one shape statement along one type equation and one term equation.
The aligned triple of lib/finite_term.ml lines 51 to 60 names both the fiber and the term.
-/
theorem safeCast {g : List Ty} {fib fiber : Ty} {tm body : Term} (hf : fib = fiber)
    (ht : tm = body) (h : SafeProp (fib :: g) tm) : SafeProp (fiber :: g) body :=
  Eq.mp (congrArg (fun z : Term => SafeProp (fiber :: g) z) ht)
    (Eq.mp (congrArg (fun z : Ty => SafeProp (z :: g) tm) hf) h)

/-- `safeInsertInv` reads one shape statement of a sorted insertion back to its two parts.
`insertEntry` of Check.lean mirrors the sort step at lib/finite_term.ml line 21.
-/
theorem safeInsertInv (g : List Ty) (entry : String × Term) :
    ∀ entries : List (String × Term), SafeEntries g (insertEntry entry entries) →
      SafeProp g entry.2 ∧ SafeEntries g entries
  | [], h => match h with | ⟨h1, _h2⟩ => ⟨h1, True.intro⟩
  | head :: rest, h =>
      ite_elim (c := labelLe entry.1 head.1 = true) (a := entry :: head :: rest)
        (b := head :: insertEntry entry rest)
        (P := fun z : List (String × Term) =>
          SafeEntries g z → SafeProp g entry.2 ∧ SafeEntries g (head :: rest))
        (fun _hc hh => hh)
        (fun _hn hh =>
          match hh with
          | ⟨h1, h2⟩ =>
              match safeInsertInv g entry rest h2 with
              | ⟨h3, h4⟩ => ⟨h3, h1, h4⟩)
        h

/-- `safeSortInv` reads one shape statement of the sorted list back to the source list.
The section arm of the evaluator walks the source list at lib/finite_term.ml lines 261 to 266 while the section rule of docs/metatheory.md lines 44 to 46 reads the sorted list.
-/
theorem safeSortInv (g : List Ty) :
    ∀ entries : List (String × Term), SafeEntries g (sortEntries entries) → SafeEntries g entries
  | [], h => h
  | entry :: rest, h =>
      match safeInsertInv g entry (sortEntries rest) h with
      | ⟨h1, h2⟩ => ⟨h1, safeSortInv g rest h2⟩


/-- `alignSafeFields` spreads one shape statement of an aligned list over the field list.
`align` at lib/finite_term.ml lines 51 to 60 keeps the order of the field list, so each field term of the section rule of docs/metatheory.md lines 44 to 46 carries its own statement.
-/
theorem alignSafeFields (ctx : List Ty) :
    ∀ (fibers : List (String × Ty)) (terms : List (String × Term))
      (pairs : List (String × Ty × Term)),
      align fibers terms = .ok pairs → SafePairs ctx pairs .none → SafeEntries ctx terms
  | [], [], _pairs, _ha, _hp => True.intro
  | (_k, _fib) :: _fs, [], _pairs, ha, _hp => (res_error_ne_ok ha).elim
  | [], (_l, _tm) :: _ts, _pairs, ha, _hp => (res_error_ne_ok ha).elim
  | (k, fib) :: fs, (l, tm) :: ts, pairs, ha, hp =>
      match alignCons k l fib fs tm ts pairs ha with
      | ⟨_hkl, tailPairs, htail, hpairs⟩ =>
          match Eq.mp
            (congrArg (fun z : List (String × Ty × Term) => SafePairs ctx z .none) hpairs) hp with
          | ⟨h1, h2⟩ => ⟨h1, alignSafeFields ctx fs ts tailPairs htail h2⟩

/-- `alignSafeBranches` reads the shape statement of one branch body out of an aligned list.
The case rule of docs/metatheory.md lines 47 to 52 aligns the fiber list with the branch list, and the body of one label runs at the context that the fiber of that label extends.
-/
theorem alignSafeBranches (ctx : List Ty) (expected : Ty) :
    ∀ (fibers : List (String × Ty)) (terms : List (String × Term))
      (pairs : List (String × Ty × Term)),
      align fibers terms = .ok pairs → SafePairs ctx pairs (.some expected) →
        ∀ (label : String) (fiber : Ty) (body : Term),
          lookup label fibers = .ok fiber → lookup label terms = .ok body →
            SafeProp (fiber :: ctx) body
  | [], [], _pairs, _ha, _hp, label, _fiber, _body, hlf, _hlt =>
      (res_error_ne_ok ((lookupNil label).symm.trans hlf)).elim
  | (_k, _fib) :: _fs, [], _pairs, ha, _hp, _label, _fiber, _body, _hlf, _hlt =>
      (res_error_ne_ok ha).elim
  | [], (_l, _tm) :: _ts, _pairs, ha, _hp, _label, _fiber, _body, _hlf, _hlt =>
      (res_error_ne_ok ha).elim
  | (k, fib) :: fs, (l, tm) :: ts, pairs, ha, hp, label, fiber, body, hlf, hlt =>
      match alignCons k l fib fs tm ts pairs ha with
      | ⟨hkl, tailPairs, htail, hpairs⟩ =>
          match Eq.mp
            (congrArg (fun z : List (String × Ty × Term) => SafePairs ctx z (.some expected))
              hpairs) hp with
          | ⟨h1, h2⟩ =>
              boolCases (label == k)
                (fun hfalse =>
                  alignSafeBranches ctx expected fs ts tailPairs htail h2 label fiber body
                    ((lookupMiss label k fib fs hfalse).symm.trans hlf)
                    ((lookupMiss label l tm ts
                      ((congrArg (fun z : String => (label == z)) hkl).symm.trans
                        hfalse)).symm.trans hlt))
                (fun htrue =>
                  safeCast (Except.ok.inj ((lookupHit label k fib fs htrue).symm.trans hlf))
                    (Except.ok.inj
                      ((lookupHit label l tm ts
                        ((congrArg (fun z : String => (label == z)) hkl).symm.trans
                          htrue)).symm.trans hlt))
                    h1)

/-- `entriesError` carries the shape statement of each field through the field walk.
`evaluate_entries` at lib/finite_term.ml lines 261 to 266 reports the error of the first field that fails, and it adds no error of its own.
-/
theorem entriesError (g : List Ty) (rho : List Value) (henv : EnvHasType rho g) :
    ∀ (entries : List (String × Term)) (fuel : Nat) (x : Err),
      SafeEntries g entries → evaluateEntries fuel rho entries = .error x → Shapeless x
  | [], _fuel, _x, _hs, h => (res_error_ne_ok h.symm).elim
  | (_label, _field) :: rest, fuel, x, hs, h =>
      match hs with
      | ⟨hs1, hs2⟩ =>
          match res_bind_error h with
          | .inl h1 => hs1 rho fuel x henv h1
          | .inr ⟨r, _hr, h2⟩ =>
              match res_bind_error h2 with
              | .inl h3 => entriesError g rho henv rest r.2 x hs2 h3
              | .inr ⟨_tl, _htl, h4⟩ => (res_error_ne_ok h4.symm).elim

/-- `branchError` inverts one failed branch walk of `evaluateBranch` of Eval.lean.
The walk of lib/finite_term.ml lines 252 and 253 reports the absent label or the error of the one body that the label selects.
-/
theorem branchError : ∀ (branches : List (String × Term)) (fuel : Nat) (rho : List Value)
    (label : String) (payload : Value) (x : Err),
    evaluateBranch fuel rho label payload branches = .error x →
      Shapeless x ∨ ∃ body : Term, lookup label branches = .ok body ∧
        evaluate fuel (payload :: rho) body = .error x
  | [], _fuel, _rho, _label, _payload, _x, h => .inl (errShapeless h True.intro)
  | (key, body) :: more, fuel, rho, label, payload, x, h =>
      boolCases (key == label)
        (fun hfalse =>
          match branchError more fuel rho label payload x
              ((Checker.ite_miss (boolNot hfalse)).symm.trans h) with
          | .inl hs => .inl hs
          | .inr ⟨b, hlk, hev⟩ =>
              .inr ⟨b, (lookupMiss label key body more (beqFalseSymm key label hfalse)).trans hlk,
                hev⟩)
        (fun htrue =>
          .inr ⟨body, lookupHit label key body more (beqSymm key label htrue),
            (Checker.ite_hit htrue).symm.trans h⟩)

mutual
/-- `safePure` states claim C3 at every node of one typing derivation.
It states docs/metatheory.md lines 237 to 243, and the recursion runs on the derivation of `HasType` with the environment and the budget quantified.
The two shape errors of lib/finite_term.ml lines 254 and 260 sit at the case arm and at the project arm, and value typing rules each of them out.
-/
theorem safePure : ∀ (g : List Ty) (t : Term) (a : Ty), HasType g t a → SafeProp g t
  | _, _, _, .var _g index _a _hvar =>
      fun _rho fuel x _henv hev =>
        match res_bind_error hev with
        | .inl h1 => tickShapeless fuel x h1
        | .inr ⟨_f, _htick, h2⟩ =>
            optionElimShapeless h2 True.intro (fun _z _y hh => (res_error_ne_ok hh.symm).elim)
  | _, _, _, .atom _g _name _labels _hmem =>
      fun _rho fuel x _henv hev =>
        match res_bind_error hev with
        | .inl h1 => tickShapeless fuel x h1
        | .inr ⟨_f, _htick, h2⟩ => (res_error_ne_ok h2.symm).elim
  | _, _, _, .tag g _label payload _fibers fiber _hlookup hpayload =>
      fun rho fuel x henv hev =>
        match res_bind_error hev with
        | .inl h1 => tickShapeless fuel x h1
        | .inr ⟨f, _htick, h2⟩ =>
            match res_bind_error h2 with
            | .inl h3 => safePure g payload fiber hpayload rho f x henv h3
            | .inr ⟨_r, _hr, h4⟩ => (res_error_ne_ok h4.symm).elim
  | _, _, _, .«section» g entries fibers sorted pairs hcanon halign hentries =>
      fun rho fuel x henv hev =>
        match res_bind_error hev with
        | .inl h1 => tickShapeless fuel x h1
        | .inr ⟨f, _htick, h2⟩ =>
            match res_bind_error h2 with
            | .inl h3 => (res_error_ne_ok (h3.symm.trans hcanon)).elim
            | .inr ⟨_s, _hs, h4⟩ =>
                match res_bind_error h4 with
                | .inl h5 =>
                    entriesError g rho henv entries f x
                      (safeSortInv g entries
                        (Eq.mp (congrArg (SafeEntries g) (canonical_sorted entries sorted hcanon))
                          (alignSafeFields g fibers sorted pairs halign
                            (safePureEntries g pairs .none hentries))))
                      h5
                | .inr ⟨_r, _hr, h6⟩ => (res_error_ne_ok h6.symm).elim
  | _, _, _, .«case» g scrutinee fibers branches sorted pairs expected hcanon halign hscr
      hbranch =>
      fun rho fuel x henv hev =>
        match res_bind_error hev with
        | .inl h1 => tickShapeless fuel x h1
        | .inr ⟨f, _htick, h2⟩ =>
            match res_bind_error h2 with
            | .inl h3 => safePure g scrutinee (.lan fibers) hscr rho f x henv h3
            | .inr ⟨r, hr, h4⟩ =>
                match r.1, h4, evalPure g scrutinee (.lan fibers) hscr rho f r.1 r.2 henv hr with
                | .atom _name, _hh, hv => False.elim (valueLanTag _ fibers hv)
                | .«section» _fields, _hh, hv => False.elim (valueLanTag _ fibers hv)
                | .tag l p, hh, hv =>
                    match valueTagFiber l p fibers hv with
                    | ⟨fib, hlkFib, hpayload⟩ =>
                        match branchError branches r.2 rho l p x hh with
                        | .inl hs => hs
                        | .inr ⟨body, hlkBody, hev2⟩ =>
                            alignSafeBranches g expected fibers sorted pairs halign
                              (safePureEntries g pairs (.some expected) hbranch) l fib body hlkFib
                              (((congrArg (fun z : List (String × Term) => lookup l z)
                                    (canonical_sorted branches sorted hcanon)).trans
                                  (lookupSort l branches)).trans hlkBody)
                              (p :: rho) r.2 x (.cons p fib rho g hpayload henv) hev2
  | _, _, _, .project g sectionTerm fibers label _a _hlookup hsec =>
      fun rho fuel x henv hev =>
        match res_bind_error hev with
        | .inl h1 => tickShapeless fuel x h1
        | .inr ⟨f, _htick, h2⟩ =>
            match res_bind_error h2 with
            | .inl h3 => safePure g sectionTerm (.ran fibers) hsec rho f x henv h3
            | .inr ⟨r, hr, h4⟩ =>
                match r.1, h4,
                    evalPure g sectionTerm (.ran fibers) hsec rho f r.1 r.2 henv hr with
                | .atom _name, _hh, hv => False.elim (valueRanSection _ fibers hv)
                | .tag _l _p, _hh, hv => False.elim (valueRanSection _ fibers hv)
                | .«section» fields, hh, _hv =>
                    match res_bind_error hh with
                    | .inl h5 => lookupShapeless label fields x h5
                    | .inr ⟨_w, _hw, h6⟩ => (res_error_ne_ok h6.symm).elim

/-- `safePureEntries` states claim C3 for one aligned entry list of either mode.
It is the list partner of `safePure` for the field list of lib/finite_term.ml line 84 and for the branch list of lines 92 and 93.
-/
theorem safePureEntries : ∀ (g : List Ty) (pairs : List (String × Ty × Term))
    (mode : Option Ty), HasTypeEntries g pairs mode → SafePairs g pairs mode
  | _, _, _, .nil g mode => safePairsNil g mode
  | _, _, _, .field g _label fiber fieldTerm rest hterm hrest =>
      ⟨safePure g fieldTerm fiber hterm, safePureEntries g rest .none hrest⟩
  | _, _, _, .branch g _label payloadType body rest expected hbody hrest =>
      ⟨safePure (payloadType :: g) body expected hbody,
        safePureEntries g rest (.some expected) hrest⟩
end

/-- `runShapeless` states that a checked run reports no shape error.
`run` at lib/finite_term.ml lines 268 to 270 checks at the empty context and it evaluates at the empty environment, and
Theorem1 of Checker.lean turns the successful check into a derivation.
-/
theorem runShapeless (f : Nat) (t : Term) (a : Ty) (x : Err) (hcheck : check f [] t a = .ok ())
    (h : run f t a = .error x) : Shapeless x :=
  match res_bind_ok hcheck with
  | ⟨_r, hr, _hu⟩ =>
      match res_bind_error h with
      | .inl h1 => (res_error_ne_ok (h1.symm.trans hr)).elim
      | .inr ⟨fuel, _hf, h2⟩ =>
          match res_bind_error h2 with
          | .inl h3 => safePure [] t a (check_sound f [] t a hcheck) [] fuel x .nil h3
          | .inr ⟨_r2, _hr2, h4⟩ => (res_error_ne_ok h4.symm).elim

end Evaluation

open Evaluation in
/-- `run_never_expected_shape` states row Theorem4-C3 of the stage brief.
It states docs/metatheory.md lines 237 to 243, and the two shape errors of lib/finite_term.ml lines 254 and 260 never leave a checked run.
-/
theorem run_never_expected_shape (f : Nat) (t : Term) (a : Ty) (hcheck : check f [] t a = .ok ()) :
    run f t a ≠ .error .expectedLan ∧ run f t a ≠ .error .expectedRan :=
  ⟨fun h => runShapeless f t a .expectedLan hcheck h,
    fun h => runShapeless f t a .expectedRan hcheck h⟩

namespace Evaluation

/-- `tickInv` reads one successful tick as a budget of one unit at least.
`tick` of Check.lean is the charge point of decision S2-D4 and it drops the budget of one unit.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem tickInv : ∀ (f g : Nat), tick f = .ok g → f = g + 1
  | 0, _g, h => (res_error_ne_ok h).elim
  | _k + 1, _g, h => congrArg (fun z : Nat => z + 1) (Except.ok.inj h)

/-- `tickMk` runs the charge point at the exact budget of one node.
It is the partner of `tickInv` and it rebuilds one run at the cost that the run needs.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem tickMk (c : Nat) : tick (c + 1) = .ok c := rfl

/-- `costTick` adds the node of one charge point to the cost of the parts. docs/metatheory.md lines 92 to 96 charge one unit for one entered node.
-/
theorem costTick {f g c rest : Nat} (ht : tick f = .ok g) (h : c + rest = g) : c + 1 + rest = f :=
  (Nat.succ_add c rest).trans ((congrArg (fun z : Nat => z + 1) h).trans (tickInv f g ht).symm)

/-- `costLeaf` states the cost of one leaf node, which is the charge point alone.
The var arm and the atom arm of lib/finite_term.ml lines 237 to 244 read no subterm.
-/
theorem costLeaf {f g rest : Nat} (ht : tick f = .ok g) (h : rest = g) : 1 + rest = f :=
  (congrArg (fun z : Nat => 1 + z) h).trans ((Nat.add_comm 1 g).trans (tickInv f g ht).symm)

/-- `costLe1` raises one cost bound of a part to the bound of the node above it.
`size` of Check.lean counts one unit for the node and the count of each part.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem costLe1 {c n : Nat} (h : c ≤ n) : c + 1 ≤ 1 + n :=
  Eq.mp (congrArg (fun z : Nat => c + 1 ≤ z) (Nat.add_comm n 1)) (Nat.succ_le_succ h)

/-- `costLeCase` bounds the cost of one case node with the count of its two parts.
`size` at the case arm counts the node, the scrutinee and the whole branch list.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem costLeCase {c1 c2 s e : Nat} (h1 : c1 ≤ s) (h2 : c2 ≤ e) : c1 + c2 + 1 ≤ 1 + s + e :=
  Eq.mp (congrArg (fun z : Nat => z ≤ 1 + s + e) (Nat.succ_add c1 c2))
    (Nat.add_le_add (costLe1 h1) h2)

/-- `twoMul` reads the doubled budget of row Theorem4-C4 as one sum.
The fuel `2 * size t` of docs/metatheory.md lines 244 to 250 pays the check and the evaluation.
-/
theorem twoMul (n : Nat) : 2 * n = n + n :=
  (Nat.succ_mul 1 n).trans (congrArg (fun z : Nat => z + n) (Nat.one_mul n))

/-- `sizeLeTwo` states that the doubled budget covers one check.
`check_complete` of Checker.lean asks for a budget of `size t` at least.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem sizeLeTwo (n : Nat) : n ≤ 2 * n :=
  Nat.le.intro (twoMul n).symm

mutual
/-- `evalCost` reads one successful evaluation as a run at its own exact cost.
The cost never passes `size t` of Check.lean, since one entered node charges one unit at lib/finite_term.ml lines 236 to 260 and one case node enters one branch alone.
This statement is the tight partner of `evaluate_mono_add` of Budget.lean, which raises a run.
-/
theorem evalCost : ∀ (t : Term) (fuel : Nat) (rho : List Value) (v : Value) (rest : Nat),
    evaluate fuel rho t = .ok (v, rest) →
      ∃ c : Nat, c + rest = fuel ∧ c ≤ size t ∧ evaluate c rho t = .ok (v, 0)
  | .var index, _fuel, _rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨_g, ht, h2⟩ =>
          match optionElimSome h2 with
          | ⟨_w, hsome, hk⟩ =>
              ⟨1, costLeaf ht (congrArg Prod.snd (Except.ok.inj hk)).symm, Nat.le_refl 1,
                res_bind_mk (a := 0) (tickMk 0)
                  ((congrArg
                      (fun z : Option Value =>
                        z.elim (Except.error (Err.invalidVariable index) : Res (Value × Nat))
                          (fun value => Except.ok (value, 0))) hsome).trans
                    (congrArg (fun z : Value => (Except.ok (z, 0) : Res (Value × Nat)))
                      (congrArg Prod.fst (Except.ok.inj hk))))⟩
  | .atom _name, _fuel, _rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨_g, ht, h2⟩ =>
          ⟨1, costLeaf ht (congrArg Prod.snd (Except.ok.inj h2)).symm, Nat.le_refl 1,
            res_bind_mk (a := 0) (tickMk 0)
              (congrArg (fun z : Value => (Except.ok (z, 0) : Res (Value × Nat)))
                (congrArg Prod.fst (Except.ok.inj h2)))⟩
  | .tag _label payload, _fuel, rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              match evalCost payload g rho r.1 r.2 hr with
              | ⟨c1, hc1, hle1, he1⟩ =>
                  ⟨c1 + 1,
                    costTick ht
                      ((congrArg (fun z : Nat => c1 + z)
                        (congrArg Prod.snd (Except.ok.inj h3))).symm.trans hc1),
                    costLe1 hle1,
                    res_bind_mk (a := c1) (tickMk c1)
                      (res_bind_mk (a := (r.1, 0)) he1
                        (congrArg (fun z : Value => (Except.ok (z, 0) : Res (Value × Nat)))
                          (congrArg Prod.fst (Except.ok.inj h3))))⟩
  | .«section» entries, _fuel, rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨sorted, hsorted, h3⟩ =>
              match res_bind_ok h3 with
              | ⟨r, hr, h4⟩ =>
                  match evalCostEntries entries g rho r.1 r.2 hr with
                  | ⟨c1, hc1, hle1, he1⟩ =>
                      ⟨c1 + 1,
                        costTick ht
                          ((congrArg (fun z : Nat => c1 + z)
                            (congrArg Prod.snd (Except.ok.inj h4))).symm.trans hc1),
                        costLe1 hle1,
                        res_bind_mk (a := c1) (tickMk c1)
                          (res_bind_mk (a := sorted) hsorted
                            (res_bind_mk (a := (r.1, 0)) he1
                              (congrArg (fun z : Value => (Except.ok (z, 0) : Res (Value × Nat)))
                                (congrArg Prod.fst (Except.ok.inj h4)))))⟩
  | .«case» scrutinee _st branches, _fuel, rho, v, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              match r.1, h3, evalCost scrutinee g rho r.1 r.2 hr with
              | .atom _name, hh, _ih => (res_error_ne_ok hh).elim
              | .«section» _fields, hh, _ih => (res_error_ne_ok hh).elim
              | .tag l p, hh, ⟨c1, hc1, hle1, he1⟩ =>
                  match evalCostBranch branches r.2 rho l p v rest hh with
                  | ⟨c2, hc2, hle2, he2⟩ =>
                      ⟨c1 + c2 + 1,
                        costTick ht
                          ((Nat.add_assoc c1 c2 rest).trans
                            ((congrArg (fun z : Nat => c1 + z) hc2).trans hc1)),
                        costLeCase hle1 hle2,
                        res_bind_mk (a := c1 + c2) (tickMk (c1 + c2))
                          (res_bind_mk (a := (Value.tag l p, c2))
                            (Eq.mp
                              (congrArg
                                (fun z : Nat =>
                                  evaluate (c1 + c2) rho scrutinee = .ok (Value.tag l p, z))
                                (Nat.zero_add c2))
                              (evaluate_mono_add scrutinee c1 c2 rho (.tag l p) 0 he1))
                            he2)⟩
  | .project field _st _label, _fuel, rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              match r.1, h3, evalCost field g rho r.1 r.2 hr with
              | .atom _name, hh, _ih => (res_error_ne_ok hh).elim
              | .tag _l _p, hh, _ih => (res_error_ne_ok hh).elim
              | .«section» fields, hh, ⟨c1, hc1, hle1, he1⟩ =>
                  match res_bind_ok hh with
                  | ⟨w, hlk, h4⟩ =>
                      ⟨c1 + 1,
                        costTick ht
                          ((congrArg (fun z : Nat => c1 + z)
                            (congrArg Prod.snd (Except.ok.inj h4))).symm.trans hc1),
                        costLe1 hle1,
                        res_bind_mk (a := c1) (tickMk c1)
                          (res_bind_mk (a := (Value.«section» fields, 0)) he1
                            (res_bind_mk (a := w) hlk
                              (congrArg (fun z : Value => (Except.ok (z, 0) : Res (Value × Nat)))
                                (congrArg Prod.fst (Except.ok.inj h4)))))⟩

/-- `evalCostEntries` is the entry list partner of `evalCost`.
The field walk at lib/finite_term.ml lines 261 to 266 adds the cost of each field and it holds no charge point of its own.
-/
theorem evalCostEntries : ∀ (entries : List (String × Term)) (fuel : Nat) (rho : List Value)
    (vals : List (String × Value)) (rest : Nat),
    evaluateEntries fuel rho entries = .ok (vals, rest) →
      ∃ c : Nat, c + rest = fuel ∧ c ≤ sizeEntries entries ∧
        evaluateEntries c rho entries = .ok (vals, 0)
  | [], _fuel, _rho, _vals, rest, h =>
      ⟨0, (Nat.zero_add rest).trans (congrArg Prod.snd (Except.ok.inj h)).symm, Nat.le_refl 0,
        congrArg
          (fun z : List (String × Value) =>
            (Except.ok (z, 0) : Res (List (String × Value) × Nat)))
          (congrArg Prod.fst (Except.ok.inj h))⟩
  | (_label, field) :: more, _fuel, rho, _vals, rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              match evalCost field _fuel rho head.1 head.2 hhead with
              | ⟨c1, hc1, hle1, he1⟩ =>
                  match evalCostEntries more head.2 rho tail.1 tail.2 htail with
                  | ⟨c2, hc2, hle2, he2⟩ =>
                      ⟨c1 + c2,
                        (Nat.add_assoc c1 c2 rest).trans
                          ((congrArg (fun z : Nat => c1 + z)
                            ((congrArg (fun z : Nat => c2 + z)
                              (congrArg Prod.snd (Except.ok.inj h3))).symm.trans hc2)).trans hc1),
                        Nat.add_le_add hle1 hle2,
                        res_bind_mk (a := (head.1, c2))
                          (Eq.mp
                            (congrArg
                              (fun z : Nat => evaluate (c1 + c2) rho field = .ok (head.1, z))
                              (Nat.zero_add c2))
                            (evaluate_mono_add field c1 c2 rho head.1 0 he1))
                          (res_bind_mk (a := (tail.1, 0)) he2
                            (congrArg
                              (fun z : List (String × Value) =>
                                (Except.ok (z, 0) :
                                  Res (List (String × Value) × Nat)))
                              (congrArg Prod.fst (Except.ok.inj h3))))⟩

/-- `evalCostBranch` is the branch list partner of `evalCost`.
The walk of lib/finite_term.ml lines 252 and 253 runs one body alone, so the cost never passes the count of the whole branch list.
-/
theorem evalCostBranch : ∀ (branches : List (String × Term)) (fuel : Nat) (rho : List Value)
    (label : String) (payload : Value) (v : Value) (rest : Nat),
    evaluateBranch fuel rho label payload branches = .ok (v, rest) →
      ∃ c : Nat, c + rest = fuel ∧ c ≤ sizeEntries branches ∧
        evaluateBranch c rho label payload branches = .ok (v, 0)
  | [], _fuel, _rho, _label, _payload, _v, _rest, h => (res_error_ne_ok h).elim
  | (key, body) :: more, fuel, rho, label, payload, v, rest, h =>
      boolCases (key == label)
        (fun hfalse =>
          match evalCostBranch more fuel rho label payload v rest
              ((Checker.ite_miss (boolNot hfalse)).symm.trans h) with
          | ⟨c, hc, hle, hev⟩ =>
              ⟨c, hc, Nat.le_trans hle (Nat.le_add_left (sizeEntries more) (size body)),
                (Checker.ite_miss (boolNot hfalse)).trans hev⟩)
        (fun htrue =>
          match evalCost body fuel (payload :: rho) v rest
              ((Checker.ite_hit htrue).symm.trans h) with
          | ⟨c, hc, hle, hev⟩ =>
              ⟨c, hc, Nat.le_trans hle (Nat.le_add_right (size body) (sizeEntries more)),
                (Checker.ite_hit htrue).trans hev⟩)
end

end Evaluation

open Evaluation in
/-- `run_budget_two_size` states row Theorem4-C4 of the stage brief.
It states docs/metatheory.md lines 243 to 246, and the budget `2 * size t` pays the check of
`check_complete` of Checker.lean and the evaluation at its own cost.
`run` at lib/finite_term.ml lines 268 to 270 returns the same value at the fixed budget.
-/
theorem run_budget_two_size (f : Nat) (t : Term) (a : Ty) (v : Value) (h : run f t a = .ok v) :
    run (2 * size t) t a = .ok v :=
  match res_bind_ok h with
  | ⟨f1, hcore, h2⟩ =>
      match res_bind_ok h2 with
      | ⟨r, hev, h3⟩ =>
          match res_bind_ok
            (check_complete (2 * size t) [] t a
              (check_sound f [] t a (res_bind_mk hcore rfl)) (sizeLeTwo (size t))) with
          | ⟨f2, hcore2, _hu⟩ =>
              match evalCost t f1 [] r.1 r.2 hev with
              | ⟨c, _hc, hle, he⟩ =>
                  res_bind_mk (a := f2) hcore2
                    (res_bind_mk (a := (r.1, 0 + size t - c))
                      (Eq.mp
                        (congrArg
                          (fun z : Nat => evaluate z [] t = .ok (r.1, 0 + size t - c))
                          (Nat.add_right_cancel
                            ((check_core_cost (2 * (2 * size t) + 2) t (2 * size t) [] a f2
                              hcore2).trans (twoMul (size t)))).symm)
                        (budget_monotone_evaluate c (size t) [] t r.1 0 hle he))
                      (congrArg (fun z : Value => (Except.ok z : Res Value))
                        (Except.ok.inj h3)))
