import KanEvmProofs.EvalSubst
import KanEvmProofs.Evaluation
import KanEvmProofs.NormalizeTyping
import KanEvmProofs.NormalizeCore

/-! # Agreement of the normalizer with the evaluator

This module proves row Theorem6-11.5, `normalize_agrees_with_run`.
It relates successful `normalize` and `run` calls on the same closed term and type,
using independent fuel budgets. The reduced term equals the quote of the evaluated value.
The core induction needs no typing assumption and also constructs an evaluation of the reduced term.
Both successful calls are hypotheses, so the theorem claims no successful fuel bound.

Claim C7, a universal successful normalization fuel bound, remains open.
This conditional agreement theorem supplies no such bound, axiom, or proof placeholder.
Strong normalization and confluence remain open in docs/metatheory.md section 12
and docs/validation.md.

Every proof of this module runs in term mode, so the module holds no tactic block.
-/

namespace NormAgree

/-- `mapInsert` moves the label view across one insertion step of the sort of Check.lean.
It repeats `mapInsertEntry` of
NormalizeTyping.lean over an arbitrary payload, which the value list of
`quote` at docs/metatheory.md lines 383 to 386 needs.
The sort mirrors lib/finite_term.ml line 21.
-/
theorem mapInsert {α : Type} (key : String) (value : α) :
    (entries : List (String × α)) →
      List.map Prod.fst (insertEntry (key, value) entries)
        = insertLabel key (List.map Prod.fst entries)
  | [] => rfl
  | (k2, _v2) :: rest =>
      ite_elim
        (P := fun (z : List (String × α)) =>
          List.map Prod.fst z = insertLabel key (k2 :: List.map Prod.fst rest))
        (fun hc => (if_pos hc).symm)
        (fun hc =>
          (congrArg (fun (z : List String) => k2 :: z) (mapInsert key value rest)).trans
            (if_neg hc).symm)

/-- `mapSort` moves the label view across the whole sort of Check.lean.
It repeats `mapSortEntries` of NormalizeTyping.lean over an arbitrary payload.
The sort mirrors lib/finite_term.ml line 21 and docs/metatheory.md lines 23 and 24 names its order.
-/
theorem mapSort {α : Type} :
    (entries : List (String × α)) →
      List.map Prod.fst (sortEntries entries) = sortLabels (List.map Prod.fst entries)
  | [] => rfl
  | (k, v) :: rest =>
      (mapInsert k v (sortEntries rest)).trans (congrArg (insertLabel k) (mapSort rest))

/-- `insertFix` states that the insertion step puts one small label at the front of the list.
It repeats `insertFix` of NormalizeTyping.lean over an arbitrary payload.
The step mirrors lib/finite_term.ml line 26 and docs/metatheory.md lines 23 and 24 names its order.
-/
theorem insertFix {α : Type} (key : String) (value : α) :
    (entries : List (String × α)) →
      Canon.LeHead key (List.map Prod.fst entries) →
      insertEntry (key, value) entries = (key, value) :: entries
  | [], h => Canon.hold_first rfl h
  | (k2, _v2) :: _rest, h => if_pos (h : labelLe key k2 = true)

/-- `sortFix` states that the sort keeps one list that already holds the ascending label order.
It repeats `sortFix` of NormalizeTyping.lean over an arbitrary payload.
The sort mirrors lib/finite_term.ml line 21 and docs/metatheory.md lines 23 and 24 names its order.
-/
theorem sortFix {α : Type} :
    (entries : List (String × α)) →
      Ty.SortedLabels (List.map Prod.fst entries) → sortEntries entries = entries
  | [], h => Canon.hold_first rfl h
  | (k, v) :: rest, h =>
      (congrArg (insertEntry (k, v))
          (sortFix rest (Canon.sortedLabels_uncons k (List.map Prod.fst rest) h).2)).trans
        (insertFix k v rest (Canon.sortedLabels_uncons k (List.map Prod.fst rest) h).1)

/-- `sortSorted` states that the sort of Check.lean returns the ascending label order.
The sort mirrors lib/finite_term.ml line 21 and docs/metatheory.md lines 23 and 24 names that order.
-/
theorem sortSorted {α : Type} (entries : List (String × α)) :
    Ty.SortedLabels (List.map Prod.fst (sortEntries entries)) :=
  cast (congrArg Ty.SortedLabels (mapSort entries)).symm
    (Canon.sortLabels_sorted (List.map Prod.fst entries))

/-- `sortIdem` states that a second sort of Check.lean changes no list.
The evaluator sorts the field values of one section at lib/finite_term.ml line 245, and the normal form of that section holds the same order, which docs/metatheory.md line 385 needs.
-/
theorem sortIdem {α : Type} (entries : List (String × α)) :
    sortEntries (sortEntries entries) = sortEntries entries :=
  sortFix (sortEntries entries) (sortSorted entries)

/-- `lookupInsertAny` states that one insertion step of the sort keeps every read of the association list.
It repeats `lookupInsert` of NormalizeTyping.lean over an arbitrary payload, which the value list of docs/metatheory.md line 385 needs.
`insertEntry` of Check.lean mirrors the stable insertion of lib/finite_term.ml line 26.
-/
theorem lookupInsertAny {α : Type} (l key : String) (value : α) :
    (entries : List (String × α)) →
      List.lookup l (insertEntry (key, value) entries)
        = List.lookup l ((key, value) :: entries)
  | [] => rfl
  | (k2, v2) :: rest =>
      ite_elim
        (P := fun (z : List (String × α)) =>
          List.lookup l z = List.lookup l ((key, value) :: (k2, v2) :: rest))
        (fun hyes => Canon.hold_first rfl hyes)
        (fun hc =>
          (NormTyping.lookupIte l k2 v2 (insertEntry (key, value) rest)).trans
            (ite_elim
              (P := fun (z : Option α) =>
                z = List.lookup l ((key, value) :: (k2, v2) :: rest))
              (fun hh =>
                ((NormTyping.lookupIte l key value ((k2, v2) :: rest)).trans
                  ((if_neg (fun (hk : (l == key) = true) =>
                      hc (Eq.mp
                        (congrArg (fun (z : String) => labelLe key z = true)
                          ((NormTyping.beqEq l key hk).symm.trans (NormTyping.beqEq l k2 hh)))
                        (NormTyping.labelLeSelf key)))).trans
                    ((NormTyping.lookupIte l k2 v2 rest).trans (if_pos hh)))).symm)
              (fun hh =>
                ((lookupInsertAny l key value rest).trans
                    (NormTyping.lookupIte l key value rest)).trans
                  ((NormTyping.lookupIte l key value ((k2, v2) :: rest)).trans
                    (congrArg
                      (fun (z : Option α) => if (l == key) = true then some value else z)
                      ((NormTyping.lookupIte l k2 v2 rest).trans (if_neg hh)))).symm)))

/-- `lookupSortAny` states that the sort of Check.lean keeps every read of the association list.
It repeats `lookupSort` of NormalizeTyping.lean over an arbitrary payload.
The sort is stable, so the first entry of one label stays the first entry of that label, which the branch read of lib/finite_term.ml lines 252 and 253 needs.
-/
theorem lookupSortAny {α : Type} (l : String) :
    (entries : List (String × α)) →
      List.lookup l (sortEntries entries) = List.lookup l entries
  | [] => rfl
  | (k, v) :: rest =>
      (lookupInsertAny l k v (sortEntries rest)).trans
        ((NormTyping.lookupIte l k v (sortEntries rest)).trans
          ((congrArg (fun (z : Option α) => if (l == k) = true then some v else z)
              (lookupSortAny l rest)).trans
            (NormTyping.lookupIte l k v rest).symm))

/-- `quoteLabels` states that `quote` of Eval.lean keeps every label of one field list. docs/metatheory.md line 385 maps the values of one section and it holds the labels.
-/
theorem quoteLabels :
    (fields : List (String × Value)) →
      List.map Prod.fst (quoteEntries fields) = List.map Prod.fst fields
  | [] => rfl
  | (label, _value) :: rest =>
      congrArg (fun (z : List String) => label :: z) (quoteLabels rest)

/-- `lookupQuote` reads one label out of the quoted field list of docs/metatheory.md line 385.
The read of the quoted list is the quote of the read, so the projection of lib/finite_term.ml line 206 agrees with the projection of lines 257 to 259.
-/
theorem lookupQuote (l : String) :
    (fields : List (String × Value)) →
      List.lookup l (quoteEntries fields) = Option.map quote (List.lookup l fields)
  | [] => rfl
  | (label, value) :: rest =>
      (NormTyping.lookupIte l label (quote value) (quoteEntries rest)).trans
        ((ite_case (c := (l == label) = true)
            (P := fun (x : Option Term) (y : Option Value) => x = Option.map quote y)
            (fun _hc => rfl) (fun _hc => lookupQuote l rest)).trans
          (congrArg (Option.map quote) (NormTyping.lookupIte l label value rest)).symm)

/-- `canonUnique` reads the distinctness test out of one successful `canonicalEntries`.
It repeats `uniqueOf` of NormalizeTyping.lean over an arbitrary payload.
`canonicalEntries` mirrors lib/finite_term.ml lines 20 to 23 and line 22 holds that test.
-/
theorem canonUnique {α : Type} (entries sorted : List (String × α))
    (h : canonicalEntries entries = Except.ok sorted) :
    unique (List.map Prod.fst (sortEntries entries)) = Except.ok () :=
  match res_bind_ok h with
  | ⟨_u, hu, _hk⟩ => hu

/-- `varNil` refutes one variable read at the empty environment.
`run` at lib/finite_term.ml lines 268 to 270 evaluates at the empty environment, so the variable arm of line 239 stops with an error there. docs/metatheory.md lines 368 to 372 state the closed setting of this module.
-/
theorem varNil {index g : Nat} {v : Value} {re : Nat}
    (h : (([] : List Value)[index]?).elim (Except.error (Err.invalidVariable index))
      (fun value => Except.ok (value, g)) = Except.ok (v, re)) : False :=
  res_error_ne_ok
    (cast (congrArg (fun (o : Option Value) =>
        o.elim (Except.error (Err.invalidVariable index))
          (fun value => Except.ok (value, g)) = Except.ok (v, re)) List.getElem?_nil) h)

/-- `beqSymm` swaps the two sides of one label test. `evaluateBranch` of Eval.lean tests the branch label against the tag label, and
`List.lookup` tests the tag label against the branch label, so the two reads of lib/finite_term.ml lines 40 and 41 and lines 252 and 253 meet here.
-/
theorem beqSymm (a b : String) (h : (a == b) = true) : (b == a) = true :=
  match NormTyping.beqEq a b h with
  | rfl => beq_self_eq_true a

/-- `tagPayload` reads the payload run out of one successful tag evaluation.
The tag arm of lib/finite_term.ml lines 242 and 243 evaluates the payload first, so a successful tag value carries one successful payload run. docs/metatheory.md lines 373 to 378 need that run for the case redex.
-/
theorem tagPayload (label : String) (p : Term) (fq : Nat) (pv : Value) (rq : Nat)
    (h : evaluate fq [] (Term.tag label p) = Except.ok (Value.tag label pv, rq)) :
    ∃ (f2 r2 : Nat), evaluate f2 [] p = Except.ok (pv, r2) :=
  match res_bind_ok h with
  | ⟨g, _ht, h2⟩ =>
      match res_bind_ok h2 with
      | ⟨res, hres, h3⟩ =>
          ⟨g, res.2,
            hres.trans
              (congrArg (fun (z : Value) => (Except.ok (z, res.2) : Res (Value × Nat)))
                (Value.tag.inj (congrArg Prod.fst (Except.ok.inj h3))).2)⟩

/-- `branchLookup` reads the branch walk of Eval.lean as one association list read.
`evaluateBranch` replaces the branch lookup of lib/finite_term.ml lines 252 and 253, per decision
S2-D5, and it takes the first label match, as `lookup` at lines 40 and 41 does.
The normalizer reads the same branch through `lookup`, so both sides pick one body.
-/
theorem branchLookup : ∀ (bs : List (String × Term)) (fu : Nat) (rho : List Value) (l : String)
    (pay w : Value) (rest : Nat),
    evaluateBranch fu rho l pay bs = Except.ok (w, rest) →
      ∃ body : Term, List.lookup l bs = some body
        ∧ evaluate fu (pay :: rho) body = Except.ok (w, rest)
  | [], _fu, _rho, _l, _pay, _w, _rest, h => (res_error_ne_ok h).elim
  | (key, body) :: more, fu, rho, l, pay, w, rest, h =>
      ite_elim
        (P := fun (z : Res (Value × Nat)) =>
          z = Except.ok (w, rest) →
            ∃ b : Term, List.lookup l ((key, body) :: more) = some b
              ∧ evaluate fu (pay :: rho) b = Except.ok (w, rest))
        (fun hc hz =>
          ⟨body,
            (NormTyping.lookupIte l key body more).trans (if_pos (beqSymm key l hc)), hz⟩)
        (fun hc hz =>
          match branchLookup more fu rho l pay w rest hz with
          | ⟨b, hb, he⟩ =>
            ⟨b,
              (NormTyping.lookupIte l key body more).trans
                ((if_neg (fun hk => hc (beqSymm l key hk))).trans hb),
              he⟩)
        h

/-- `Agrees` states the agreement of one reduced term with one value.
The first part reads the term as the quote of the value of docs/metatheory.md lines 383 to 386.
The second part runs the term back to that value at `evaluate` of lib/finite_term.ml lines 236 to 260, and the case redex of lines 187 to 190 needs that run for its payload.
-/
def Agrees (x : Term) (v : Value) : Prop :=
  x = quote v ∧ ∃ (f rest : Nat), evaluate f [] x = Except.ok (v, rest)

/-- `agreesCast` moves one agreement across the two equations of one returned pair.
Each arm of lib/finite_term.ml lines 162 to 225 names the parts of one returned pair, and docs/metatheory.md lines 368 to 402 state the agreement over those parts.
-/
theorem agreesCast {x0 x : Term} {v0 v : Value} (hx : x0 = x) (hv : v0 = v) (p : Agrees x0 v0) :
    Agrees x v :=
  Eq.mp (congrArg (fun (z : Value) => Agrees x z) hv)
    (Eq.mp (congrArg (fun (z : Term) => Agrees z v0) hx) p)

/-- `atomAgrees` states the agreement at one atom node.
`reduce` returns the atom unchanged at lib/finite_term.ml lines 166 and 167, and `evaluate` returns the atom value at line 240. docs/metatheory.md lines 383 to 386 quote that value to the same term.
-/
theorem atomAgrees (name : String) : Agrees (Term.atom name) (Value.atom name) :=
  ⟨rfl, 1, 0, rfl⟩

/-- `bindOkTag` rebuilds one tag run out of one payload run.
The tag arm of `evaluate` at lib/finite_term.ml lines 241 to 243 wraps the payload value, and docs/metatheory.md lines 383 to 386 quote the tag value to the tag term.
-/
theorem bindOkTag (label : String) (e : Res (Value × Nat)) (v : Value) (rest : Nat)
    (h : e = Except.ok (v, rest)) :
    (e >>= fun (res : Value × Nat) =>
        (Except.ok (Value.tag label res.1, res.2) : Res (Value × Nat)))
      = Except.ok (Value.tag label v, rest) :=
  congrArg
    (fun (z : Res (Value × Nat)) =>
      z >>= fun (res : Value × Nat) =>
        (Except.ok (Value.tag label res.1, res.2) : Res (Value × Nat)))
    h

/-- `tagAgrees` lifts one agreement through one tag node.
The tag arm of `reduce` at lib/finite_term.ml lines 171 to 175 keeps the label, and the tag arm of `evaluate` at lines 241 to 243 builds the tag value. docs/metatheory.md lines 383 to 386 quote the tag value to the tag term.
-/
theorem tagAgrees (label : String) (x : Term) (v : Value) (p : Agrees x v) :
    Agrees (Term.tag label x) (Value.tag label v) :=
  ⟨congrArg (fun (z : Term) => Term.tag label z) p.1,
    match p.2 with
    | ⟨f, rest, hev⟩ => ⟨f + 1, rest, bindOkTag label (evaluate f [] x) v rest hev⟩⟩

/-- `pairedLabels` states that one pairing of Evaluation.lean holds one shared label sequence.
`evaluate_entries` at lib/finite_term.ml lines 261 to 266 keeps the label of each field, and docs/metatheory.md line 385 maps the values under those labels.
-/
theorem pairedLabels (rho : List Value) :
    ∀ (values : List (String × Value)) (terms : List (String × Term)),
      Evaluation.Paired rho values terms →
        List.map Prod.fst values = List.map Prod.fst terms
  | _, _, .nil => rfl
  | _, _, .cons l0 _v0 _t0 vs ts _f0 _r0 _hev htail =>
      congrArg (fun (z : List String) => l0 :: z) (pairedLabels rho vs ts htail)

/-- `pairedLookup` reads one label out of one pairing of Evaluation.lean.
Both lists hold one label sequence, so one read of the value list and one read of the term list name one position. docs/metatheory.md line 385 needs that read for the projection of lib/finite_term.ml lines 257 to 259.
-/
theorem pairedLookup (rho : List Value) (l : String) (w : Value) (tm : Term) :
    ∀ (values : List (String × Value)) (terms : List (String × Term)),
      Evaluation.Paired rho values terms → List.lookup l values = some w →
        List.lookup l terms = some tm → ∃ (f r : Nat), evaluate f rho tm = Except.ok (w, r)
  | _, _, .nil, hv, _ht => (Evaluation.noneNeSome rfl hv).elim
  | _, _, .cons l0 v0 t0 vs ts f0 r0 hev htail, hv, ht =>
      ite_case (c := (l == l0) = true)
        (P := fun (zv : Option Value) (zt : Option Term) =>
          zv = some w → zt = some tm → ∃ (f r : Nat), evaluate f rho tm = Except.ok (w, r))
        (fun _hc hzv hzt =>
          ⟨f0, r0,
            Eq.mp
              (congrArg (fun (z : Term) => evaluate f0 rho z = Except.ok (w, r0))
                (Option.some.inj hzt))
              (Eq.mp
                (congrArg (fun (z : Value) => evaluate f0 rho t0 = Except.ok (z, r0))
                  (Option.some.inj hzv))
                hev)⟩)
        (fun _hc hzv hzt => pairedLookup rho l w tm vs ts htail hzv hzt)
        ((NormTyping.lookupIte l l0 v0 vs).symm.trans hv)
        ((NormTyping.lookupIte l l0 t0 ts).symm.trans ht)

/-- `canonMk` rebuilds one successful `canonical entries` run out of one distinctness test.
`canonicalEntries` mirrors lib/finite_term.ml lines 20 to 23, and line 22 holds the test that this lemma supplies. docs/metatheory.md lines 23 and 24 name the sorted result.
-/
theorem canonMk {α : Type} (entries : List (String × α))
    (hu : unique (List.map Prod.fst (sortEntries entries)) = Except.ok ()) :
    canonicalEntries entries = Except.ok (sortEntries entries) :=
  congrArg
    (fun (z : Res Unit) =>
      z >>= fun (_u : Unit) => (Except.ok (sortEntries entries) : Res (List (String × α))))
    hu

/-- `entriesGlue` runs one field list at one budget that covers the head run and the tail run.
`evaluate_entries` at lib/finite_term.ml lines 261 to 266 threads one budget, and the raise of docs/metatheory.md lines 87 to 91 lifts each part to the shared budget.
-/
theorem entriesGlue (label : String) (x : Term) (w : Value) (terms : List (String × Term))
    (vs : List (String × Value)) (fh rh ft rt : Nat)
    (hhead : evaluate fh [] x = Except.ok (w, rh))
    (htail : evaluateEntries ft [] terms = Except.ok (vs, rt)) :
    evaluateEntries (fh + ft) [] ((label, x) :: terms)
      = Except.ok ((label, w) :: vs, rt + rh) :=
  (congrArg
      (fun (z : Res (Value × Nat)) =>
        z >>= fun (result : Value × Nat) =>
          evaluateEntries result.2 [] terms >>= fun (tail : List (String × Value) × Nat) =>
            (Except.ok ((label, result.1) :: tail.1, tail.2)
              : Res (List (String × Value) × Nat)))
      (evaluate_mono_add x fh ft [] w rh hhead)).trans
    (congrArg
      (fun (z : Res (List (String × Value) × Nat)) =>
        z >>= fun (tail : List (String × Value) × Nat) =>
          (Except.ok ((label, w) :: tail.1, tail.2) : Res (List (String × Value) × Nat)))
      ((congrArg (fun (z : Nat) => evaluateEntries z [] terms) (Nat.add_comm ft rh)).symm.trans
        (evaluate_entries_mono_add terms ft rh [] vs rt htail)))

/-- `sectionMk` runs one section term back to one section value.
The section arm of `evaluate` at lib/finite_term.ml lines 244 to 247 tests the labels, runs the fields and sorts the values, and docs/metatheory.md lines 383 to 386 need that run at one quoted field list.
-/
theorem sectionMk (out : List (String × Term)) (values : List (String × Value)) (f rest : Nat)
    (hu : unique (List.map Prod.fst (sortEntries out)) = Except.ok ())
    (hs : sortEntries values = values)
    (hev : evaluateEntries f [] out = Except.ok (values, rest)) :
    evaluate (f + 1) [] (Term.«section» out) = Except.ok (Value.«section» values, rest) :=
  (congrArg
      (fun (z : Res (List (String × Term))) =>
        z >>= fun (_sorted : List (String × Term)) =>
          evaluateEntries f [] out >>= fun (result : List (String × Value) × Nat) =>
            (Except.ok (Value.«section» (sortEntries result.1), result.2) : Res (Value × Nat)))
      (canonMk out hu)).trans
    ((congrArg
        (fun (z : Res (List (String × Value) × Nat)) =>
          z >>= fun (result : List (String × Value) × Nat) =>
            (Except.ok (Value.«section» (sortEntries result.1), result.2) : Res (Value × Nat)))
        hev).trans
      (congrArg
        (fun (z : List (String × Value)) => (Except.ok (Value.«section» z, rest) : Res (Value × Nat)))
        hs))

/-- `fieldRound` reads one field run out of one section run.
The section value of lib/finite_term.ml lines 244 to 247 holds one value per label, and the projection of lines 257 to 259 reads one of them. docs/metatheory.md lines 383 to 386 quote that field value back to its own term.
-/
theorem fieldRound (ents : List (String × Value)) (l : String) (w : Value) (f rest : Nat)
    (hsec : evaluate f [] (Term.«section» (quoteEntries ents))
      = Except.ok (Value.«section» ents, rest))
    (hlook : List.lookup l ents = some w) :
    ∃ (f2 r2 : Nat), evaluate f2 [] (quote w) = Except.ok (w, r2) :=
  match res_bind_ok hsec with
  | ⟨g, _ht, h2⟩ =>
      match res_bind_ok h2 with
      | ⟨_sorted, _hcanon, h3⟩ =>
          match res_bind_ok h3 with
          | ⟨eres, hee, h4⟩ =>
              match eres, hee, h4 with
              | (vals, fu2), hee2, h42 =>
                  pairedLookup [] l w (quote w) vals (quoteEntries ents)
                    (Evaluation.evalEntriesPaired (quoteEntries ents) g [] vals fu2 hee2)
                    ((lookupSortAny l vals).symm.trans
                      (Eq.mpr
                        (congrArg (fun (z : List (String × Value)) => List.lookup l z = some w)
                          (Value.«section».inj (pair_value_eq h42)))
                        hlook))
                    ((lookupQuote l ents).trans (congrArg (Option.map quote) hlook))

/-- `agreeFields` carries the agreement across one aligned field list.
`reduce_fields` at lib/finite_term.ml lines 211 to 218 reduces each field at the fiber of its label, and
`evaluate_entries` at lines 261 to 266 runs the same fields. docs/metatheory.md line 385 states the field agreement of the section arm.
-/
theorem agreeFields (step : Nat → Term → Ty → Res (Term × Nat))
    (hstep : ∀ (fr : Nat) (tm : Term) (b : Ty) (x : Term) (r2 fe : Nat) (w : Value) (re : Nat),
      step fr tm b = Except.ok (x, r2) → evaluate fe [] tm = Except.ok (w, re) → Agrees x w) :
    ∀ (fields : List (String × Ty × Term)) (values : List (String × Value)) (fr : Nat)
      (out : List (String × Term)) (r : Nat),
      reduceFields step fr fields = Except.ok (out, r) →
      Evaluation.Paired [] values
          (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) fields) →
        out = quoteEntries values
          ∧ ∃ (f rest : Nat), evaluateEntries f [] out = Except.ok (values, rest)
  | [], values, _fr, _out, _r, hred, hp =>
      match (Evaluation.pairedNil [] values [] hp rfl).symm with
      | rfl =>
          ⟨(pair_value_eq hred).symm,
            0, 0,
            Eq.mp
              (congrArg
                (fun (z : List (String × Term)) =>
                  evaluateEntries 0 [] z = Except.ok (([] : List (String × Value)), 0))
                (pair_value_eq hred))
              rfl⟩
  | (label, fiber, tm) :: rest, values, fr, _out, _r, hred, hp =>
      match Evaluation.pairedCons [] values
          ((label, tm) :: List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) rest) hp label tm
          (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) rest) rfl with
      | ⟨v0, vs, f0, r0, hvalues, hev, htail⟩ =>
          match hvalues.symm with
          | rfl =>
              match res_bind_ok hred with
              | ⟨head, hhead, h2⟩ =>
                  match head, hhead, h2 with
                  | (hx, hfuel), hhead2, h22 =>
                      match res_bind_ok h22 with
                      | ⟨tl, htl, h3⟩ =>
                          match tl, htl, h3 with
                          | (touts, tfuel), htl2, h32 =>
                              match hstep fr tm fiber hx hfuel f0 v0 r0 hhead2 hev,
                                  agreeFields step hstep rest vs hfuel touts tfuel htl2 htail with
                              | ⟨hq, fh, rh, hevh⟩, ⟨htouts, ft, rt, hevt⟩ =>
                                  ⟨(pair_value_eq h32).symm.trans
                                      ((congrArg (fun (z : Term) => (label, z) :: touts) hq).trans
                                        (congrArg
                                          (fun (z : List (String × Term)) =>
                                            (label, quote v0) :: z)
                                          htouts)),
                                    fh + ft, rt + rh,
                                    Eq.mp
                                      (congrArg
                                        (fun (z : List (String × Term)) =>
                                          evaluateEntries (fh + ft) [] z
                                            = Except.ok ((label, v0) :: vs, rt + rh))
                                        (pair_value_eq h32))
                                      (entriesGlue label hx v0 touts vs fh rh ft rt hevh hevt)⟩

/-- `canonSorted` reads the sorted list out of one successful `canonicalEntries`.
`canonicalEntries` mirrors lib/finite_term.ml lines 20 to 23 and returns the sort of its own input, which docs/metatheory.md lines 23 and 24 name.
-/
theorem canonSorted {α : Type} (entries sorted : List (String × α))
    (h : canonicalEntries entries = Except.ok sorted) : sortEntries entries = sorted :=
  match res_bind_ok h with
  | ⟨_u, _hu, hs⟩ => Except.ok.inj hs

/-- `projFieldAgree` closes the projection arm at one section value.
The reduced section holds the quoted field list, so the read of lib/finite_term.ml line 206 returns the quote of the value that the read of lines 257 to 259 returns. docs/metatheory.md lines 383 to 386 state that agreement.
-/
theorem projFieldAgree (ents : List (String × Value)) (label : String) (found : Term) (w : Value)
    (hagr : Agrees (Term.«section» (quoteEntries ents)) (Value.«section» ents))
    (hfound : lookup label (quoteEntries ents) = Except.ok found)
    (hw : lookup label ents = Except.ok w) : Agrees found w :=
  let hlookw : List.lookup label ents = some w := NormTyping.lookupSome label ents w hw
  let hq : found = quote w :=
    Option.some.inj
      ((NormTyping.lookupSome label (quoteEntries ents) found hfound).symm.trans
        ((lookupQuote label ents).trans (congrArg (Option.map quote) hlookw)))
  ⟨hq,
    match hagr.2 with
    | ⟨f, rest, hsec⟩ =>
        match fieldRound ents label w f rest hsec hlookw with
        | ⟨f2, r3, hev⟩ =>
            ⟨f2, r3,
              Eq.mp
                (congrArg (fun (z : Term) => evaluate f2 [] z = Except.ok (w, r3)) hq.symm)
                hev⟩⟩

/-- `AgreeGas` states row Theorem6-11.5 of the stage brief at one gas value of `reduce`.
The reduced term of one closed run agrees with the value of the evaluated run, per docs/metatheory.md lines 383 to 386. The environment is empty, since `run` at lib/finite_term.ml lines 268 to 270 starts there and the closed setting of docs/metatheory.md lines 368 to 372 keeps it empty.
-/
def AgreeGas (gas : Nat) : Prop :=
  ∀ (fr : Nat) (t : Term) (a : Ty) (x : Term) (r2 fe : Nat) (v : Value) (re : Nat),
    reduce gas fr t a = Except.ok (x, r2) →
      evaluate fe [] t = Except.ok (v, re) → Agrees x v

/-- `sectionAgree` closes the section arm at one aligned field list.
`reduce` sorts the entries at lib/finite_term.ml lines 197 to 203 and the evaluator sorts the field values at line 245, so both sides hold the canonical order of lines 20 to 23. docs/metatheory.md lines 383 to 386 state the field agreement.
-/
theorem sectionAgree (gasPred : Nat) (ihp : AgreeGas gasPred)
    (entries : List (String × Term)) (fibers : List (String × Ty))
    (sorted : List (String × Term)) (fields : List (String × Ty × Term))
    (out : List (String × Term)) (values : List (String × Value)) (fu fv ro rv : Nat)
    (hcanon : canonicalEntries entries = Except.ok sorted)
    (halign : align fibers sorted = Except.ok fields)
    (hrf : reduceFields (fun (f : Nat) (z : Term) (b : Ty) => reduce gasPred f z b) fu fields
      = Except.ok (out, ro))
    (hee : evaluateEntries fv [] entries = Except.ok (values, rv)) :
    Agrees (Term.«section» out) (Value.«section» (sortEntries values)) :=
  let base : Evaluation.Paired [] values entries :=
    Evaluation.evalEntriesPaired entries fv [] values rv hee
  let hterms : List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) fields
      = sortEntries entries :=
    (NormTyping.alignParts fibers sorted fields halign).2.trans
      (canonSorted entries sorted hcanon).symm
  let hpaired : Evaluation.Paired [] (sortEntries values)
      (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) fields) :=
    Eq.mp
      (congrArg
        (fun (z : List (String × Term)) => Evaluation.Paired [] (sortEntries values) z)
        hterms.symm)
      (Evaluation.pairedSort [] values entries base)
  match agreeFields (fun (f : Nat) (z : Term) (b : Ty) => reduce gasPred f z b)
      (fun (fr2 : Nat) (tm : Term) (b : Ty) (x2 : Term) (r3 fe2 : Nat) (w : Value) (re2 : Nat)
          (hs : reduce gasPred fr2 tm b = Except.ok (x2, r3))
          (he : evaluate fe2 [] tm = Except.ok (w, re2)) => ihp fr2 tm b x2 r3 fe2 w re2 hs he)
      fields (sortEntries values) fu out ro hrf hpaired with
  | ⟨hq, f2, r3, hev⟩ =>
      let hlabels : List.map Prod.fst out = List.map Prod.fst (sortEntries values) :=
        (congrArg (List.map Prod.fst) hq).trans (quoteLabels (sortEntries values))
      let hsortOut : sortEntries out = out :=
        sortFix out (Eq.mpr (congrArg Ty.SortedLabels hlabels) (sortSorted values))
      let hlv : List.map Prod.fst (sortEntries values)
          = List.map Prod.fst (sortEntries entries) :=
        (mapSort values).trans
          ((congrArg sortLabels (pairedLabels [] values entries base)).trans
            (mapSort entries).symm)
      ⟨congrArg (fun (z : List (String × Term)) => Term.«section» z) hq,
        f2 + 1, r3,
        sectionMk out (sortEntries values) f2 r3
          (Eq.mpr
            (congrArg (fun (z : List String) => unique z = Except.ok ())
              ((congrArg (List.map Prod.fst) hsortOut).trans hlabels))
            (Eq.mpr
              (congrArg (fun (z : List String) => unique z = Except.ok ()) hlv)
              (canonUnique entries sorted hcanon)))
          (sortIdem values) hev⟩

/-- `redexAgree` closes the case redex of lib/finite_term.ml lines 187 to 190.
The reducer substitutes the reduced payload into the branch body and the evaluator extends the environment with the payload value, so Theorem5 at `d = 0` matches the two steps, as docs/metatheory.md lines 386 to 389 state.
-/
theorem redexAgree (gasPred : Nat) (ihp : AgreeGas gasPred)
    (branches sorted : List (String × Term)) (lbl : String) (pay : Value)
    (payTerm body opened x : Term) (rf0 ropen er r2 re : Nat) (a : Ty) (v : Value)
    (hcanon : canonicalEntries branches = Except.ok sorted)
    (hpay : ∃ (f2 r3 : Nat), evaluate f2 [] payTerm = Except.ok (pay, r3))
    (hbody : lookup lbl sorted = Except.ok body)
    (hsub : substituteCore rf0 payTerm body = Except.ok (opened, ropen))
    (hstep : reduce gasPred ropen opened a = Except.ok (x, r2))
    (hbr : evaluateBranch er [] lbl pay branches = Except.ok (v, re)) : Agrees x v :=
  match branchLookup branches er [] lbl pay v re hbr with
  | ⟨body2, hlb, hevb⟩ =>
      let hbodyEq : body2 = body :=
        Option.some.inj
          (hlb.symm.trans
            ((lookupSortAny lbl branches).symm.trans
              (Eq.mp
                (congrArg (fun (z : List (String × Term)) => List.lookup lbl z = some body)
                  (canonSorted branches sorted hcanon).symm)
                (NormTyping.lookupSome lbl sorted body hbody))))
      match hpay with
      | ⟨f2, r3, hp⟩ =>
          match evaluate_sub_env 0 [] [] payTerm body opened rf0 ropen f2 r3 er re pay v
              rfl hsub hp
              (Eq.mp
                (congrArg (fun (z : Term) => evaluate er (pay :: []) z = Except.ok (v, re))
                  hbodyEq)
                hevb) with
          | ⟨f3, r4, hopen⟩ => ihp ropen opened a x r2 f3 v r4 hstep hopen

/-- One induction step compares successful reduction and evaluation of a closed term.
The case arm uses substitution agreement, while the projection arm reads a quoted field.
-/
theorem agreeGasStep (gasPred : Nat) (ihp : AgreeGas gasPred) : AgreeGas (gasPred + 1) :=
  fun _fr t a x r2 _fe v re hred heval =>
    match res_bind_ok hred with
    | ⟨gr, _htr, hr⟩ =>
        match t, hr, heval with
        | .var _index, _hr, he =>
            match res_bind_ok he with
            | ⟨_ge, _hte, he2⟩ => (varNil he2).elim
        | .atom name, hr, he =>
            match res_bind_ok he with
            | ⟨_ge, _hte, he2⟩ =>
                agreesCast (pair_value_eq hr) (pair_value_eq he2) (atomAgrees name)
        | .tag label payload, hr, he =>
            match a, hr with
            | .atoms .., hr => (res_error_ne_ok hr).elim
            | .ran .., hr => (res_error_ne_ok hr).elim
            | .lan _fibers, hr =>
                match res_bind_ok hr, res_bind_ok he with
                | ⟨fiber, _hfiber, hr2⟩, ⟨ge, _hte, he⟩ =>
                    match res_bind_ok hr2, res_bind_ok he with
                    | ⟨rp, hrp, hr3⟩, ⟨ep, hep, he2⟩ =>
                        agreesCast (pair_value_eq hr3) (pair_value_eq he2)
                          (tagAgrees label rp.1 ep.1
                            (ihp gr payload fiber rp.1 rp.2 ge ep.1 ep.2 hrp hep))
        | .«section» entries, hr, he =>
            match a, hr with
            | .atoms .., hr => (res_error_ne_ok hr).elim
            | .lan .., hr => (res_error_ne_ok hr).elim
            | .ran fibers, hr =>
                match res_bind_ok hr, res_bind_ok he with
                | ⟨sorted, hcanon, hr2⟩, ⟨ge, _hte, he⟩ =>
                    match res_bind_ok hr2, res_bind_ok he with
                    | ⟨fields, halign, hr3⟩, ⟨_esorted, _hecanon, he2⟩ =>
                        match res_bind_ok hr3, res_bind_ok he2 with
                        | ⟨outs, houts, hr4⟩, ⟨evs, hevs, he3⟩ =>
                            agreesCast (pair_value_eq hr4) (pair_value_eq he3)
                              (sectionAgree gasPred ihp entries fibers sorted fields outs.1 evs.1
                                gr ge outs.2 evs.2 hcanon halign houts hevs)
        | .«case» scrutinee st branches, hr, he =>
            match st, hr with
            | .atoms .., hr => (res_error_ne_ok hr).elim
            | .ran .., hr => (res_error_ne_ok hr).elim
            | .lan fibers, hr =>
                match res_bind_ok hr, res_bind_ok he with
                | ⟨sorted, hcanon, hr2⟩, ⟨ge, _hte, he⟩ =>
                    match res_bind_ok hr2, res_bind_ok he with
                    | ⟨rp, hrp, hr3⟩, ⟨ep, hep, he2⟩ =>
                        match ep, hep, he2 with
                        | (.atom _name, _er), _hep, he2 => (res_error_ne_ok he2).elim
                        | (.«section» _entries, _er), _hep, he2 => (res_error_ne_ok he2).elim
                        | (.tag label pay, er), hep, he2 =>
                            match rp, hrp, hr3 with
                            | (rt, rr), hrp, hr3 =>
                                match rt, ihp gr scrutinee (.lan fibers) rt rr ge (.tag label pay) er
                                    hrp hep, hr3 with
                                | _, ⟨rfl, fpay, rpay, hpay⟩, hr3 =>
                                    match res_bind_ok hr3 with
                                    | ⟨body, hbody, hr4⟩ =>
                                        match res_bind_ok hr4 with
                                        | ⟨opened, hopen, hr5⟩ =>
                                            redexAgree gasPred ihp branches sorted label pay
                                              (quote pay) body opened.1 x rr opened.2 er r2 re a v
                                              hcanon (tagPayload label (quote pay) fpay pay rpay hpay)
                                              hbody hopen hr5 he2
        | .project field sty label, hr, he =>
            match sty, hr with
            | .atoms .., hr => (res_error_ne_ok hr).elim
            | .lan .., hr => (res_error_ne_ok hr).elim
            | .ran fibers, hr =>
                match res_bind_ok hr, res_bind_ok he with
                | ⟨_actual, _hactual, hr2⟩, ⟨ge, _hte, he⟩ =>
                    ite_elim (P := fun z : Res (Term × Nat) =>
                        z = Except.ok (x, r2) → Agrees x v)
                      (fun _hc hr3 =>
                        match res_bind_ok hr3, res_bind_ok he with
                        | ⟨rp, hrp, hr4⟩, ⟨ep, hep, he2⟩ =>
                            match ep, hep, he2 with
                            | (.atom _name, _er), _hep, he2 => (res_error_ne_ok he2).elim
                            | (.tag _label _pay, _er), _hep, he2 => (res_error_ne_ok he2).elim
                            | (.«section» ents, er), hep, he2 =>
                                match rp, hrp, hr4 with
                                | (rt, rr), hrp, hr4 =>
                                    match rt, ihp gr field (.ran fibers) rt rr ge (.«section» ents) er
                                        hrp hep, hr4 with
                                    | _, ⟨rfl, fsec, rsec, hsec⟩, hr4 =>
                                        match res_bind_ok hr4, res_bind_ok he2 with
                                        | ⟨found, hfound, hr5⟩, ⟨w, hw, he3⟩ =>
                                            agreesCast (pair_value_eq hr5) (pair_value_eq he3)
                                              (projFieldAgree ents label found w
                                                ⟨rfl, fsec, rsec, hsec⟩ hfound hw))
                      (fun _hc hr3 => (res_error_ne_ok hr3).elim) hr2

/-- Successful reduction and evaluation agree at every structural gas value.
No typing assumption or relation between the two fuel budgets is required.
-/
theorem agreeGas : (gas : Nat) → AgreeGas gas
  | 0 => fun _fr _t _a _x _r2 _fe _v _re hr _he => (res_error_ne_ok hr).elim
  | gasPred + 1 => agreeGasStep gasPred (agreeGas gasPred)

end NormAgree

/-- Successful normalization and execution of one closed term return the same quoted value.
The two calls have independent budgets. This theorem does not assert successful termination.
-/
theorem normalize_agrees_with_run (normalFuel runFuel : Nat) (t x : Term) (a : Ty) (v : Value)
    (hn : normalize normalFuel [] t a = Except.ok x)
    (he : run runFuel t a = Except.ok v) : x = quote v :=
  match res_bind_ok hn, res_bind_ok he with
  | ⟨nr, _hcn, hn2⟩, ⟨er, _hce, he2⟩ =>
      match res_bind_ok hn2, res_bind_ok he2 with
      | ⟨nx, hnx, hn3⟩, ⟨ev, hev, he3⟩ =>
          (Except.ok.inj hn3).symm.trans
            ((NormAgree.agreeGas (nr + 1) nr t a nx.1 nx.2 er ev.1 ev.2 hnx hev).1.trans
              (congrArg quote (Except.ok.inj he3)))
