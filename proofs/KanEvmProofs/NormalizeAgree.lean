import KanEvmProofs.EvalSubst
import KanEvmProofs.NormalizeTyping
import KanEvmProofs.NormalizeCore

/-! # Agreement of the normalizer with the evaluator

This module supplies helper lemmas for row Theorem6-11.5, `normalize_agrees_with_run`.
The agreement theorem remains open and is not declared in this module.
Its intended statement relates `normalize` at lib/finite_term.ml lines 227 to 229 to `run` at lines 268 to 270, as docs/metatheory.md lines 368 to 402 describe.
Both runs will be hypotheses, so the intended theorem claims no successful fuel bound.

Row Theorem6-C7 of the theorem inventory states no theorem, and the row records the reason word for word.
The reason reads that claim C7 cannot be stated as a proved theorem for this fragment.
Claim C7 stays open.
A finite fuel bound for the agreement needs strong normalization, which docs/metatheory.md section 12 lists as open, and docs/validation.md records that gap.

That open obligation carries no axiom and no proof placeholder here. docs/metatheory.md lines 403 and 404 list weak normalization as open, so a fuel at which
`normalize` returns a value stays outside this mechanization.

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

end NormAgree
