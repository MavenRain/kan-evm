import KanEvmProofs.Budget
import KanEvmProofs.Canonical
import KanEvmProofs.Reduce
import KanEvmProofs.Substitution
import KanEvmProofs.Typing
import KanEvmProofs.Checker

/-! # Typing preservation of reduction

This module holds row Theorem6-11.3 of the stage brief, `reduce_preserves_type`. docs/metatheory.md lines 321 to 353 state the theorem and the eight cases of its proof.
`reduce` of Reduce.lean mirrors the OCaml `reduce` at lib/finite_term.ml lines 162 to 225.
The proof walks the gas of decision S2-D6, since every nested call of `reduce` drops one gas unit.
Each case inverts one typing rule of Typing.lean and it rebuilds that rule at the reduced term.
The case of a tag scrutinee reuses `substitution_zero` of Substitution.lean, per row Theorem3.
The two neutral cases rebuild a sorted entry list, which docs/metatheory.md lines 345 to 353 state.
Namespace `NormTyping` holds the helper lemmas, and the inventory name sits at the root.
-/

namespace NormTyping

/-- `transportType` moves one typing derivation along one term equality and one type equality.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem transportType (g : List Ty) (x y : Term) (b c : Ty) (hx : x = y) (hb : b = c)
    (typed : HasType g x b) : HasType g y c :=
  Eq.mp (congrArg (fun (z : Ty) => HasType g y z) hb)
    (Eq.mp (congrArg (fun (z : Term) => HasType g z b) hx) typed)

/-- `transportBranch` moves one branch derivation along one payload type and one body equality.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem transportBranch (g : List Ty) (b c : Ty) (x y : Term) (expected : Ty) (hb : b = c)
    (hx : x = y) (typed : HasType (b :: g) x expected) : HasType (c :: g) y expected :=
  Eq.mp (congrArg (fun (z : Ty) => HasType (z :: g) y expected) hb)
    (Eq.mp (congrArg (fun (z : Term) => HasType (b :: g) z expected) hx) typed)

/-- `compareSelf` names the reflexive law of the label comparison of Syntax.lean line 62.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem compareSelf (a : String) : compare a a = Ordering.eq := Std.ReflCmp.compare_self

/-- `compareEq` reads one label equality out of an equal comparison.
`align` at lib/finite_term.ml lines 51 to 60 takes the equal arm for one shared key.
-/
theorem compareEq (a b : String) (h : compare a b = Ordering.eq) : a = b :=
  Std.LawfulEqCmp.eq_of_compare h

/-- `labelLeSelf` states that one label precedes itself in the order of `labelLe`.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem labelLeSelf (a : String) : labelLe a a = true := congrArg Ordering.isLE (compareSelf a)

/-- `beqEq` reads one label equality out of the boolean test that `List.lookup` runs.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem beqEq (a b : String) (h : (a == b) = true) : a = b := eq_of_beq h

/-- `ordCases` proves one property of the three way comparison of `align`, arm after arm.
Each arm carries the equation that names the comparison, so the equal arm keeps the key equality.
`align` of Check.lean mirrors lib/finite_term.ml lines 51 to 60.
-/
theorem ordCases {α : Type} {x1 x2 x3 : α} {P : Ordering → α → Prop}
    (hlt : P Ordering.lt x1) (heq : P Ordering.eq x2) (hgt : P Ordering.gt x3) :
    (o : Ordering) → P o (match o with | .lt => x1 | .gt => x3 | .eq => x2)
  | .lt => hlt
  | .gt => hgt
  | .eq => heq

/-- `lookupSome` reads the option form out of one successful `lookup` of Check.lean.
`lookup` mirrors the association list read at lib/finite_term.ml lines 40 and 41.
-/
theorem lookupSome {α : Type} (l : String) (entries : List (String × α)) (v : α)
    (h : lookup l entries = Except.ok v) : List.lookup l entries = some v :=
  Option.rec (motive := fun (o : Option α) =>
      o.elim (Except.error (Err.unexpectedLabel l)) Except.ok = Except.ok v → o = some v)
    (fun herr => (res_error_ne_ok herr).elim)
    (fun _w hok => congrArg some (Except.ok.inj hok))
    (List.lookup l entries) h

/-- `lookupIte` names the step of `List.lookup` over one entry list as one test.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem lookupIte {α : Type} (l k : String) (v : α) (entries : List (String × α)) :
    List.lookup l ((k, v) :: entries)
      = if (l == k) = true then some v else List.lookup l entries :=
  cond_eq_ite (l == k) (some v) (List.lookup l entries)

/-- `lookupInsert` states that one insertion step of the sort keeps every read of `List.lookup`.
`insertEntry` of Check.lean mirrors the stable insertion of lib/finite_term.ml line 26.
The moved entry passes an entry with a smaller label, and that label differs from the key it holds.
-/
theorem lookupInsert (l key : String) (value : Term) :
    (entries : List (String × Term)) →
      List.lookup l (insertEntry (key, value) entries)
        = List.lookup l ((key, value) :: entries)
  | [] => rfl
  | (k2, v2) :: rest =>
      ite_elim
        (P := fun (z : List (String × Term)) =>
          List.lookup l z = List.lookup l ((key, value) :: (k2, v2) :: rest))
        (fun hyes => Canon.hold_first rfl hyes)
        (fun hc =>
          (lookupIte l k2 v2 (insertEntry (key, value) rest)).trans
            (ite_elim
              (P := fun (z : Option Term) =>
                z = List.lookup l ((key, value) :: (k2, v2) :: rest))
              (fun hh =>
                ((lookupIte l key value ((k2, v2) :: rest)).trans
                  ((if_neg (fun (hk : (l == key) = true) =>
                      hc (Eq.mp
                        (congrArg (fun (z : String) => labelLe key z = true)
                          ((beqEq l key hk).symm.trans (beqEq l k2 hh)))
                        (labelLeSelf key)))).trans
                    ((lookupIte l k2 v2 rest).trans (if_pos hh)))).symm)
              (fun hh =>
                ((lookupInsert l key value rest).trans (lookupIte l key value rest)).trans
                  ((lookupIte l key value ((k2, v2) :: rest)).trans
                    (congrArg
                      (fun (z : Option Term) => if (l == key) = true then some value else z)
                      ((lookupIte l k2 v2 rest).trans (if_neg hh)))).symm)))

/-- `lookupSort` states that the sort of Check.lean keeps every read of `List.lookup`.
The sort is stable, so the first entry of one label stays the first entry of that label.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem lookupSort (l : String) :
    (entries : List (String × Term)) →
      List.lookup l (sortEntries entries) = List.lookup l entries
  | [] => rfl
  | (k, v) :: rest =>
      (lookupInsert l k v (sortEntries rest)).trans
        ((lookupIte l k v (sortEntries rest)).trans
          ((congrArg (fun (z : Option Term) => if (l == k) = true then some v else z)
              (lookupSort l rest)).trans
            (lookupIte l k v rest).symm))

/-- `labelsFirst` states that the fiber view of one aligned triple list keeps every label.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem labelsFirst :
    (pairs : List (String × Ty × Term)) →
      List.map Prod.fst (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) pairs)
        = List.map Prod.fst pairs
  | [] => rfl
  | head :: rest => congrArg (fun (z : List String) => head.1 :: z) (labelsFirst rest)

/-- `labelsSecond` states that the term view of one aligned triple list keeps every label.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem labelsSecond :
    (pairs : List (String × Ty × Term)) →
      List.map Prod.fst (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) pairs)
        = List.map Prod.fst pairs
  | [] => rfl
  | head :: rest => congrArg (fun (z : List String) => head.1 :: z) (labelsSecond rest)

/-- `mapInsertEntry` moves the label view across one insertion step of the sort of Check.lean.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem mapInsertEntry (key : String) (value : Term) :
    (entries : List (String × Term)) →
      List.map Prod.fst (insertEntry (key, value) entries)
        = insertLabel key (List.map Prod.fst entries)
  | [] => rfl
  | (k2, _v2) :: rest =>
      ite_elim
        (P := fun (z : List (String × Term)) =>
          List.map Prod.fst z = insertLabel key (k2 :: List.map Prod.fst rest))
        (fun hc => (if_pos hc).symm)
        (fun hc =>
          (congrArg (fun (z : List String) => k2 :: z) (mapInsertEntry key value rest)).trans
            (if_neg hc).symm)

/-- `mapSortEntries` moves the label view across the whole sort of Check.lean.
It is the entry list partner of `Canon.map_sortFibers` of Canonical.lean.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem mapSortEntries :
    (entries : List (String × Term)) →
      List.map Prod.fst (sortEntries entries) = sortLabels (List.map Prod.fst entries)
  | [] => rfl
  | (k, v) :: rest =>
      (mapInsertEntry k v (sortEntries rest)).trans
        (congrArg (insertLabel k) (mapSortEntries rest))

/-- `insertFix` states that the insertion step puts one small label at the front of the list.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem insertFix (key : String) (value : Term) :
    (entries : List (String × Term)) →
      Canon.LeHead key (List.map Prod.fst entries) →
      insertEntry (key, value) entries = (key, value) :: entries
  | [], h => Canon.hold_first rfl h
  | (k2, _v2) :: _rest, h => if_pos (h : labelLe key k2 = true)

/-- `sortFix` states that the sort keeps one list that already holds the ascending label order.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem sortFix :
    (entries : List (String × Term)) →
      Ty.SortedLabels (List.map Prod.fst entries) → sortEntries entries = entries
  | [], h => Canon.hold_first rfl h
  | (k, v) :: rest, h =>
      (congrArg (insertEntry (k, v))
          (sortFix rest (Canon.sortedLabels_uncons k (List.map Prod.fst rest) h).2)).trans
        (insertFix k v rest (Canon.sortedLabels_uncons k (List.map Prod.fst rest) h).1)

/-- `uniqueOf` reads the distinctness test out of one successful `canonicalEntries`.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem uniqueOf (entries sorted : List (String × Term))
    (h : canonicalEntries entries = Except.ok sorted) :
    unique (List.map Prod.fst sorted) = Except.ok () :=
  match res_bind_ok h with
  | ⟨_u, hu, hs⟩ =>
      Eq.mp
        (congrArg
          (fun (z : List (String × Term)) => unique (List.map Prod.fst z) = Except.ok ())
          (Except.ok.inj hs))
        hu

/-- `sortedOf` reads the ascending label order out of one successful `canonicalEntries`.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem sortedOf (entries sorted : List (String × Term))
    (h : canonicalEntries entries = Except.ok sorted) :
    Ty.SortedLabels (List.map Prod.fst sorted) :=
  Eq.mpr
    (congrArg Ty.SortedLabels
      ((congrArg (List.map Prod.fst) (canonical_sorted entries sorted h)).trans
        (mapSortEntries entries)))
    (Canon.sortLabels_sorted (List.map Prod.fst entries))

/-- `canonFix` states that `canonicalEntries` keeps one list that already holds the canonical form.
`canonicalEntries` of Check.lean mirrors `canonical` at lib/finite_term.ml lines 20 to 23.
The reduced entry list of a section holds the label sequence of the checked list, so it is canonical.
-/
theorem canonFix (out : List (String × Term))
    (hs : Ty.SortedLabels (List.map Prod.fst out))
    (hu : unique (List.map Prod.fst out) = Except.ok ()) :
    canonicalEntries out = Except.ok out :=
  (congrArg
      (fun (z : List (String × Term)) =>
        unique (List.map Prod.fst z)
          >>= Function.const Unit (Except.ok z : Res (List (String × Term))))
      (sortFix out hs)).trans
    (congrArg
      (fun (r : Res Unit) =>
        r >>= Function.const Unit (Except.ok out : Res (List (String × Term))))
      hu)

/-- `alignSelf` names the successful step of `align` for one shared key.
`align` of Check.lean mirrors lib/finite_term.ml lines 51 to 60, which reads the labels alone.
-/
theorem alignSelf (key : String) (fiber : Ty) (types : List (String × Ty)) (field : Term)
    (terms : List (String × Term)) :
    align ((key, fiber) :: types) ((key, field) :: terms)
      = (align types terms >>= fun (r : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, field) :: r)) :=
  ordCases
    (P := fun (o : Ordering) (r : Res (List (String × Ty × Term))) =>
      compare key key = o →
        r = (align types terms >>= fun (z : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, field) :: z)))
    (fun ho => Ordering.noConfusion ((compareSelf key).symm.trans ho))
    (fun ho => Canon.hold_first rfl ho)
    (fun ho => Ordering.noConfusion ((compareSelf key).symm.trans ho))
    (compare key key) rfl

/-- `alignParts` reads the two views of the aligned triple list out of one successful `align`.
The fiber view returns the fiber list, and the term view returns the sorted entry list. docs/metatheory.md lines 53 to 59 state that key alignment.
-/
theorem alignParts :
    (fibers : List (String × Ty)) → (terms : List (String × Term)) →
      (pairs : List (String × Ty × Term)) → align fibers terms = Except.ok pairs →
      List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) pairs = fibers
        ∧ List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) pairs = terms
  | [], [], pairs, h =>
      match (Except.ok.inj h : ([] : List (String × Ty × Term)) = pairs) with
      | rfl => ⟨rfl, rfl⟩
  | .cons .., [], _pairs, h => (res_error_ne_ok h).elim
  | [], .cons .., _pairs, h => (res_error_ne_ok h).elim
  | (key, fiber) :: types, (label, field) :: terms, pairs, h =>
      ordCases
        (P := fun (o : Ordering) (r : Res (List (String × Ty × Term))) =>
          compare key label = o →
            (ps : List (String × Ty × Term)) → r = Except.ok ps →
              List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) ps = (key, fiber) :: types
                ∧ List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) ps
                  = (label, field) :: terms)
        (fun ho _ps hps => Canon.hold_first (res_error_ne_ok hps).elim ho)
        (fun ho _ps hps =>
          match res_bind_ok hps with
          | ⟨r0, hr0, hcons⟩ =>
              match (Except.ok.inj hcons : (key, fiber, field) :: r0 = _ps) with
              | rfl =>
                  ⟨congrArg (fun (z : List (String × Ty)) => (key, fiber) :: z)
                      (alignParts types terms r0 hr0).1,
                    (congrArg (fun (z : List (String × Term)) => (key, field) :: z)
                        (alignParts types terms r0 hr0).2).trans
                      (congrArg (fun (z : String) => (z, field) :: terms)
                        (compareEq key label ho))⟩)
        (fun ho _ps hps => Canon.hold_first (res_error_ne_ok hps).elim ho)
        (compare key label) rfl pairs h

/-- `entriesUncons` splits the entry judgement of a section at its first field.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem entriesUncons (g : List Ty) (label : String) (fiber : Ty) (value : Term)
    (rest : List (String × Ty × Term))
    (h : HasTypeEntries g ((label, fiber, value) :: rest) Option.none) :
    HasType g value fiber ∧ HasTypeEntries g rest Option.none :=
  match h with
  | .field _ctx _label _fiber _field _rest htype hrest => ⟨htype, hrest⟩

/-- `branchesUncons` splits the entry judgement of a case node at its first branch.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem branchesUncons (g : List Ty) (label : String) (fiber : Ty) (body : Term)
    (rest : List (String × Ty × Term)) (expected : Ty)
    (h : HasTypeEntries g ((label, fiber, body) :: rest) (Option.some expected)) :
    HasType (fiber :: g) body expected ∧ HasTypeEntries g rest (Option.some expected) :=
  match h with
  | .branch _ctx _label _payloadType _body _rest _expected htype hrest => ⟨htype, hrest⟩

/-- `tagInv` inverts the tag rule at one reduced tag term.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem tagInv (g : List Ty) (label : String) (payload : Term) (fibers : List (String × Ty))
    (h : HasType g (Term.tag label payload) (Ty.lan fibers)) :
    ∃ (fiber : Ty), lookup label fibers = Except.ok fiber ∧ HasType g payload fiber :=
  match h with
  | .tag _ctx _label _payload _fibers fiber hlookup hpayload => ⟨fiber, hlookup, hpayload⟩

/-- `sectionInv` inverts the section rule at one reduced section term.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem sectionInv (g : List Ty) (entries : List (String × Term)) (fibers : List (String × Ty))
    (h : HasType g (Term.«section» entries) (Ty.ran fibers)) :
    ∃ (sorted : List (String × Term)) (pairs : List (String × Ty × Term)),
      canonicalEntries entries = Except.ok sorted ∧ align fibers sorted = Except.ok pairs
        ∧ HasTypeEntries g pairs Option.none :=
  match h with
  | .«section» _ctx _entries _fibers sorted pairs hcanon halign hentries =>
      ⟨sorted, pairs, hcanon, halign, hentries⟩

/-- `noneNotSome` rejects a lookup that reports a hit in an empty list.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem noneNotSome {α : Type} {p : Prop} {v : α}
    (h : (Option.none : Option α) = Option.some v) : p :=
  nomatch h

/-- `fieldAt` reads the type of one field out of the entry judgement of a section.
`align` pairs each fiber with the field of one label, per lib/finite_term.ml lines 51 to 60, so one label reads one type and one field out of the same aligned list.
-/
theorem fieldAt (g : List Ty) (label : String) (fiber : Ty) (value : Term) :
    (pairs : List (String × Ty × Term)) → HasTypeEntries g pairs Option.none →
      List.lookup label (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) pairs)
        = some fiber →
      List.lookup label (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) pairs)
        = some value →
      HasType g value fiber
  | [], _hentries, hfib, hval => Canon.hold_first (noneNotSome hfib) hval
  | (k, fb, v) :: rest, hentries, hfib, hval =>
      if hc : (label == k) = true then
        transportType g v value fb fiber
          (Option.some.inj
            ((if_pos hc).symm.trans
              ((lookupIte label k v
                (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) rest)).symm.trans hval)))
          (Option.some.inj
            ((if_pos hc).symm.trans
              ((lookupIte label k fb
                (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) rest)).symm.trans hfib)))
          (entriesUncons g k fb v rest hentries).1
      else
        fieldAt g label fiber value rest (entriesUncons g k fb v rest hentries).2
          ((if_neg hc).symm.trans
            ((lookupIte label k fb
              (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) rest)).symm.trans hfib))
          ((if_neg hc).symm.trans
            ((lookupIte label k v
              (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) rest)).symm.trans hval))

/-- `branchAt` reads the judgement of one branch out of the entry judgement of a case node.
Each branch body runs under the fiber of its label, per lib/finite_term.ml lines 92 and 93.
-/
theorem branchAt (g : List Ty) (label : String) (fiber : Ty) (body : Term) (expected : Ty) :
    (pairs : List (String × Ty × Term)) → HasTypeEntries g pairs (Option.some expected) →
      List.lookup label (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) pairs)
        = some fiber →
      List.lookup label (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) pairs)
        = some body →
      HasType (fiber :: g) body expected
  | [], _hentries, hfib, hval => Canon.hold_first (noneNotSome hfib) hval
  | (k, fb, v) :: rest, hentries, hfib, hval =>
      if hc : (label == k) = true then
        transportBranch g fb fiber v body expected
          (Option.some.inj
            ((if_pos hc).symm.trans
              ((lookupIte label k fb
                (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) rest)).symm.trans hfib)))
          (Option.some.inj
            ((if_pos hc).symm.trans
              ((lookupIte label k v
                (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) rest)).symm.trans hval)))
          (branchesUncons g k fb v rest expected hentries).1
      else
        branchAt g label fiber body expected rest
          (branchesUncons g k fb v rest expected hentries).2
          ((if_neg hc).symm.trans
            ((lookupIte label k fb
              (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) rest)).symm.trans hfib))
          ((if_neg hc).symm.trans
            ((lookupIte label k v
              (List.map (fun (p : String × Ty × Term) => (p.1, p.2.2)) rest)).symm.trans hval))


/-- `Rebuilt` names the conclusion of the two list rebuild lemmas below.
It states that the reduced entry list aligns against the fiber list of the input triples, that the aligned result carries the entry judgement, and that the label order is the input order.
It names one conclusion of this module, so it mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
def Rebuilt (g : List Ty) (mode : Option Ty) (pairs : List (String × Ty × Term))
    (out : List (String × Term)) : Prop :=
  ∃ pairs2 : List (String × Ty × Term),
    align (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) pairs) out = Except.ok pairs2
      ∧ HasTypeEntries g pairs2 mode
      ∧ List.map Prod.fst out = List.map Prod.fst pairs

/-- `fieldsRebuild` types the field list that `reduceFields` returns for a section node.
The walk of lib/finite_term.ml lines 211 to 216 keeps the label of each field, so the reduced list aligns against the same fiber list and it carries the entry judgement of the input.
-/
theorem fieldsRebuild (g : List Ty) (gasPred : Nat)
    (ih : (ctx : List Ty) → (f : Nat) → (x x' : Term) → (b : Ty) → (r : Nat) →
      HasType ctx x b → reduce gasPred f x b = Except.ok (x', r) → HasType ctx x' b) :
    (pairs : List (String × Ty × Term)) → (fuel : Nat) → (out : List (String × Term)) →
      (rest : Nat) → HasTypeEntries g pairs Option.none →
      reduceFields (fun f x a => reduce gasPred f x a) fuel pairs = Except.ok (out, rest) →
      Rebuilt g Option.none pairs out
  | [], _fuel, out, _rest, hentries, h =>
      Eq.mp
        (congrArg (Rebuilt g Option.none ([] : List (String × Ty × Term)))
          (congrArg Prod.fst (Except.ok.inj h) : ([] : List (String × Term)) = out))
        ⟨[], rfl, Canon.hold_first (HasTypeEntries.nil g Option.none) hentries, rfl⟩
  | (label, fiber, value) :: rest0, fuel, out, _rest, hentries, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              match fieldsRebuild g gasPred ih rest0 head.2 tail.1 tail.2
                  (entriesUncons g label fiber value rest0 hentries).2 htail with
              | ⟨pairs2, halign, hentries2, hlabels⟩ =>
                  Eq.mp
                    (congrArg (Rebuilt g Option.none ((label, fiber, value) :: rest0))
                      (congrArg Prod.fst (Except.ok.inj h3)
                        : (label, head.1) :: tail.1 = out))
                    ⟨(label, fiber, head.1) :: pairs2,
                      (alignSelf label fiber
                          (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) rest0)
                          head.1 tail.1).trans (res_bind_mk halign rfl),
                      HasTypeEntries.field g label fiber head.1 pairs2
                        (ih g fuel value head.1 fiber head.2
                          (entriesUncons g label fiber value rest0 hentries).1 hhead)
                        hentries2,
                      congrArg (fun (z : List String) => label :: z) hlabels⟩

/-- `branchesRebuild` types the branch list that `reduceBranches` returns for a neutral case node.
The walk of lib/finite_term.ml lines 219 to 225 keeps the label of each branch and it reduces each body at the expected type of the whole node, under the fiber of its own label.
-/
theorem branchesRebuild (g : List Ty) (gasPred : Nat) (expected : Ty)
    (ih : (ctx : List Ty) → (f : Nat) → (x x' : Term) → (b : Ty) → (r : Nat) →
      HasType ctx x b → reduce gasPred f x b = Except.ok (x', r) → HasType ctx x' b) :
    (pairs : List (String × Ty × Term)) → (fuel : Nat) → (out : List (String × Term)) →
      (rest : Nat) → HasTypeEntries g pairs (Option.some expected) →
      reduceBranches (fun f x a => reduce gasPred f x a) fuel pairs expected
          = Except.ok (out, rest) →
      Rebuilt g (Option.some expected) pairs out
  | [], _fuel, out, _rest, hentries, h =>
      Eq.mp
        (congrArg (Rebuilt g (Option.some expected) ([] : List (String × Ty × Term)))
          (congrArg Prod.fst (Except.ok.inj h) : ([] : List (String × Term)) = out))
        ⟨[], rfl, Canon.hold_first (HasTypeEntries.nil g (Option.some expected)) hentries, rfl⟩
  | (label, fiber, body) :: rest0, fuel, out, _rest, hentries, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              match branchesRebuild g gasPred expected ih rest0 head.2 tail.1 tail.2
                  (branchesUncons g label fiber body rest0 expected hentries).2 htail with
              | ⟨pairs2, halign, hentries2, hlabels⟩ =>
                  Eq.mp
                    (congrArg (Rebuilt g (Option.some expected) ((label, fiber, body) :: rest0))
                      (congrArg Prod.fst (Except.ok.inj h3)
                        : (label, head.1) :: tail.1 = out))
                    ⟨(label, fiber, head.1) :: pairs2,
                      (alignSelf label fiber
                          (List.map (fun (p : String × Ty × Term) => (p.1, p.2.1)) rest0)
                          head.1 tail.1).trans (res_bind_mk halign rfl),
                      HasTypeEntries.branch g label fiber head.1 pairs2 expected
                        (ih (fiber :: g) fuel body head.1 expected head.2
                          (branchesUncons g label fiber body rest0 expected hentries).1 hhead)
                        hentries2,
                      congrArg (fun (z : List String) => label :: z) hlabels⟩

/-- `neutralCase` types the rebuilt case node of a neutral scrutinee. lib/finite_term.ml lines 191 to 208 keep the node and they reduce every branch body.
The reduced branch list holds the labels of the sorted branch list, so it is canonical already, and it aligns against the same fiber list, which rebuilds the case rule of
Typing.lean.
-/
theorem neutralCase (g : List Ty) (gasPred : Nat) (fibers : List (String × Ty))
    (branches sorted : List (String × Term)) (pairs : List (String × Ty × Term)) (expected : Ty)
    (ih : (ctx : List Ty) → (f : Nat) → (x x' : Term) → (b : Ty) → (r : Nat) →
      HasType ctx x b → reduce gasPred f x b = Except.ok (x', r) → HasType ctx x' b)
    (hcanon : canonicalEntries branches = Except.ok sorted)
    (halign : align fibers sorted = Except.ok pairs)
    (hentries : HasTypeEntries g pairs (Option.some expected))
    (u : Term) (fuel : Nat) (t' : Term) (rest : Nat) (scrut : HasType g u (Ty.lan fibers))
    (h : (align fibers sorted >>= fun (fields : List (String × Ty × Term)) =>
            reduceBranches (fun f x a => reduce gasPred f x a) fuel fields expected
              >>= fun (r : List (String × Term) × Nat) =>
                Except.ok (Term.«case» u (Ty.lan fibers) r.1, r.2))
          = Except.ok (t', rest)) :
    HasType g t' expected :=
  match res_bind_ok h with
  | ⟨fields, hal2, h2⟩ =>
      match res_bind_ok h2 with
      | ⟨r, hrb, h3⟩ =>
          match branchesRebuild g gasPred expected ih pairs fuel r.1 r.2 hentries
              (Eq.mpr
                (congrArg
                  (fun (z : List (String × Ty × Term)) =>
                    reduceBranches (fun f x a => reduce gasPred f x a) fuel z expected
                      = Except.ok r)
                  (Except.ok.inj (halign.symm.trans hal2) : pairs = fields))
                hrb) with
          | ⟨pairs2, halign2, hentries2, hlabels⟩ =>
              Eq.mp
                (congrArg (fun (z : Term) => HasType g z expected)
                  (congrArg Prod.fst (Except.ok.inj h3)
                    : Term.«case» u (Ty.lan fibers) r.1 = t'))
                (HasType.«case» g u fibers r.1 r.1 pairs2 expected
                  (canonFix r.1
                    (Eq.mpr
                      (congrArg Ty.SortedLabels
                        (hlabels.trans
                          ((labelsSecond pairs).symm.trans
                            (congrArg (List.map Prod.fst)
                              (alignParts fibers sorted pairs halign).2))))
                      (sortedOf branches sorted hcanon))
                    (Eq.mpr
                      (congrArg (fun (z : List String) => unique z = Except.ok ())
                        (hlabels.trans
                          ((labelsSecond pairs).symm.trans
                            (congrArg (List.map Prod.fst)
                              (alignParts fibers sorted pairs halign).2))))
                      (uniqueOf branches sorted hcanon)))
                  (Eq.mp
                    (congrArg (fun (z : List (String × Ty)) => align z r.1 = Except.ok pairs2)
                      (alignParts fibers sorted pairs halign).1)
                    halign2)
                  scrut hentries2)

/-- `sectionCase` types the rebuilt section node of lib/finite_term.ml lines 178 to 183.
The walk keeps the label of each field, so the reduced entry list is canonical already and it aligns against the same fiber list, which rebuilds the section rule of
Typing.lean.
-/
theorem sectionCase (g : List Ty) (gasPred : Nat) (fibers : List (String × Ty))
    (entries sorted : List (String × Term)) (pairs : List (String × Ty × Term))
    (ih : (ctx : List Ty) → (f : Nat) → (x x' : Term) → (b : Ty) → (r : Nat) →
      HasType ctx x b → reduce gasPred f x b = Except.ok (x', r) → HasType ctx x' b)
    (hcanon : canonicalEntries entries = Except.ok sorted)
    (halign : align fibers sorted = Except.ok pairs)
    (hentries : HasTypeEntries g pairs Option.none)
    (fuel : Nat) (t' : Term) (rest : Nat)
    (h : (align fibers sorted >>= fun (fields : List (String × Ty × Term)) =>
            reduceFields (fun f x a => reduce gasPred f x a) fuel fields
              >>= fun (r : List (String × Term) × Nat) =>
                Except.ok (Term.«section» r.1, r.2))
          = Except.ok (t', rest)) :
    HasType g t' (Ty.ran fibers) :=
  match res_bind_ok h with
  | ⟨fields, hal2, h2⟩ =>
      match res_bind_ok h2 with
      | ⟨r, hrf, h3⟩ =>
          match fieldsRebuild g gasPred ih pairs fuel r.1 r.2 hentries
              (Eq.mpr
                (congrArg
                  (fun (z : List (String × Ty × Term)) =>
                    reduceFields (fun f x a => reduce gasPred f x a) fuel z = Except.ok r)
                  (Except.ok.inj (halign.symm.trans hal2) : pairs = fields))
                hrf) with
          | ⟨pairs2, halign2, hentries2, hlabels⟩ =>
              Eq.mp
                (congrArg (fun (z : Term) => HasType g z (Ty.ran fibers))
                  (congrArg Prod.fst (Except.ok.inj h3) : Term.«section» r.1 = t'))
                (HasType.«section» g r.1 fibers r.1 pairs2
                  (canonFix r.1
                    (Eq.mpr
                      (congrArg Ty.SortedLabels
                        (hlabels.trans
                          ((labelsSecond pairs).symm.trans
                            (congrArg (List.map Prod.fst)
                              (alignParts fibers sorted pairs halign).2))))
                      (sortedOf entries sorted hcanon))
                    (Eq.mpr
                      (congrArg (fun (z : List String) => unique z = Except.ok ())
                        (hlabels.trans
                          ((labelsSecond pairs).symm.trans
                            (congrArg (List.map Prod.fst)
                              (alignParts fibers sorted pairs halign).2))))
                      (uniqueOf entries sorted hcanon)))
                  (Eq.mp
                    (congrArg (fun (z : List (String × Ty)) => align z r.1 = Except.ok pairs2)
                      (alignParts fibers sorted pairs halign).1)
                    halign2)
                  hentries2)

/-- `preservesAt` states row Theorem6-11.3 of the stage brief at one gas value. docs/metatheory.md lines 321 to 353 state the theorem and its cases.
The recursion walks the gas of decision S2-D6, since every nested call of `reduce` drops one unit, and the case of a tag scrutinee reduces a substituted body, which is no subterm of the input.
The context is quantified at each step, since a branch body runs under the fiber of its label.
-/
theorem preservesAt :
    (gas : Nat) → (f : Nat) → (g : List Ty) → (t t' : Term) → (a : Ty) → (rest : Nat) →
      HasType g t a → reduce gas f t a = Except.ok (t', rest) → HasType g t' a
  | 0, _f, _g, _t, _t', _a, _rest, _typed, h => (res_error_ne_ok h).elim
  | gasPred + 1, _f, g, t, t', a, rest, typed, h =>
      match res_bind_ok h with
      | ⟨f2, _htick, hb⟩ =>
          match typed, hb with
          | .var ctx index b hvar, hb2 =>
              Eq.mp
                (congrArg (fun (z : Term) => HasType ctx z b)
                  (congrArg Prod.fst (Except.ok.inj hb2) : Term.var index = t'))
                (HasType.var ctx index b hvar)
          | .atom ctx name labels hmem, hb2 =>
              Eq.mp
                (congrArg (fun (z : Term) => HasType ctx z (Ty.atoms labels))
                  (congrArg Prod.fst (Except.ok.inj hb2) : Term.atom name = t'))
                (HasType.atom ctx name labels hmem)
          | .tag ctx label payload fibers fiber hlook hpay, hb2 =>
              match res_bind_ok hb2 with
              | ⟨fiber2, hl2, hb3⟩ =>
                  match res_bind_ok hb3 with
                  | ⟨r, hr, hb4⟩ =>
                      Eq.mp
                        (congrArg (fun (z : Term) => HasType ctx z (Ty.lan fibers))
                          (congrArg Prod.fst (Except.ok.inj hb4) : Term.tag label r.1 = t'))
                        (HasType.tag ctx label r.1 fibers fiber2 hl2
                          (preservesAt gasPred f2 ctx payload r.1 fiber2 r.2
                            (Eq.mp
                              (congrArg (fun (z : Ty) => HasType ctx payload z)
                                (Except.ok.inj (hlook.symm.trans hl2) : fiber = fiber2))
                              hpay)
                            hr))
          | .«section» ctx entries fibers sorted pairs hcanon halign hentries, hb2 =>
              match res_bind_ok hb2 with
              | ⟨s2, hc2, hb3⟩ =>
                  sectionCase ctx gasPred fibers entries sorted pairs
                    (fun (ctx2 : List Ty) (f3 : Nat) (x x2 : Term) (b2 : Ty) (r2 : Nat)
                        (hx : HasType ctx2 x b2)
                        (hr : reduce gasPred f3 x b2 = Except.ok (x2, r2)) =>
                      preservesAt gasPred f3 ctx2 x x2 b2 r2 hx hr)
                    hcanon halign hentries f2 t' rest
                    (Eq.mpr
                      (congrArg
                        (fun (z : List (String × Term)) =>
                          (align fibers z >>= fun (fields : List (String × Ty × Term)) =>
                            reduceFields (fun f4 x a2 => reduce gasPred f4 x a2) f2 fields
                              >>= fun (r : List (String × Term) × Nat) =>
                                Except.ok (Term.«section» r.1, r.2))
                            = Except.ok (t', rest))
                        (Except.ok.inj (hcanon.symm.trans hc2) : sorted = s2))
                      hb3)
          | .«case» ctx scrutinee fibers branches sorted pairs expected hcanon halign hscrut
              hentries, hb2 =>
              match res_bind_ok hb2 with
              | ⟨s2, hc2, hb3⟩ =>
                  match res_bind_ok hb3 with
                  | ⟨head, hh, hb4⟩ =>
                      match head, hh, hb4 with
                      | (uu, fuel2), hh2, hb5 =>
                          match uu, hh2, hb5 with
                          | .tag lbl payload, hh3, hb6 =>
                              match tagInv ctx lbl payload fibers
                                  (preservesAt gasPred f2 ctx scrutinee (Term.tag lbl payload)
                                    (Ty.lan fibers) fuel2 hscrut hh3) with
                              | ⟨fiber, hlook, hpay⟩ =>
                                  match res_bind_ok hb6 with
                                  | ⟨body, hbody, hb7⟩ =>
                                      match res_bind_ok hb7 with
                                      | ⟨opened, hsub, hb8⟩ =>
                                          preservesAt gasPred opened.2 ctx opened.1 t' expected
                                            rest
                                            (substitution_zero ctx fiber expected fuel2 opened.2
                                              payload body opened.1 hpay
                                              (branchAt ctx lbl fiber body expected pairs hentries
                                                ((congrArg
                                                    (fun (z : List (String × Ty)) =>
                                                      List.lookup lbl z)
                                                    (alignParts fibers sorted pairs halign).1).trans
                                                  (lookupSome lbl fibers fiber hlook))
                                                ((congrArg
                                                    (fun (z : List (String × Term)) =>
                                                      List.lookup lbl z)
                                                    (alignParts fibers sorted pairs halign).2).trans
                                                  (lookupSome lbl sorted body
                                                    (Eq.mpr
                                                      (congrArg
                                                        (fun (z : List (String × Term)) =>
                                                          lookup lbl z = Except.ok body)
                                                        (Except.ok.inj (hcanon.symm.trans hc2)
                                                          : sorted = s2))
                                                      hbody))))
                                              hsub).1
                                            hb8
                          | .var index, hh3, hb6 =>
                              neutralCase ctx gasPred fibers branches sorted pairs expected
                                (fun (ctx2 : List Ty) (f3 : Nat) (x x2 : Term) (b2 : Ty) (r2 : Nat)
                                    (hx : HasType ctx2 x b2)
                                    (hr : reduce gasPred f3 x b2 = Except.ok (x2, r2)) =>
                                  preservesAt gasPred f3 ctx2 x x2 b2 r2 hx hr)
                                hcanon halign hentries (Term.var index) fuel2 t' rest
                                (preservesAt gasPred f2 ctx scrutinee (Term.var index)
                                  (Ty.lan fibers) fuel2 hscrut hh3)
                                (Eq.mpr
                                  (congrArg
                                    (fun (z : List (String × Term)) =>
                                      (align fibers z >>= fun (fs : List (String × Ty × Term)) =>
                                        reduceBranches (fun f4 x a2 => reduce gasPred f4 x a2)
                                            fuel2 fs expected
                                          >>= fun (r : List (String × Term) × Nat) =>
                                            Except.ok (Term.«case» (Term.var index)
                                              (Ty.lan fibers) r.1, r.2))
                                        = Except.ok (t', rest))
                                    (Except.ok.inj (hcanon.symm.trans hc2) : sorted = s2))
                                  hb6)
                          | .«case» inner innerType innerBranches, hh3, hb6 =>
                              neutralCase ctx gasPred fibers branches sorted pairs expected
                                (fun (ctx2 : List Ty) (f3 : Nat) (x x2 : Term) (b2 : Ty) (r2 : Nat)
                                    (hx : HasType ctx2 x b2)
                                    (hr : reduce gasPred f3 x b2 = Except.ok (x2, r2)) =>
                                  preservesAt gasPred f3 ctx2 x x2 b2 r2 hx hr)
                                hcanon halign hentries
                                (Term.«case» inner innerType innerBranches) fuel2 t' rest
                                (preservesAt gasPred f2 ctx scrutinee
                                  (Term.«case» inner innerType innerBranches)
                                  (Ty.lan fibers) fuel2 hscrut hh3)
                                (Eq.mpr
                                  (congrArg
                                    (fun (z : List (String × Term)) =>
                                      (align fibers z >>= fun (fs : List (String × Ty × Term)) =>
                                        reduceBranches (fun f4 x a2 => reduce gasPred f4 x a2)
                                            fuel2 fs expected
                                          >>= fun (r : List (String × Term) × Nat) =>
                                            Except.ok (Term.«case»
                                              (Term.«case» inner innerType innerBranches)
                                              (Ty.lan fibers) r.1, r.2))
                                        = Except.ok (t', rest))
                                    (Except.ok.inj (hcanon.symm.trans hc2) : sorted = s2))
                                  hb6)
                          | .project inner innerType innerLabel, hh3, hb6 =>
                              neutralCase ctx gasPred fibers branches sorted pairs expected
                                (fun (ctx2 : List Ty) (f3 : Nat) (x x2 : Term) (b2 : Ty) (r2 : Nat)
                                    (hx : HasType ctx2 x b2)
                                    (hr : reduce gasPred f3 x b2 = Except.ok (x2, r2)) =>
                                  preservesAt gasPred f3 ctx2 x x2 b2 r2 hx hr)
                                hcanon halign hentries
                                (Term.project inner innerType innerLabel) fuel2 t' rest
                                (preservesAt gasPred f2 ctx scrutinee
                                  (Term.project inner innerType innerLabel)
                                  (Ty.lan fibers) fuel2 hscrut hh3)
                                (Eq.mpr
                                  (congrArg
                                    (fun (z : List (String × Term)) =>
                                      (align fibers z >>= fun (fs : List (String × Ty × Term)) =>
                                        reduceBranches (fun f4 x a2 => reduce gasPred f4 x a2)
                                            fuel2 fs expected
                                          >>= fun (r : List (String × Term) × Nat) =>
                                            Except.ok (Term.«case»
                                              (Term.project inner innerType innerLabel)
                                              (Ty.lan fibers) r.1, r.2))
                                        = Except.ok (t', rest))
                                    (Except.ok.inj (hcanon.symm.trans hc2) : sorted = s2))
                                  hb6)
                          | .atom _nm, _hh3, hb6 => (res_error_ne_ok hb6).elim
                          | .«section» _ents, _hh3, hb6 => (res_error_ne_ok hb6).elim
          | .project ctx sectionTerm fibers label b hlook hsec, hb2 =>
              match res_bind_ok hb2 with
              | ⟨_actual, _hl2, hb3⟩ =>
                  ite_elim
                    (P := fun (z : Res (Term × Nat)) =>
                      z = Except.ok (t', rest) → HasType ctx t' b)
                    (fun _hc hb4 =>
                      match res_bind_ok hb4 with
                      | ⟨head, hh, hb5⟩ =>
                          match head, hh, hb5 with
                          | (uu, fuel2), hh2, hb6 =>
                              match uu, hh2, hb6 with
                              | .«section» ents, hh3, hb7 =>
                                  match sectionInv ctx ents fibers
                                      (preservesAt gasPred f2 ctx sectionTerm
                                        (Term.«section» ents) (Ty.ran fibers) fuel2 hsec hh3) with
                                  | ⟨s3, pairs3, hcanon3, halign3, hentries3⟩ =>
                                      match res_bind_ok hb7 with
                                      | ⟨found, hfound, hb8⟩ =>
                                          Eq.mp
                                            (congrArg (fun (z : Term) => HasType ctx z b)
                                              (congrArg Prod.fst (Except.ok.inj hb8)
                                                : found = t'))
                                            (fieldAt ctx label b found pairs3 hentries3
                                              ((congrArg
                                                  (fun (z : List (String × Ty)) =>
                                                    List.lookup label z)
                                                  (alignParts fibers s3 pairs3 halign3).1).trans
                                                (lookupSome label fibers b hlook))
                                              ((congrArg
                                                  (fun (z : List (String × Term)) =>
                                                    List.lookup label z)
                                                  (alignParts fibers s3 pairs3 halign3).2).trans
                                                ((congrArg
                                                    (fun (z : List (String × Term)) =>
                                                      List.lookup label z)
                                                    (canonical_sorted ents s3 hcanon3)).trans
                                                  ((lookupSort label ents).trans
                                                    (lookupSome label ents found hfound)))))
                              | .var index, hh3, hb7 =>
                                  Eq.mp
                                    (congrArg (fun (z : Term) => HasType ctx z b)
                                      (congrArg Prod.fst (Except.ok.inj hb7)
                                        : Term.project (Term.var index) (Ty.ran fibers) label
                                            = t'))
                                    (HasType.project ctx (Term.var index) fibers label b hlook
                                      (preservesAt gasPred f2 ctx sectionTerm (Term.var index)
                                        (Ty.ran fibers) fuel2 hsec hh3))
                              | .«case» inner innerType innerBranches, hh3, hb7 =>
                                  Eq.mp
                                    (congrArg (fun (z : Term) => HasType ctx z b)
                                      (congrArg Prod.fst (Except.ok.inj hb7)
                                        : Term.project
                                            (Term.«case» inner innerType innerBranches)
                                            (Ty.ran fibers) label = t'))
                                    (HasType.project ctx
                                      (Term.«case» inner innerType innerBranches) fibers label b
                                      hlook
                                      (preservesAt gasPred f2 ctx sectionTerm
                                        (Term.«case» inner innerType innerBranches)
                                        (Ty.ran fibers) fuel2 hsec hh3))
                              | .project inner innerType innerLabel, hh3, hb7 =>
                                  Eq.mp
                                    (congrArg (fun (z : Term) => HasType ctx z b)
                                      (congrArg Prod.fst (Except.ok.inj hb7)
                                        : Term.project
                                            (Term.project inner innerType innerLabel)
                                            (Ty.ran fibers) label = t'))
                                    (HasType.project ctx
                                      (Term.project inner innerType innerLabel) fibers label b
                                      hlook
                                      (preservesAt gasPred f2 ctx sectionTerm
                                        (Term.project inner innerType innerLabel)
                                        (Ty.ran fibers) fuel2 hsec hh3))
                              | .atom _nm, _hh3, hb7 => (res_error_ne_ok hb7).elim
                              | .tag _lbl _payload, _hh3, hb7 => (res_error_ne_ok hb7).elim)
                    (fun _hc hb4 => (res_error_ne_ok hb4).elim)
                    hb3

end NormTyping

/-- Row Theorem6-11.3 of the theorem inventory: reduction keeps the type of the input term. docs/metatheory.md lines 321 to 353 state it of
`reduce` at lib/finite_term.ml lines 162 to 225. A reduced term of one type holds that type again, under the same context.
-/
theorem reduce_preserves_type (gas f : Nat) (g : List Ty) (t t' : Term) (a : Ty) (rest : Nat)
    (typed : HasType g t a) (reduced : reduce gas f t a = Except.ok (t', rest)) :
    HasType g t' a :=
  NormTyping.preservesAt gas f g t t' a rest typed reduced


/-- A successful public normalization checks its input and preserves that type.
This composes checker soundness with reduction preservation for the shared budget of lib/finite_term.ml lines 227 to 229.
No input typing hypothesis is required.
-/
theorem normalize_preserves_type (fuel : Nat) (g : List Ty) (t t' : Term) (a : Ty)
    (h : normalize fuel g t a = Except.ok t') : HasType g t' a :=
  match res_bind_ok h with
  | ⟨remaining, checked, reduced⟩ =>
      match res_bind_ok reduced with
      | ⟨result, core, returned⟩ =>
          (Except.ok.inj returned) ▸
            reduce_preserves_type (remaining + 1) remaining g t result.1 a result.2
              (Checker.check_core_sound (2 * fuel + 2) fuel g t a remaining checked) core

/-- The output of public normalization passes the checker at its node count.
The OCaml normalizer at lib/finite_term.ml lines 227 to 229 performs no output check.
Checker completeness makes that omitted check a theorem, without spending the input budget.
-/
theorem normalize_output_checks (fuel : Nat) (g : List Ty) (t t' : Term) (a : Ty)
    (h : normalize fuel g t a = Except.ok t') : check (size t') g t' a = Except.ok () :=
  check_complete (size t') g t' a (normalize_preserves_type fuel g t t' a h) (Nat.le_refl _)
