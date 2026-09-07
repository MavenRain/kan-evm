import KanEvmProofs.Syntax

/-! # Lemma 0 of the finite fragment

This module holds row Lemma0 of the theorem inventory. `ty_canonical` states that every type a smart constructor returns is canonical.
`canonical_beq_iff` states that structural equality decides the intended type equality.
The two names mirror lib/finite_term.ml lines 15 to 29 and lines 67 and 100.
They state docs/metatheory.md lines 21 to 33. Decision S2-D1 exports the `Ty` constructors, so the scope is a smart constructor result alone.
Canonicity of an annotation inside a `Term` comes from the side condition of decision S2-D7.
Namespace `Canon` holds the helper lemmas, and the two inventory names sit at the root.
-/

namespace Canon

/-- `hold_first` returns the first proof and holds the second one.
The unused variable linter asks every arm of a proof to name each binder it needs.
Three arms of this module carry a hypothesis that the goal of the arm does not need.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem hold_first {p q : Prop} (hp : p) (hq : q) : p := (And.intro hp hq).left

/-- `error_ne_ok` states that a failure result never equals a success result.
It serves the smart constructor proofs of lib/finite_term.ml lines 20 to 29. docs/metatheory.md lines 21 to 33 need that step for
Lemma 0.
-/
theorem error_ne_ok {α : Type} {e : Err} {v : α}
    (h : (Except.error e : Res α) = Except.ok v) : False := nomatch h

/-- `false_ne_true` states that the two `Bool` values differ.
It serves the structural comparison of lib/finite_term.ml lines 67 and 100. docs/metatheory.md line 32 states the comparison part of
Lemma 0.
-/
theorem false_ne_true (h : (false : Bool) = true) : False := Bool.noConfusion h

/-- `true_ne_false` states the same difference of the two `Bool` values in the other order.
It serves the order test of lib/finite_term.ml lines 21 and 26. docs/metatheory.md lines 23 and 24 states the sorted order of
Lemma 0.
-/
theorem true_ne_false (h : (true : Bool) = false) : False := Bool.noConfusion h

/-- `ok_of_bind` splits one successful bind into a successful step and a successful rest.
It mirrors the `let*` operator of lib/finite_term.ml line 13.
The three smart constructors of lib/finite_term.ml lines 20 to 29 use that operator.
-/
theorem ok_of_bind {α β : Type} (m : Res α) (k : α → Res β) (b : β)
    (h : (m >>= k) = Except.ok b) : ∃ a, m = Except.ok a ∧ k a = Except.ok b :=
  match m, h with
  | .ok a, hok => ⟨a, rfl, hok⟩
  | .error e, herr => False.elim (error_ne_ok (α := β) (e := e) (v := b) herr)

/-- `labelLe_swap` states that the label order of `labelLe` is total.
The order comes from `String.compare`, which lib/finite_term.ml lines 21 and 26 use. docs/metatheory.md lines 21 to 25 need totality for the sorted order of
Lemma 0.
-/
theorem labelLe_swap (a b : String) (h : labelLe a b = false) : labelLe b a = true :=
  match hab : compare a b with
  | .lt => False.elim (true_ne_false ((congrArg Ordering.isLE hab).symm.trans h))
  | .eq => False.elim (true_ne_false ((congrArg Ordering.isLE hab).symm.trans h))
  | .gt =>
      congrArg Ordering.isLE
        (Std.OrientedCmp.eq_swap.trans (congrArg Ordering.swap hab) : compare b a = Ordering.lt)

/-- `labelLe_of_not` restates `labelLe_swap` for a negated hypothesis.
The insertion step of the sorts at lib/finite_term.ml lines 21 and 26 reaches this form. docs/metatheory.md lines 21 to 25 state the sorted order of
Lemma 0.
-/
theorem labelLe_of_not (a b : String) (h : ¬(labelLe a b = true)) : labelLe b a = true :=
  labelLe_swap a b (Eq.mp (Bool.not_eq_true (labelLe a b)) h)

/-- `LeHead` states that one label precedes the head of a label list.
`LeHead` is the step relation of the sorts at lib/finite_term.ml lines 21 and 26. docs/metatheory.md lines 23 and 24 names the sorted order that
`LeHead` supports.
-/
def LeHead (a : String) (l : List String) : Prop :=
  match l.head? with
  | none => True
  | some b => labelLe a b = true

/-- `sortedLabels_cons` puts one label in front of a sorted label list.
The sorted order is part one of the canonicity of decision S2-D2. docs/metatheory.md lines 23 and 24 states that part of
Lemma 0.
-/
theorem sortedLabels_cons (a : String) : (l : List String) →
    LeHead a l ∧ Ty.SortedLabels l → Ty.SortedLabels (a :: l)
  | [], h => h.1
  | .cons .., h => h

/-- `sortedLabels_uncons` reads the head order and the tail order out of a sorted list.
It is the inverse of `sortedLabels_cons` for part one of decision S2-D2. docs/metatheory.md lines 23 and 24 states that part of
Lemma 0.
-/
theorem sortedLabels_uncons (a : String) : (l : List String) →
    Ty.SortedLabels (a :: l) → LeHead a l ∧ Ty.SortedLabels l
  | [], h => ⟨h, h⟩
  | .cons .., h => h

/-- `leHead_insertLabel` keeps the head order through one insertion.
`insertLabel` is the step of the label sort of lib/finite_term.ml line 26. docs/metatheory.md lines 23 and 24 states the sorted order that this step holds.
-/
theorem leHead_insertLabel (a x : String) : (l : List String) →
    labelLe a x = true ∧ LeHead a l → LeHead a (insertLabel x l)
  | [], h => h.1
  | b :: rest, h =>
      if hb : labelLe x b = true then
        Eq.mpr (congrArg (LeHead a)
            (if_pos hb : insertLabel x (b :: rest) = x :: b :: rest)) h.1
      else
        Eq.mpr (congrArg (LeHead a)
            (if_neg hb : insertLabel x (b :: rest) = b :: insertLabel x rest)) h.2

/-- `sortedLabels_insertLabel` keeps the sorted order through one insertion.
`insertLabel` is the step of the label sort of lib/finite_term.ml line 26. docs/metatheory.md lines 23 and 24 states the sorted order of
Lemma 0.
-/
theorem sortedLabels_insertLabel (x : String) : (l : List String) →
    Ty.SortedLabels l → Ty.SortedLabels (insertLabel x l)
  | [], h => h
  | b :: rest, h =>
      if hb : labelLe x b = true then
        Eq.mpr (congrArg Ty.SortedLabels
            (if_pos hb : insertLabel x (b :: rest) = x :: b :: rest))
          (sortedLabels_cons x (b :: rest) ⟨hb, h⟩)
      else
        Eq.mpr (congrArg Ty.SortedLabels
            (if_neg hb : insertLabel x (b :: rest) = b :: insertLabel x rest))
          (sortedLabels_cons b (insertLabel x rest)
            ⟨leHead_insertLabel b x rest
              ⟨labelLe_of_not x b hb, (sortedLabels_uncons b rest h).1⟩,
              sortedLabels_insertLabel x rest (sortedLabels_uncons b rest h).2⟩)

/-- `sortLabels_sorted` states that the label sort returns a sorted list.
`sortLabels` mirrors the sort of lib/finite_term.ml line 26. docs/metatheory.md lines 23 and 24 states the sorted order of
Lemma 0.
-/
theorem sortLabels_sorted : (l : List String) → Ty.SortedLabels (sortLabels l)
  | [] => True.intro
  | head :: rest => sortedLabels_insertLabel head (sortLabels rest) (sortLabels_sorted rest)

/-- `distinctLabels_of_unique` reads distinctness out of a successful `unique` run.
`unique` mirrors lib/finite_term.ml lines 15 to 18. docs/metatheory.md lines 23 and 24 states the distinctness part of
Lemma 0.
-/
theorem distinctLabels_of_unique : (l : List String) →
    unique l = Except.ok () → Ty.DistinctLabels l
  | [], h => hold_first True.intro h
  | [_only], h => hold_first True.intro h
  | a :: b :: rest, h =>
      if hab : a = b then
        False.elim (error_ne_ok (α := Unit) (e := Err.duplicateLabel a) (v := ())
          ((if_pos hab : unique (a :: b :: rest)
            = Except.error (Err.duplicateLabel a)).symm.trans h))
      else
        ⟨hab, distinctLabels_of_unique (b :: rest)
          ((if_neg hab : unique (a :: b :: rest) = unique (b :: rest)).symm.trans h)⟩

/-- `map_insertFiber` states that one fiber insertion moves the label list one step.
`insertFiber` is the step of the fiber sort of lib/finite_term.ml line 21. docs/metatheory.md lines 23 and 24 states the sorted order that the step holds.
-/
theorem map_insertFiber (f : String × Ty) : (l : List (String × Ty)) →
    List.map Prod.fst (insertFiber f l) = insertLabel f.1 (List.map Prod.fst l)
  | [] => rfl
  | b :: rest =>
      if hb : labelLe f.1 b.1 = true then
        (congrArg (List.map Prod.fst)
            (if_pos hb : insertFiber f (b :: rest) = f :: b :: rest)).trans
          (if_pos hb : insertLabel f.1 (b.1 :: List.map Prod.fst rest)
            = f.1 :: b.1 :: List.map Prod.fst rest).symm
      else
        (congrArg (List.map Prod.fst)
            (if_neg hb : insertFiber f (b :: rest) = b :: insertFiber f rest)).trans
          ((congrArg (List.cons b.1) (map_insertFiber f rest)).trans
            (if_neg hb : insertLabel f.1 (b.1 :: List.map Prod.fst rest)
              = b.1 :: insertLabel f.1 (List.map Prod.fst rest)).symm)

/-- `map_sortFibers` states that the fiber sort and the label sort agree on labels.
`sortFibers` mirrors the sort of lib/finite_term.ml line 21, which orders on the label alone. docs/metatheory.md lines 23 and 24 states the sorted order of
Lemma 0.
-/
theorem map_sortFibers : (l : List (String × Ty)) →
    List.map Prod.fst (sortFibers l) = sortLabels (List.map Prod.fst l)
  | [] => rfl
  | head :: rest =>
      (map_insertFiber head (sortFibers rest)).trans
        (congrArg (insertLabel head.1) (map_sortFibers rest))

/-- `canonicalFibers_insertFiber` keeps canonicity of every fiber through one insertion.
`insertFiber` is the step of the fiber sort of lib/finite_term.ml line 21. docs/metatheory.md lines 26 to 28 state the nesting part of
Lemma 0.
-/
theorem canonicalFibers_insertFiber (f : String × Ty) (hf : Ty.Canonical f.2) :
    (l : List (String × Ty)) →
    Ty.CanonicalFibers l → Ty.CanonicalFibers (insertFiber f l)
  | [], h => ⟨hf, h⟩
  | b :: rest, h =>
      if hb : labelLe f.1 b.1 = true then
        Eq.mpr (congrArg Ty.CanonicalFibers
            (if_pos hb : insertFiber f (b :: rest) = f :: b :: rest)) ⟨hf, h⟩
      else
        Eq.mpr (congrArg Ty.CanonicalFibers
            (if_neg hb : insertFiber f (b :: rest) = b :: insertFiber f rest))
          ⟨h.1, canonicalFibers_insertFiber f hf rest h.2⟩

/-- `canonicalFibers_sortFibers` keeps canonicity of every fiber through the fiber sort.
`sortFibers` mirrors the sort of lib/finite_term.ml line 21. docs/metatheory.md lines 26 to 28 state the nesting part of
Lemma 0.
-/
theorem canonicalFibers_sortFibers : (l : List (String × Ty)) →
    Ty.CanonicalFibers l → Ty.CanonicalFibers (sortFibers l)
  | [], h => h
  | head :: rest, h =>
      canonicalFibers_insertFiber head h.1 (sortFibers rest)
        (canonicalFibers_sortFibers rest h.2)

/-- `canonical_ok` reads the two facts a successful `canonical` run gives.
`canonical` mirrors lib/finite_term.ml lines 20 to 23. docs/metatheory.md lines 21 to 28 state the parts of
Lemma 0 that the two facts serve.
-/
theorem canonical_ok (entries fibers : List (String × Ty))
    (h : canonical entries = Except.ok fibers) :
    fibers = sortFibers entries
      ∧ unique (List.map Prod.fst (sortFibers entries)) = Except.ok () :=
  match ok_of_bind (unique (List.map Prod.fst (sortFibers entries)))
      (fun (_ok : Unit) => (Except.ok (sortFibers entries) : Res (List (String × Ty))))
      fibers h with
  | ⟨_u, hu, hk⟩ => ⟨(Except.ok.inj hk).symm, hu⟩

/-- `canonical_sorted` states the sorted order of a successful `canonical` run.
`canonical` mirrors lib/finite_term.ml lines 20 to 23. docs/metatheory.md lines 23 and 24 states the sorted order of
Lemma 0.
-/
theorem canonical_sorted (entries : List (String × Ty)) :
    Ty.SortedLabels (List.map Prod.fst (sortFibers entries)) :=
  Eq.mpr (congrArg Ty.SortedLabels (map_sortFibers entries))
    (sortLabels_sorted (List.map Prod.fst entries))

/-- `atoms_canonical` states part one of Lemma 0 for the atom constructor.
`atoms` mirrors lib/finite_term.ml lines 25 to 27. docs/metatheory.md lines 21 to 33 state Lemma 0.
-/
theorem atoms_canonical (labels : List String) (t : Ty)
    (h : atoms labels = Except.ok t) : Ty.Canonical t :=
  match ok_of_bind (unique (sortLabels labels))
      (fun (_ok : Unit) => (Except.ok (Ty.atoms (sortLabels labels)) : Res Ty)) t h with
  | ⟨_u, hu, hk⟩ =>
      Eq.mpr (congrArg Ty.Canonical ((Except.ok.inj hk).symm : t = Ty.atoms (sortLabels labels)))
        ⟨sortLabels_sorted labels, distinctLabels_of_unique (sortLabels labels) hu⟩

/-- `lan_canonical` states part two of Lemma 0 for the left extension constructor.
`lan` mirrors lib/finite_term.ml line 28. docs/metatheory.md lines 21 to 33 state Lemma 0, and lines 31 to 33 name the exported constructors, so canonicity of every fiber given is a hypothesis here.
-/
theorem lan_canonical (entries : List (String × Ty)) (t : Ty)
    (hc : Ty.CanonicalFibers entries) (h : lan entries = Except.ok t) : Ty.Canonical t :=
  match ok_of_bind (canonical entries)
      (fun fibers => (Except.ok (Ty.lan fibers) : Res Ty)) t h with
  | ⟨fibers, hcan, hk⟩ =>
      Eq.mpr (congrArg Ty.Canonical
          (((Except.ok.inj hk).symm.trans (congrArg Ty.lan (canonical_ok entries fibers hcan).1) :
            t = Ty.lan (sortFibers entries))))
        ⟨canonical_sorted entries,
          distinctLabels_of_unique (List.map Prod.fst (sortFibers entries))
            (canonical_ok entries fibers hcan).2,
          canonicalFibers_sortFibers entries hc⟩

/-- `ran_canonical` states part three of Lemma 0 for the right extension constructor.
`ran` mirrors lib/finite_term.ml line 29. docs/metatheory.md lines 21 to 33 state Lemma 0, and lines 31 to 33 name the exported constructors, so canonicity of every fiber given is a hypothesis here.
-/
theorem ran_canonical (entries : List (String × Ty)) (t : Ty)
    (hc : Ty.CanonicalFibers entries) (h : ran entries = Except.ok t) : Ty.Canonical t :=
  match ok_of_bind (canonical entries)
      (fun fibers => (Except.ok (Ty.ran fibers) : Res Ty)) t h with
  | ⟨fibers, hcan, hk⟩ =>
      Eq.mpr (congrArg Ty.Canonical
          (((Except.ok.inj hk).symm.trans (congrArg Ty.ran (canonical_ok entries fibers hcan).1) :
            t = Ty.ran (sortFibers entries))))
        ⟨canonical_sorted entries,
          distinctLabels_of_unique (List.map Prod.fst (sortFibers entries))
            (canonical_ok entries fibers hcan).2,
          canonicalFibers_sortFibers entries hc⟩

end Canon

/-- `ty_canonical` is row Lemma0, part one of the theorem inventory.
Every type that one of the three smart constructors returns is canonical.
The three parts mirror `atoms`, `lan` and `ran` at lib/finite_term.ml lines 25 to 29. docs/metatheory.md lines 21 to 33 state
Lemma 0. The `lan` part and the `ran` part carry canonicity of every fiber given, since decision S2-D1 exports the
`Ty` constructors and docs/metatheory.md lines 31 to 33 record that limit.
-/
theorem ty_canonical :
    (∀ (labels : List String) (t : Ty), atoms labels = Except.ok t → Ty.Canonical t)
      ∧ (∀ (entries : List (String × Ty)) (t : Ty),
          Ty.CanonicalFibers entries → lan entries = Except.ok t → Ty.Canonical t)
      ∧ (∀ (entries : List (String × Ty)) (t : Ty),
          Ty.CanonicalFibers entries → ran entries = Except.ok t → Ty.Canonical t) :=
  ⟨Canon.atoms_canonical, Canon.lan_canonical, Canon.ran_canonical⟩

mutual
/-- `ty_beq_iff` states that the structural comparison decides equality of two types.
`Ty.beq` serves the two type comparisons at lib/finite_term.ml lines 67 and 100. docs/metatheory.md line 32 states this consequence of
Lemma 0. The proof is a term-mode pair of theorems in one `mutual` block, per the induction rule of the builder rules, since
`Ty` nests a `List` of fibers.
-/
theorem ty_beq_iff : (t u : Ty) → (Ty.beq t u = true ↔ t = u)
  | .atoms .., .atoms .. =>
      ⟨fun h => congrArg Ty.atoms (eq_of_beq h), fun h => beq_iff_eq.mpr (Ty.atoms.inj h)⟩
  | .lan f1, .lan f2 =>
      ⟨fun h => congrArg Ty.lan ((ty_beqFibers_iff f1 f2).mp h),
        fun h => (ty_beqFibers_iff f1 f2).mpr (Ty.lan.inj h)⟩
  | .ran f1, .ran f2 =>
      ⟨fun h => congrArg Ty.ran ((ty_beqFibers_iff f1 f2).mp h),
        fun h => (ty_beqFibers_iff f1 f2).mpr (Ty.ran.inj h)⟩
  | .atoms .., .lan .. =>
      ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩
  | .atoms .., .ran .. =>
      ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩
  | .lan .., .atoms .. =>
      ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩
  | .lan .., .ran .. =>
      ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩
  | .ran .., .atoms .. =>
      ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩
  | .ran .., .lan .. =>
      ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩

/-- `ty_beqFibers_iff` is the fiber list partner of `ty_beq_iff`.
`Ty.beqFibers` walks the fiber lists that lib/finite_term.ml lines 67 and 100 compare. docs/metatheory.md line 32 states that two canonical types are equal exactly when they carry the same labels and the same fiber types.
-/
theorem ty_beqFibers_iff : (f g : List (String × Ty)) → (Ty.beqFibers f g = true ↔ f = g)
  | [], [] => ⟨fun h => Canon.hold_first rfl h, fun h => Canon.hold_first rfl h⟩
  | [], .cons .. => ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩
  | .cons .., [] => ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩
  | (a, t) :: r1, (b, u) :: r2 =>
      ⟨fun h =>
        congr
          (congrArg List.cons
            (congr (congrArg Prod.mk
                (eq_of_beq (Eq.mp (Bool.and_eq_true (a == b) (Ty.beq t u))
                  (Eq.mp (Bool.and_eq_true (a == b && Ty.beq t u) (Ty.beqFibers r1 r2)) h).1).1))
              ((ty_beq_iff t u).mp
                (Eq.mp (Bool.and_eq_true (a == b) (Ty.beq t u))
                  (Eq.mp (Bool.and_eq_true (a == b && Ty.beq t u) (Ty.beqFibers r1 r2)) h).1).2)))
          ((ty_beqFibers_iff r1 r2).mp
            (Eq.mp (Bool.and_eq_true (a == b && Ty.beq t u) (Ty.beqFibers r1 r2)) h).2),
        fun h =>
        Eq.mpr (Bool.and_eq_true (a == b && Ty.beq t u) (Ty.beqFibers r1 r2))
          ⟨Eq.mpr (Bool.and_eq_true (a == b) (Ty.beq t u))
              ⟨beq_iff_eq.mpr (Prod.mk.inj (List.cons.inj h).1).1,
                (ty_beq_iff t u).mpr (Prod.mk.inj (List.cons.inj h).1).2⟩,
            (ty_beqFibers_iff r1 r2).mpr (List.cons.inj h).2⟩⟩
end

/-- `canonical_beq_iff` is row Lemma0, part two of the theorem inventory.
On canonical types the structural equality of lib/finite_term.ml lines 67 and 100 agrees with the intended type equality. docs/metatheory.md line 32 states that consequence of
Lemma 0. The two canonicity hypotheses hold the scope of the statement, and the proof reaches the stronger
`ty_beq_iff`, which the deep embedding of decision S2-D1 makes available.
-/
theorem canonical_beq_iff (t u : Ty) (_ht : Ty.Canonical t) (_hu : Ty.Canonical u) :
    ((t == u) = true ↔ t = u) := ty_beq_iff t u
