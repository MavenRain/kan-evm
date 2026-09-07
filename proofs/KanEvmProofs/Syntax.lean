/-! # Syntax of the finite fragment

This module mirrors the nondependent finite fragment of lib/finite_term.ml.
It holds the deep embedding of decision S2-D1. It also holds the canonicity predicate of decision S2-D2 and the error type of
S2-D3.
-/

/-- `Ty` mirrors the OCaml type `ty` at lib/finite_term.ml line 1.
`atoms` holds a finite label set. `lan` and `ran` hold one fiber list each.
Decision S2-D1 keeps the `List` nesting, so this is a nested inductive.
The constructors are exported, so a hand built value need not satisfy `Ty.Canonical`.
-/
inductive Ty where
  | atoms (labels : List String)
  | lan (fibers : List (String × Ty))
  | ran (fibers : List (String × Ty))
  deriving Repr

/-- `Term` mirrors the OCaml type `term`, per decision S2-D1.
`Term` follows lib/finite_term.mli lines 21 to 28 and lib/finite_term.ml lines 31 to 38.
The names `section` and `case` are Lean keywords, so each one takes the guillemet form.
`var` carries a `Nat` index.
The OCaml test for a negative index at lib/finite_term.ml line 44 has no image over `Nat`.
Each `case` branch binds its payload at index zero, as lib/finite_term.mli line 31 states.
-/
inductive Term where
  | var (index : Nat)
  | atom (label : String)
  | tag (label : String) (payload : Term)
  | «section» (fields : List (String × Term))
  | «case» (scrutinee : Term) (scrutineeType : Ty) (branches : List (String × Term))
  | project («section» : Term) (sectionType : Ty) (label : String)
  deriving Repr

/-- `Err` mirrors the OCaml type `error`, constructor for constructor, per decision S2-D3.
`Err` follows lib/finite_term.mli lines 4 to 13 and lib/finite_term.ml lines 2 to 11.
`invalidVariable` carries a `Nat`, which matches the `var` index of `Term`.
-/
inductive Err where
  | duplicateLabel (label : String)
  | missingLabel (label : String)
  | unexpectedLabel (label : String)
  | invalidVariable (index : Nat)
  | invalidAtom (name : String)
  | typeMismatch
  | expectedLan
  | expectedRan
  | resourceExhausted
  deriving Repr, DecidableEq, BEq

/-- `Res` is the result monad of decision S2-D3.
`Res` replaces the OCaml `result` type and the bind operator at lib/finite_term.ml line 13.
Every helper of this package stays total and reports a failure as an `Err` value.
-/
abbrev Res (a : Type) : Type := Except Err a

/-- `labelLe` is the ascending label order of `String.compare`.
The two OCaml sorts at lib/finite_term.ml lines 21 and 26 use that same comparison.
The result is `true` when the first label comes first or equals the second one.
-/
def labelLe (a b : String) : Bool := (compare a b).isLE

/-- `insertLabel` puts one label into a list that already holds the ascending order.
`insertLabel` is the step of `sortLabels`, which mirrors lib/finite_term.ml line 26.
-/
def insertLabel (label : String) : List String → List String
  | [] => [label]
  | head :: rest =>
      if labelLe label head then label :: head :: rest else head :: insertLabel label rest

/-- `sortLabels` sorts a label list into ascending order.
`sortLabels` mirrors `List.sort String.compare` at lib/finite_term.ml line 26.
Decision S2-D5 names `List.mergeSort` here.
That function is well founded at Lean v4.33.1 and does not reduce through `rfl`.
The examples of decision S2-D10 need that reduction, so this structural sort replaces it.
Both functions return the same ascending order. A repeated label stays an error of `unique`.
-/
def sortLabels : List String → List String
  | [] => []
  | head :: rest => insertLabel head (sortLabels rest)

/-- `insertFiber` puts one fiber into a list that already holds the ascending label order.
`insertFiber` is the step of `sortFibers`, which mirrors lib/finite_term.ml line 21.
-/
def insertFiber (fiber : String × Ty) : List (String × Ty) → List (String × Ty)
  | [] => [fiber]
  | head :: rest =>
      if labelLe fiber.1 head.1 then fiber :: head :: rest else head :: insertFiber fiber rest

/-- `sortFibers` sorts a fiber list into ascending label order.
`sortFibers` mirrors the sort of `canonical` at lib/finite_term.ml line 21.
The order key is the label alone, as that OCaml comparison shows.
-/
def sortFibers : List (String × Ty) → List (String × Ty)
  | [] => []
  | head :: rest => insertFiber head (sortFibers rest)

mutual
/-- `Ty.beq` compares two types structurally.
`Ty.beq` serves the type comparisons at lib/finite_term.ml lines 67 and 100.
Lemma0 of the theorem inventory relates this comparison to equality on canonical types.
-/
def Ty.beq : Ty → Ty → Bool
  | .atoms l1, .atoms l2 => l1 == l2
  | .lan f1, .lan f2 => Ty.beqFibers f1 f2
  | .ran f1, .ran f2 => Ty.beqFibers f1 f2
  | .atoms .., .lan .. => false
  | .atoms .., .ran .. => false
  | .lan .., .atoms .. => false
  | .lan .., .ran .. => false
  | .ran .., .atoms .. => false
  | .ran .., .lan .. => false

/-- `Ty.beqFibers` compares two fiber lists structurally, label and fiber together.
`Ty.beqFibers` is the list partner of `Ty.beq` for the nested inductive of decision S2-D1.
`Ty.beq` mirrors the type comparison of lib/finite_term.ml line 67 and line 100, and this list partner states no proposition of docs/metatheory.md.
-/
def Ty.beqFibers : List (String × Ty) → List (String × Ty) → Bool
  | [], [] => true
  | [], .cons .. => false
  | .cons .., [] => false
  | (a, t) :: r1, (b, u) :: r2 => a == b && Ty.beq t u && Ty.beqFibers r1 r2
end

/-- `BEq Ty` gives the `==` notation for the structural comparison of `Ty.beq`.
The OCaml checker uses the same structural comparison at lib/finite_term.ml lines 67 and 100.
-/
instance : BEq Ty := ⟨Ty.beq⟩

/-- `Ty.SortedLabels` is part one of canonicity, per decision S2-D2.
Every adjacent label pair holds the ascending order of `labelLe`.
The sort of lib/finite_term.ml lines 20 to 23 establishes that order, and docs/metatheory.md lines 23 and 24 name it in
Lemma 0.
-/
def Ty.SortedLabels : List String → Prop
  | [] => True
  | [_only] => True
  | a :: b :: rest => labelLe a b = true ∧ Ty.SortedLabels (b :: rest)

/-- `Ty.DistinctLabels` is part two of canonicity, per decision S2-D2.
`Ty.DistinctLabels` mirrors the adjacent test of `unique` at lib/finite_term.ml lines 15 to 18.
With part one, the adjacent test gives distinctness over the whole list.
-/
def Ty.DistinctLabels : List String → Prop
  | [] => True
  | [_only] => True
  | a :: b :: rest => a ≠ b ∧ Ty.DistinctLabels (b :: rest)

mutual
/-- `Ty.Canonical` states the three parts of decision S2-D2.
Each fiber list holds the ascending label order and no label repeats.
Every nested type is canonical too. A successful result of `atoms` satisfies this predicate, since a label list holds no nested type.
A successful result of `lan` or of `ran` satisfies it when every fiber given is canonical, since the smart constructor sorts the outer label list alone.
Lemma0 proves both forms. It states Lemma 0 of docs/metatheory.md lines 23 and 24 as one predicate, which the
OCaml side gets from the abstraction boundary of lib/finite_term.mli line 3.
-/
def Ty.Canonical : Ty → Prop
  | .atoms labels => Ty.SortedLabels labels ∧ Ty.DistinctLabels labels
  | .lan fibers =>
      Ty.SortedLabels (fibers.map Prod.fst) ∧ Ty.DistinctLabels (fibers.map Prod.fst)
        ∧ Ty.CanonicalFibers fibers
  | .ran fibers =>
      Ty.SortedLabels (fibers.map Prod.fst) ∧ Ty.DistinctLabels (fibers.map Prod.fst)
        ∧ Ty.CanonicalFibers fibers

/-- `Ty.CanonicalFibers` walks a fiber list and states canonicity of every fiber.
`Ty.CanonicalFibers` is the list partner of `Ty.Canonical`, per decision S2-D1.
The fiber lists come from lib/finite_term.ml lines 20 to 23, and docs/metatheory.md lines 23 and 24 name the order of
Lemma 0.
-/
def Ty.CanonicalFibers : List (String × Ty) → Prop
  | [] => True
  | (_label, fiber) :: rest => Ty.Canonical fiber ∧ Ty.CanonicalFibers rest
end

/-- `unique` mirrors the OCaml `unique` at lib/finite_term.ml lines 15 to 18.
The input holds the ascending order, so one adjacent test finds every repeat.
The first repeated label becomes `Err.duplicateLabel`.
-/
def unique : List String → Res Unit
  | [] => .ok ()
  | [_only] => .ok ()
  | a :: b :: rest => if a = b then .error (.duplicateLabel a) else unique (b :: rest)

/-- `canonical` mirrors the OCaml `canonical` at lib/finite_term.ml lines 20 to 23.
It sorts the entries into ascending label order, then it tests the labels for a repeat.
The sort cannot fail, so `Err.duplicateLabel` is the only error here.
-/
def canonical (entries : List (String × Ty)) : Res (List (String × Ty)) :=
  let sorted := sortFibers entries
  unique (sorted.map Prod.fst) >>= fun (_ok : Unit) => .ok sorted

/-- `atoms` mirrors the OCaml `atoms` at lib/finite_term.ml lines 25 to 27.
It sorts the labels, then it rejects a repeated label.
A successful result satisfies `Ty.Canonical`, per decision S2-D2.
-/
def atoms (labels : List String) : Res Ty :=
  let sorted := sortLabels labels
  unique sorted >>= fun (_ok : Unit) => .ok (.atoms sorted)

/-- `lan` mirrors the OCaml `lan` at lib/finite_term.ml line 28.
It canonicalizes the fibers, then it wraps them as a left extension type.
A successful result satisfies `Ty.Canonical` when every fiber given is canonical, per decision S2-D2 and
Lemma0. The sort reaches the outer label list alone, and the exported `Ty` constructors let a caller supply a fiber that no smart constructor built, which the
OCaml `lan` at line 28 cannot receive, since the abstraction boundary of lib/finite_term.mli line 3 holds there.
-/
def lan (entries : List (String × Ty)) : Res Ty :=
  canonical entries >>= fun fibers => .ok (.lan fibers)

/-- `ran` mirrors the OCaml `ran` at lib/finite_term.ml line 29.
It canonicalizes the fibers, then it wraps them as a right extension type.
A successful result satisfies `Ty.Canonical` when every fiber given is canonical, per decision S2-D2 and
Lemma0. The sort reaches the outer label list alone, and the exported `Ty` constructors let a caller supply a fiber that no smart constructor built, which the
OCaml `ran` at line 29 cannot receive, since the abstraction boundary of lib/finite_term.mli line 3 holds there.
-/
def ran (entries : List (String × Ty)) : Res Ty :=
  canonical entries >>= fun fibers => .ok (.ran fibers)
