import KanEvmProofs.Reduce

/-! # Fidelity examples of the finite fragment

This module transcribes the measured cases of decision S2-D10.
Every fuel number comes from test/finite_normalize_test.ml, which holds the binding numbers.
The exact budgets 10, 8 and 6 come from the boundary list at lines 42 to 56 of that file.
The neutral form cases come from lines 47, 48 and 58 to 82 of that file and run at fuel 100000.
Each example closes with `rfl`, so the Lean model computes the OCaml result at the OCaml fuel.
Gate S2-G5 builds this module, so a fuel number that moves fails the gate.
The fidelity table of decision S2-D9 sits in proofs/FIDELITY.md and no proof depends on it.
-/

namespace Fidelity

/-- `tyA` is the type `atoms ["x", "y"]` of test/finite_normalize_test.ml line 24.
The OCaml source names it `a`.
-/
def tyA : Ty := .atoms ["x", "y"]

/-- `tyOne` is the type `atoms ["x"]` of test/finite_normalize_test.ml line 26.
The OCaml source names it `one`.
-/
def tyOne : Ty := .atoms ["x"]

/-- `tySum` is the type `lan ["k", a]` of test/finite_normalize_test.ml line 27.
The OCaml source names it `sum`.
-/
def tySum : Ty := .lan [("k", tyA)]

/-- `tyOneSum` is the type `lan ["a", one]` of test/finite_normalize_test.ml line 28.
The OCaml source names it `one_sum`.
-/
def tyOneSum : Ty := .lan [("a", tyOne)]

/-- `tyTwo` is the right extension type of test/finite_normalize_test.ml line 30.
It holds the two fibers `a` and `b`, and each fiber is the type `tyA`.
The OCaml source names it `two`.
-/
def tyTwo : Ty := .ran [("a", tyA), ("b", tyA)]

/-- The smart constructor `atoms` of Syntax.lean returns `tyA`, so the fixture is canonical.
The fixture is test data of test/finite_normalize_test.ml, and it states no proposition of docs/metatheory.md.
-/
example : atoms ["x", "y"] = .ok tyA := rfl

/-- The smart constructor `atoms` of Syntax.lean returns `tyOne`, so the fixture is canonical.
The fixture is test data of test/finite_normalize_test.ml, and it states no proposition of docs/metatheory.md.
-/
example : atoms ["x"] = .ok tyOne := rfl

/-- The smart constructor `lan` of Syntax.lean returns `tySum`, so the fixture is canonical.
The fixture is test data of test/finite_normalize_test.ml, and it states no proposition of docs/metatheory.md.
-/
example : lan [("k", tyA)] = .ok tySum := rfl

/-- The smart constructor `lan` of Syntax.lean returns `tyOneSum`, so the fixture is canonical.
The fixture is test data of test/finite_normalize_test.ml, and it states no proposition of docs/metatheory.md.
-/
example : lan [("a", tyOne)] = .ok tyOneSum := rfl

/-- The smart constructor `ran` of Syntax.lean returns `tyTwo`, so the fixture is canonical.
The fixture is test data of test/finite_normalize_test.ml, and it states no proposition of docs/metatheory.md.
-/
example : ran [("a", tyA), ("b", tyA)] = .ok tyTwo := rfl

/-- `tagCase` is the term of test/finite_normalize_test.ml lines 51 and 52.
It is a `case` of a `tag` at the type `tyOneSum`, and the one branch is the payload variable.
-/
def tagCase : Term := .«case» (.tag "a" (.atom "x")) tyOneSum [("a", .var 0)]

/-- `sectionProject` is the term of test/finite_normalize_test.ml line 54.
It projects the label `b` out of a two field section at the type `tyTwo`.
The field order of the source is reversed, so the canonical order runs as well.
-/
def sectionProject : Term :=
  .project (.«section» [("b", .atom "y"), ("a", .atom "x")]) tyTwo "b"

/-- `neutralCase` is the term `neutral_case` of test/finite_normalize_test.ml lines 47 and 48.
The scrutinee is a variable, so the reduction of the branch body stops at the neutral form.
-/
def neutralCase : Term := .«case» (.var 0) tySum [("k", .var 0)]

/-- `innerRedex` is the term `inner` of test/finite_normalize_test.ml line 60.
It is a `case` of a `tag` under one branch binder, so it is a redex.
-/
def innerRedex : Term := .«case» (.tag "k" (.var 0)) tySum [("k", .var 1)]

/-- `neutralBranchRedex` is the term of test/finite_normalize_test.ml lines 61 and 62.
It holds `innerRedex` under the branch of a neutral `case`.
-/
def neutralBranchRedex : Term := .«case» (.var 0) tySum [("k", innerRedex)]

/-- `shifting` is the term of test/finite_normalize_test.ml line 67.
The payload of the inner `tag` is the outer bound variable, so the shift must keep it.
-/
def shifting : Term :=
  .«case» (.tag "k" (.var 0)) tySum
    [("k", .«case» (.tag "k" (.atom "x")) tySum [("k", .var 1)])]

/-- `shiftingUnderNeutral` is the term of test/finite_normalize_test.ml lines 68 and 69.
It holds `shifting` under the branch of a neutral `case`.
-/
def shiftingUnderNeutral : Term := .«case» (.var 0) tySum [("k", shifting)]

/-- `neutralProject` is the term of test/finite_normalize_test.ml line 74.
It projects the label `b` out of a variable, so the projection stays a projection.
-/
def neutralProject : Term := .project (.var 0) tyTwo "b"

/-- `projectOfNeutralCase` is the term of test/finite_normalize_test.ml lines 77 and 78.
It projects the label `a` out of a neutral `case` whose branch holds one redex.
-/
def projectOfNeutralCase : Term :=
  .project
    (.«case» (.var 1) tySum [("k", .«case» (.tag "k" (.var 0)) tySum [("k", .var 2)])])
    tyTwo "a"

/-- `projectOfNeutralCaseReduced` is the expected normal form of test/finite_normalize_test.ml lines 80 and 81.
The branch redex reduces and the projection of the neutral `case` remains.
-/
def projectOfNeutralCaseReduced : Term :=
  .project (.«case» (.var 1) tySum [("k", .var 1)]) tyTwo "a"

/-- The exact budget for `tagCase` is 10, as test/finite_normalize_test.ml line 52 states.
The comment at line 50 splits that budget into check 4, reduce 3, substitute 2 and one reduction of the substituted body.
The normal form is the atom `x`.
-/
example : normalize 10 [] tagCase tyOne = .ok (Term.atom "x") := rfl

/-- One unit under the exact budget the run returns `Err.resourceExhausted`.
The boundary test at test/finite_normalize_test.ml lines 43 and 44 states that rejection.
-/
example : normalize 9 [] tagCase tyOne = .error .resourceExhausted := rfl

/-- The exact budget for `sectionProject` is 8, as test/finite_normalize_test.ml line 54 states.
The comment at line 53 splits that budget into check 4 and reduce 4, since the selected field needs no extra visit.
The normal form is the atom `y`.
-/
example : normalize 8 [] sectionProject tyA = .ok (Term.atom "y") := rfl

/-- One unit under the exact budget the run returns `Err.resourceExhausted`.
The boundary test at test/finite_normalize_test.ml lines 43 and 44 states that rejection.
-/
example : normalize 7 [] sectionProject tyA = .error .resourceExhausted := rfl

/-- The exact budget for `neutralCase` is 6, as test/finite_normalize_test.ml line 56 states.
The comment at line 55 splits that budget into check 3 and reduce 3, since a neutral scrutinee blocks the substitution.
The context holds one `tySum` entry and the normal form is the input.
-/
example : normalize 6 [tySum] neutralCase tyA = .ok neutralCase := rfl

/-- One unit under the exact budget the run returns `Err.resourceExhausted`.
The boundary test at test/finite_normalize_test.ml lines 43 and 44 states that rejection.
-/
example : normalize 5 [tySum] neutralCase tyA = .error .resourceExhausted := rfl

/-- A nested redex under a neutral branch reduces, as test/finite_normalize_test.ml lines 61 to 64 state.
The fuel is the 100000 of line 31 and the normal form is `neutralCase`.
-/
example : normalize 100000 [tySum] neutralBranchRedex tyA = .ok neutralCase := rfl

/-- The shift arithmetic keeps the payload of the inner `tag`, as test/finite_normalize_test.ml lines 68 to 70 state.
The fuel is the 100000 of line 31 and the normal form is `neutralCase`.
-/
example : normalize 100000 [tySum] shiftingUnderNeutral tyA = .ok neutralCase := rfl

/-- The outer variable survives the substitution, as test/finite_normalize_test.ml lines 71 and 72 state.
The context holds `tyA` at index 0 and `tySum` at index 1.
-/
example : normalize 100000 [tyA, tySum] shifting tyA = .ok (Term.var 0) := rfl

/-- A projection of a neutral section stays a projection, as test/finite_normalize_test.ml lines 74 and 75 state.
The fuel is the 100000 of line 31 and the normal form is the input.
-/
example : normalize 100000 [tyTwo] neutralProject tyA = .ok neutralProject := rfl

/-- A projection of a neutral
`case` keeps every branch reduction, as test/finite_normalize_test.ml lines 76 to 82 state.
The fuel is the 100000 of line 31.
-/
example : normalize 100000 [tyTwo, tySum] projectOfNeutralCase tyA
    = .ok projectOfNeutralCaseReduced := rfl

end Fidelity
