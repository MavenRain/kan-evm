import KanEvmProofs

/-! # Public normalization agreement checks

These checks import only the reusable package root. Each concrete application supplies
successful normalization and evaluation premises by computation, so a theorem with
uninhabited premises cannot pass these cases. The budgets are deliberately different.
The contract is docs/metatheory.md section 11.5; these checks add no library declarations.
-/

namespace AgreementTests

/-- The public contract accepts independent budgets without extra typing assumptions. -/
example (normalFuel runFuel : Nat) (t x : Term) (a : Ty) (v : Value)
    (hn : normalize normalFuel [] t a = Except.ok x)
    (he : run runFuel t a = Except.ok v) : x = quote v :=
  normalize_agrees_with_run normalFuel runFuel t x a v hn he

/-- Core agreement also supplies a successful evaluation of the normalized output. -/
example (gas normalFuel runFuel : Nat) (t x : Term) (a : Ty) (v : Value)
    (normalRest runRest : Nat)
    (hn : reduce gas normalFuel t a = Except.ok (x, normalRest))
    (he : evaluate runFuel [] t = Except.ok (v, runRest)) :
    x = quote v ∧ ∃ (fuel rest : Nat), evaluate fuel [] x = Except.ok (v, rest) :=
  NormAgree.agreeGas gas normalFuel t a x normalRest runFuel v runRest hn he

/-- A singleton atom type makes the payload result observable. -/
private def atomType : Ty := .atoms ["x"]

/-- The outer case binds a payload of the singleton atom type. -/
private def sumType : Ty := .lan [("a", atomType)]

/-- This is the ten-unit case redex from docs/finite-terms.md. -/
private def beta : Term :=
  .«case» (.tag "a" (.atom "x")) sumType [("a", .var 0)]

/-- Normalization pays for substitution while evaluation extends the environment. -/
example : Term.atom "x" = quote (Value.atom "x") :=
  normalize_agrees_with_run 10 8 beta (.atom "x") atomType (.atom "x") rfl rfl

/-- The section combines an atom and a nested tag in canonical type order. -/
private def sectionType : Ty := .ran [("a", atomType), ("z", sumType)]

/-- Source fields arrive in reverse order and contain a nested constructor. -/
private def unsortedSection : Term :=
  .«section» [("z", .tag "a" (.atom "x")), ("a", .atom "x")]

/-- Agreement is literal equality with the sorted quotation, including nested tags. -/
example : Term.«section» [("a", .atom "x"), ("z", .tag "a" (.atom "x"))]
    = quote (Value.«section» [("a", .atom "x"), ("z", .tag "a" (.atom "x"))]) :=
  normalize_agrees_with_run 8 9 unsortedSection
    (.«section» [("a", .atom "x"), ("z", .tag "a" (.atom "x"))]) sectionType
    (.«section» [("a", .atom "x"), ("z", .tag "a" (.atom "x"))]) rfl rfl

/-- The inner binder has a different payload, so capturing it changes the result. -/
private def nestedCase : Term :=
  .«case» (.tag "a" (.atom "x")) sumType
    [("a", .«case» (.tag "b" (.atom "y")) (.lan [("b", .atoms ["y"])])
      [("b", .var 1)])]

/-- Substitution crosses a retained binder and preserves the outer payload. -/
example : Term.atom "x" = quote (Value.atom "x") :=
  normalize_agrees_with_run 20 14 nestedCase (.atom "x") atomType (.atom "x") rfl rfl

/-- Projection reads a field from the sorted quotation of the reduced section. -/
example : Term.tag "a" (.atom "x") = quote (Value.tag "a" (.atom "x")) :=
  normalize_agrees_with_run 10 11 (.project unsortedSection sectionType "z")
    (.tag "a" (.atom "x")) sumType (.tag "a" (.atom "x")) rfl rfl

end AgreementTests
