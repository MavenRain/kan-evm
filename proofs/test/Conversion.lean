import KanEvmProofs

/-! # Public fueled conversion checks

Concrete equalities reduce in the kernel through the reusable package root.
The cases exercise shared fuel boundaries, validation, canonical field order,
neutral syntax, annotations, and the quoted execution agreement theorem.
-/

namespace ConversionTests

private def atomType : Ty := .atoms ["x", "y"]
private def sumType : Ty := .lan [("a", atomType)]
private def beta : Term :=
  .«case» (.tag "a" (.atom "x")) sumType [("a", .var 0)]

/-- Both atom checks and both atom reductions spend one unit each. -/
example : convert 4 [] (.atom "x") (.atom "x") atomType = .ok true := rfl
example : convert 3 [] (.atom "x") (.atom "x") atomType =
    .error .resourceExhausted := rfl
example : convert 4 [] (.atom "x") (.atom "y") atomType = .ok false := rfl

/-- The beta redex costs ten units, leaving exactly two for the right atom. -/
example : normalizeWithRest 12 [] beta atomType = .ok (.atom "x", 2) := rfl
example : convert 12 [] beta (.atom "x") atomType = .ok true := rfl
example : convert 11 [] beta (.atom "x") atomType = .error .resourceExhausted := rfl
example : convert 12 [] (.atom "x") beta atomType = .ok true := rfl

/-- Equality of invalid syntax cannot bypass either checker. -/
example : convert 3 [] (.atom "x") (.atom "bad") atomType =
    .error (.invalidAtom "bad") := rfl
example : convert 100 [] (.atom "bad") (.atom "bad") atomType =
    .error (.invalidAtom "bad") := rfl
example : convert 100 [] (.atom "bad") (.atom "x") atomType =
    .error (.invalidAtom "bad") := rfl
example : convert 1 [] (.atom "x") (.atom "bad") atomType =
    .error .resourceExhausted := rfl

private def twoSumType : Ty := .lan [("a", atomType), ("b", atomType)]
private def invalidBranch : Term :=
  .«case» (.tag "a" (.atom "x")) twoSumType [("a", .var 0), ("b", .atom "bad")]

/-- An unchosen invalid branch of the right operand remains a checking error. -/
example : convert 100 [] (.atom "x") invalidBranch atomType =
    .error (.invalidAtom "bad") := rfl

private def sectionType : Ty := .ran [("a", atomType), ("z", atomType)]
private def unsortedSection : Term := .«section» [("z", .atom "y"), ("a", .atom "x")]
private def sortedSection : Term := .«section» [("a", .atom "x"), ("z", .atom "y")]

/-- Canonical reduction removes source field ordering before comparison. -/
example : convert 12 [] unsortedSection sortedSection sectionType = .ok true := rfl
example : convert 11 [] unsortedSection sortedSection sectionType =
    .error .resourceExhausted := rfl

private def unsortedNeutral : Term :=
  .«case» (.var 0) twoSumType [("b", .var 0), ("a", .var 0)]
private def sortedNeutral : Term :=
  .«case» (.var 0) twoSumType [("a", .var 0), ("b", .var 0)]

/-- Open neutral cases canonicalize branch order, while variable identity remains exact. -/
example : convert 16 [twoSumType] unsortedNeutral sortedNeutral atomType = .ok true := rfl
example : convert 4 [atomType, atomType] (.var 0) (.var 1) atomType = .ok false := rfl

private def sumEta : Term := .«case» (.var 0) sumType [("a", .tag "a" (.var 0))]
private def singletonSectionType : Ty := .ran [("a", atomType)]
private def sectionEta : Term :=
  .«section» [("a", .project (.var 0) singletonSectionType "a")]

/-- Conversion retains neutral sums and products without eta expansion. -/
example : convert 10 [sumType] (.var 0) sumEta sumType = .ok false := rfl
example : convert 8 [singletonSectionType] (.var 0) sectionEta singletonSectionType =
    .ok false := rfl

/-- Structural comparison includes type annotations and nested field bodies. -/
example : Term.beq (.project (.var 0) (.ran [("a", .atoms ["x"])]) "a")
    (.project (.var 0) (.ran [("a", .atoms ["y"])]) "a") = false := rfl
example : Term.beq (.«case» (.var 0) sumType [("a", .atom "x")])
    (.«case» (.var 0) sumType [("a", .atom "y")]) = false := rfl

/-- The public corollary accepts independent execution budgets with no extra premise. -/
example (fuel leftRunFuel rightRunFuel : Nat) (left right : Term) (a : Ty)
    (leftValue rightValue : Value)
    (hc : convert fuel [] left right a = .ok true)
    (hl : run leftRunFuel left a = .ok leftValue)
    (hr : run rightRunFuel right a = .ok rightValue) :
    quote leftValue = quote rightValue :=
  convert_agrees_with_run fuel leftRunFuel rightRunFuel left right a leftValue rightValue
    hc hl hr

/-- The semantic corollary accepts independent successful execution budgets. -/
example : quote (Value.atom "x") = quote (Value.atom "x") :=
  convert_agrees_with_run 12 8 2 beta (.atom "x") atomType (.atom "x") (.atom "x")
    rfl rfl rfl

/-- A false result still certifies both inputs at the requested type. -/
example : HasType [] (.atom "x") atomType ∧ HasType [] (.atom "y") atomType :=
  convert_inputs_typed 4 [] (.atom "x") (.atom "y") atomType false rfl

end ConversionTests
