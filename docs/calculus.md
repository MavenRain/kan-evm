# Candidate calculus: decisions and open obligations

This is a research specification, not a completed type theory. Rules below have
their stated semantic scope; none establishes consistency of an unrestricted
Kan-only dependent calculus.

## Established starting model

Let A and B be finite discrete categories, f : A -> B, and X : A -> FinSet.
Reindexing f* has adjoints Lan_f and Ran_f:

    Lan_f ⊣ f* ⊣ Ran_f
    (Lan_f X)(b) = Σ (a in A with f(a)=b), X(a)
    (Ran_f X)(b) = Π (a in A with f(a)=b), X(a)

The equality here is equality of finite labels. It is not an encoding of
intensional identity types. Finite sets and their elements live in the OCaml
host model; they are not claimed to be derived Kan terms.

At a fixed b:

    f(a)=b    x ∈ X(a)
    ------------------------- Lan introduction
    tag(a,x) ∈ (Lan_f X)(b)

    for each a with f(a)=b, s(a) ∈ X(a)
    --------------------------------- Ran introduction
    s ∈ (Ran_f X)(b)

Lan elimination applies a branch to the tag and payload. Ran elimination selects
a section component. Empty indexing fibers yield an empty Lan and a singleton
Ran (the empty section). A nonempty indexing fiber containing an empty X(a)
has no Ran sections. Different tags with equal payload labels remain distinct.

The implementation validates introductions. OCaml callbacks used for Lan
elimination are not checked object-language functions. Abstract values certify
the existence of a validated introduction but do not encode diagram identity in
an OCaml phantom type; elimination is self-contained and never reinterprets a
value against a new diagram. This API is not a substitute for dependent typing.

## Candidate dependent syntax boundary

The [finite-term specification](finite-terms.md) now supplies an executable
nondependent syntax with checked branches and environment-based evaluation.
The separate [dependent reference fragment](dependent-terms.md) implements
Pi/Sigma and Nat/Vec constructors with dependent checking and beta conversion.
It does not discharge the model or dependent metatheory obligations below.

The [M1 dependent specification](dependent-calculus.md) supplies judgments without
universes, as ruled by D3. The M2/full-language target must also provide universe
levels. Candidate notation for that target:

    Γ context       Γ ⊢ A : U_l       Γ ⊢ t : A
    Δ ⊢ σ : Γ       Γ ⊢ t ≡ u : A

These are placeholders, not assumed formation rules. A fibered model must
explain which Kan extensions exist, at what size, how context extension works,
and how substitution commutes with the proposed constructors. Do not introduce
arbitrary category equality as a decision procedure for term conversion.

## Obligations before calling this a language kernel

| Obligation | Required evidence | Status |
|---|---|---|
| Primitive inventory | Complete syntax and rules, including all generators | Finite fragment and initial dependent subset documented; Nat/Vec eliminators and M2 generators remain open |
| Dependent products/sums | Formation, intro, elim, beta/eta and substitution | Pi/Sigma checking, beta and substitution implemented; eta deferred, dependent proofs and categorical model open |
| Universes | Stratification, level constraints, closure without type-in-type | Open |
| Equality | Intensional identity and specified decidable conversion | Open |
| Induction | Nat induction and indexed vector elimination, not just Church encodings | Extra Nat/Vec formation and constructors implemented; induction eliminators remain open under the disclosed initiality assumptions |
| Prop and quotients | Lean-compatible eliminations, irrelevance and computation policy | Open |
| Safety | Weakening, substitution, preservation and appropriate progress theorem | Open |
| Conversion algorithm | Soundness, completeness for chosen equality, termination | Checked normalize-and-compare implemented for the finite and initial dependent fragments with shared budgets; declarative soundness/completeness, confluence and strong normalization remain open |
| Lean embedding | Typing and reduction preservation with explicit axiom accounting | Open |
| Efficient representation | Correctness of sharing and specialized derived forms | Open |

A theorem that two categorical constructions are isomorphic does not make them
definitionally equal. Every proposed optimization or encoding must specify
whether its equality is judgmental, propositional, or a semantic isomorphism.

General Kan extensions need not exist; neither existence nor computability may
be assumed for arbitrary diagrams. If induction requires an extra existence or
initiality principle, record it as an additional assumption and assess whether
it violates the Kan-only criterion before extending the implementation.

## Mathematical references

- [Riehl, Category Theory in Context](https://math.jhu.edu/~eriehl/context/):
  Kan extensions, adjunctions and their universal properties.
- [Gratzer and Sterling, Syntactic categories for dependent type theory](https://www.danielgratzer.com/papers/syntactic-categories-for-dependent-type-theory.pdf):
  categorical presentations of dependent theories and adequacy. This is relevant
  background, not a proof that this candidate calculus supports Lean.
