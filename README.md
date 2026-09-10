# Kan EVM research prototype

Investigate an EVM-targeting language whose logical constructors derive from a
Kan-extension core, with Lean 4 logical expressiveness and OCaml-class measured
compilation performance. These are acceptance criteria, not current capabilities.

Current status: **M0 complete; M1 finite and initial dependent fragments implemented**. The OCaml library
validates finite diagrams and checks introductions and eliminations for their
left and right Kan extensions. This project is not a proof kernel or EVM compiler.
Finite sets are supplied as metatheoretic inputs; this does not
establish that they can be derived in the proposed language.

The separate `Finite_term` library adds explicit Lan/Ran terms, annotated
eliminations, typed checking errors, budgeted closed evaluation, checked
capture-avoiding substitution, a fuel-bounded open-term beta normalizer with
neutral forms, and checked normalize-and-compare conversion under one shared
budget. Conversion returns equality, inequality, or a typed error; exhaustion
never counts as a Boolean answer. It remains a nondependent finite-fiber fragment.
Part of M1's metatheory remains open. See the
[primitive inventory and rules](docs/finite-terms.md).

The separate [dependent reference fragment](docs/dependent-terms.md) adds
`Dependent_term`: dependent Pi/Sigma checking, lambda/application and pair/split
beta reduction, Nat/Vec constructors, capture-avoiding substitution through types,
and checked type and term conversion. It validates dependent contexts and meters
type work under the shared budget. Nat and Vec are disclosed extra primitives,
not finite Kan derivations. Their induction eliminators and the dependent
metatheory remain open; this slice has no universes, identity types or eta.

The reusable Lean 4.33.1 package in [proofs/](proofs/README.md) mechanizes
checker soundness/completeness, substitution, evaluation preservation, normalizer
typing and normal-form guarantees, and successful closed normalization/evaluation
agreement for a deep embedding of the nondependent finite fragment. Conversion proofs establish
structural comparison correctness, checked operands, and agreement with quoted
successful closed executions. Its 42 audited theorem names
depend only on `propext`, `Classical.choice`, and `Quot.sound`. A successful
normalization fuel bound, strong normalization, and confluence remain open. The
[fidelity table](proofs/FIDELITY.md) records the embedding differences.
These finite-fragment proofs do not cover `Dependent_term`.

```sh
cd kan-evm
dune runtest
```

Requires OCaml >= 4.13 and Dune >= 3.0; no external libraries. Initially validated
with OCaml 5.2.1 and Dune 3.24.2. Tests include malformed diagrams, empty fibers,
introduction/elimination behavior, and exhaustive finite adjunction checks.

- [Scope and acceptance criteria](docs/scope.md)
- [Candidate calculus and open obligations](docs/calculus.md)
- [Milestones and measurement protocol](docs/roadmap.md)
- [Finite model interface](lib/finite_kan.mli)
- [Validation evidence and limits](docs/validation.md)

Working directory name `kan-evm` is provisional. No existing language's name,
implementation, or compatibility is implied.
