# Kan EVM research prototype

Investigate an EVM-targeting language whose logical constructors derive from a
Kan-extension core, with Lean 4 logical expressiveness and OCaml-class measured
compilation performance. These are acceptance criteria, not current capabilities.

Current status: **M0 complete; first M1 finite-term slice implemented**. The OCaml library
validates finite diagrams and checks introductions and eliminations for their
left and right Kan extensions. It is not a dependent type checker, proof kernel,
or EVM compiler. Finite sets are supplied as metatheoretic inputs; this does not
establish that they can be derived in the proposed language.

The separate `Finite_term` library adds explicit Lan/Ran terms, annotated
eliminations, typed checking errors, budgeted closed evaluation and checked
capture-avoiding substitution. It remains
a nondependent finite-fiber fragment; M1's metatheory and dependent constructors
are open. See the [primitive inventory and rules](docs/finite-terms.md).

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
