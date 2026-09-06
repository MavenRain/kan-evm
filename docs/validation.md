# M0 validation — 2026-09-05

Command: `dune runtest` from the project root.
Environment: OCaml 5.2.1, Dune 3.24.2. Exit code: 0.

```text
PASS malformed diagrams
PASS introductions and eliminations
PASS 39 exhaustive finite adjunction scenarios
```

The 39 scenarios cover 13 families (zero, one or two source indices, with
zero, one or two atoms per fiber) and three choices of Y (zero, one or two
elements), for a map to a singleton codomain. Each scenario enumerates every
function on both sides of each adjunction and checks both round trips and
hom-set cardinalities. Separate cases exercise a codomain with an empty indexing
fiber, invalid introductions and malformed diagrams.

These are bounded semantic tests, not metatheory proofs. Naturality of the
adjunction bijections, arbitrary finite maps, dependent syntax, universes,
induction, quotients, proof erasure and EVM execution are not established by
this test suite. Compilation speed has not been benchmarked.

## M1 finite-term slice - 2026-09-05

Environment: OCaml 5.2.1, Dune 3.24.2. `dunecho test` exited 0.
Because its summary did not count this custom test runner, both executables
were also invoked directly and each exited 0:

```text
_build/default/test/finite_kan_test.exe
PASS malformed diagrams
PASS introductions and eliminations
PASS 39 exhaustive finite adjunction scenarios

_build/default/test/finite_term_test.exe
PASS finite term checking, beta evaluation, binders and resource limits
```

The new tests cover canonical atom order, duplicate type labels, context lookup,
empty types and fibers, both beta computations, canonical section order, nested
payload binders, invalid unexecuted branches, missing/duplicate/extra fields,
incorrect eliminator annotations, payload type errors, and exact shared-budget
boundaries for checking and evaluation. These are regression cases, not an
exhaustive term enumeration or substitution/preservation proof. Resource limits
have the narrower scope documented in [finite terms](finite-terms.md).
