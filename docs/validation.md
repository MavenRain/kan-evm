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
