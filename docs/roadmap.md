# Milestones

## M0: executable semantic laboratory (this repository)

Implement finite diagrams and Lan/Ran introduction checking. Test empty fibers,
malformed maps, and the two adjunction bijections on a bounded exhaustive model.
Deliver the scope and a visible list of unresolved theoretical obligations.

Exit: tests pass. This does not establish the full universal properties for all
finite sets, dependent type safety, Lean compatibility, or EVM correctness.

## M1: pure calculus and reference checker

Started: [explicit finite-fiber terms](finite-terms.md) have checking, closed
evaluation, checked syntactic substitution and a fuel-bounded open-term beta
normalizer that keeps neutral forms, with typed errors and shared node budgets.
`Finite_term.convert` now checks and normalizes both terms under one shared
budget and compares their canonical normal forms. This completes the executable
finite-fragment comparison step, with beta only and exhaustion as inconclusive.
The Lean package in `proofs/` mechanizes checker soundness/completeness,
weakening, substitution, evaluation preservation, substitution/environment
agreement, reduction gas and fuel properties, reduction typing, and normal
forms. Public normalization preserves typing and its output rechecks.
Status: the finite-fragment theorem inventory is mechanized, including
`normalize_agrees_with_run`: successful closed normalization agrees with `run`
at independent budgets. A successful normalization fuel bound, strong
normalization and confluence remain open. This is a nondependent Lean embedding.

Lean 4.33.1 and its axiom policy are pinned in [Lean target](lean-target.md).
The primitive inventory and computation rules are documented. The separate
[dependent reference fragment](dependent-terms.md) now implements Pi/Sigma
formation, introductions, eliminations and beta reduction, Nat/Vec constructors,
dependent context validation, substitution through types, and checked type/term
conversion. Genuine dependent examples include `Sigma (Nat, Vec (a, Var 0))`.
It has typed errors, no inference or proof search, and one budget that includes
type work. Exhaustion remains inconclusive. Nat and Vec are additional
primitives under D2, not derivations from finite Kan extensions.

Remaining work: Nat induction and the length-indexed vector eliminator,
dependent substitution/preservation and checker proofs, a dependent Lean
embedding, and justification of conversion. A model identifying dependent
Pi/Sigma with Kan extensions and the disclosed initiality assumptions remain
obligations. The finite-fragment Lean theorems do not cover the new library.

Exit: checked derivations and negative cases; substitution and preservation
proofs for the implemented fragment; a precise remaining gap to Lean. If a
derivation needs a new primitive, revisit the core claim instead of concealing it.

## M2: Lean-strength logical account

Cover universes, inductive families, propositions, quotients and declared axioms.
Give a translation with typing and computation preservation. Establish the
checker metatheory against a precise theory. A sample corpus is regression
evidence; it does not replace an expressiveness proof.

## M3: executable extraction and EVM vertical slice

Define the computational fragment, proof erasure, effect semantics and typed IR.
Pin an EVM fork, ABI and storage layout. Compile a checked bounded-counter
contract with invariant 0 <= counter <= limit. Specify rejection of overflowing
updates, malformed calldata and failed execution. Differential-test source and
bytecode traces, including storage and revert behavior. Formalize each lowering
pass's obligation; do not call test coverage a compiler-correctness proof.

## M4: performance and usability

Add surface elaboration, checked module artifacts and optimized derived forms.
Measure before adding parallelism or complex caches. Proof-heavy benchmarks and
ordinary executable benchmarks must both remain visible.

### Benchmark protocol

Record CPU, OS, memory, power mode, tool versions, source/artifact hashes, cache
state, exact commands, and at least 10 timed samples after a declared warm-up.
Publish raw samples, median, p95, peak RSS, output size and contract gas where
applicable. Declare the percentile calculation. Avoid mixing process startup
with in-process throughput measurements without labeling them.

Use pinned `ocamlc` and `ocamlopt` baselines separately. Compare equivalent
executable algorithms and data sizes, documenting target differences. Report
front-end and backend timings independently; an OCaml executable and EVM
bytecode are not equivalent outputs. No speed result exists at M0.

Measure clean full-source builds, warm no-change builds, implementation edits,
interface edits, proof edits and backend-only runs. Include deep conversion,
large inductive eliminations and failed obligations. Record proof search and
certificate checking costs; cached proofs cannot stand in for fresh checking.

The proposed release gate is median and p95 no slower than the selected OCaml
baseline for each predeclared comparable workload, with full results for
proof-heavy workloads that have no fair OCaml analogue. Ratify the corpus and
baseline before measuring; do not change them after observing a slow result.
