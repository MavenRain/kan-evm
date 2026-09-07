# M0 validation - 2026-09-05

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

## M1 checked substitution - 2026-09-05

Environment: OCaml 5.2.1, Dune 3.24.2. `opam exec -- dunecho test` exited 0.
All three custom test executables were also invoked directly and exited 0.
The existing finite-model and finite-term suites retain the results above;
the new executable reports:

```text
_build/default/test/finite_substitution_test.exe
PASS 6983 substitution typing and evaluation comparisons
PASS finite substitution, capture avoidance and resource limits
```

The deterministic corpus combines four replacement/result types (two atom sets,
a singleton-fiber Lan and a two-field Ran) with four contexts: empty, one atom
variable, two same-type atom variables and two different-type atom variables.
Terms combine context variables, introductions, Cases and projections in the
bounded shapes defined by the test generator. Each substitution result is
checked in the reduced context. Both sides of the substitution/evaluation
equation are closed using Case binders and evaluated; this closing operation
does not call syntactic substitution. Same-type outer variables receive distinct
atom values so capture can change the observable result.

Separate regression cases check nested binders inside both body and replacement,
free-index shifting, removal of the nearest context entry, source field order,
empty fibers, malformed inputs including unused replacements, and exact fuel
boundaries including repeated and unused occurrences. The corpus is not an
exhaustive syntax enumeration or a substitution/preservation proof. Node fuel
does not bound host stack, type operations or allocation.

## M1 normalization slice - 2026-09-06

Environment: OCaml 5.2.1, Dune 3.24.2. `opam exec -- dunecho build` reported
0 errors and 0 warnings. All four custom test executables were invoked directly
and exited 0. Their PASS lines are:

```text
_build/default/test/finite_kan_test.exe
PASS malformed diagrams
PASS introductions and eliminations
PASS 39 exhaustive finite adjunction scenarios

_build/default/test/finite_term_test.exe
PASS finite term checking, beta evaluation, binders and resource limits

_build/default/test/finite_substitution_test.exe
PASS 6983 substitution typing and evaluation comparisons
PASS finite substitution, capture avoidance and resource limits

_build/default/test/finite_normalize_test.exe
PASS 53 closed normal form and value comparisons
PASS 415 open term recheck and idempotence comparisons
PASS finite normalization, neutral forms, canonical order and resource limits
```

The normalization corpus reuses the substitution generator over four types (two
atom sets, a singleton-fiber Lan and a two-field Ran) and six contexts: empty,
one atom variable, one Lan variable, two different atom variables, one Ran
variable and one two-fiber Lan variable. It also builds Cases annotated with a
two-fiber Lan. Their two branches bind payloads of different types, and their
bodies range over the payload variable and the closed atoms, so a wrong branch
or a mislaid payload changes the result. Branch bodies are supplied in reversed
label order. Every closed corpus normal form equals the term form of the value
that `run` returns. Every open corpus normal form rechecks at its expected type
in its context and is unchanged by a second normalization. Separate cases pin
neutral Case and Project forms, a nested redex inside a branch of a neutral
Case, the shift arithmetic for a Case of a Tag under an outer binder, canonical
output order for unsorted sections and branches, rejected inputs that return
`Missing_label`, `Unexpected_label`, `Type_mismatch` and `Invalid_atom` instead
of a term, and three exact fuel boundaries: 10, 8 and 6 units, each of which
returns `Resource_exhausted` with one unit less.

Limits: the corpus is bounded and generated, not an exhaustive enumeration of
the syntax. These results are executable evidence, not proofs of preservation,
confluence or strong normalization. There is no eta rule, so normal forms are
canonical only up to beta and label order. The normalizer does not recheck its
own output; the tests do. Node fuel bounds visited term nodes only, not host
stack, allocation, sorting or type operations.


## M1 mechanization

Validated 2026-09-06 with Lean 4.33.1 and the kan-tactics revision in
`proofs/lake-manifest.json`. The package builds every proof submodule and the
public `KanEvmProofs` root. No Lean errors or warnings were reported.

```sh
lake +leanprover/lean4:v4.33.1 --dir proofs build
lake +leanprover/lean4:v4.33.1 --dir proofs env lean proofs/Axioms.lean
```

The axiom command's source path is relative to the calling repository root.
Final full-build line:

```text
Build completed successfully (20 jobs).
```

The 30 completed inventory theorem names and three public normalization
corollaries report these transitive dependencies:

```text
'ty_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'canonical_beq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'budget_monotone_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'budget_monotone_shift' depends on axioms: [propext]
'budget_monotone_sub' depends on axioms: [propext]
'budget_monotone_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound]
'budget_monotone_reduce' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_gas_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_cost_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'reduce_step_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_error_not_typable' depends on axioms: [propext, Classical.choice, Quot.sound]
'check_error_choice_varies' depends on axioms: [propext, Classical.choice, Quot.sound]
'weakening_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'substitution_at_depth' depends on axioms: [propext, Classical.choice, Quot.sound]
'substitution_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'substitute_budget_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'evaluate_preserves_type' depends on axioms: [propext, Classical.choice, Quot.sound]
'run_never_expected_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'run_budget_two_size' depends on axioms: [propext, Classical.choice, Quot.sound]
'shift_preserves_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'evaluate_sub_env' depends on axioms: [propext, Classical.choice, Quot.sound]
'evaluate_sub_budget_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'reduce_gas_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound]
'reduce_gas_unused' depends on axioms: [propext, Classical.choice, Quot.sound]
'reduce_fuel_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound]
'reduce_preserves_type' depends on axioms: [propext, Classical.choice, Quot.sound]
'normalize_is_check_then_reduce' depends on axioms: [propext, Classical.choice, Quot.sound]
'reduce_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'normalize_preserves_type' depends on axioms: [propext, Classical.choice, Quot.sound]
'normalize_output_checks' depends on axioms: [propext, Classical.choice, Quot.sound]
'normalize_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The proof-source scan found no proof placeholders, added axioms, unsafe or
partial declarations, native decision shortcuts, foreign implementations, or
exception primitives. All authored proofs use term mode, with no tactic blocks.
The compiled `Fidelity.lean` examples retain the measured fuel boundaries 10,
8, and 6 and the neutral-form examples. These examples and `FIDELITY.md` connect
the embedding to OCaml; they do not prove equivalence of the two implementations.

A separate Lake client required the local `proofs/` package and imported
`KanEvmProofs`. Its build checked `check_sound`, `substitution_at_depth`,
`normalize_preserves_type`, `normalize_output_checks`, and
`normalize_normal_form`, and exited 0. The initial client check detected that
the submodule-only Lake glob omitted the root module. The package now uses
`andSubmodules` so both the root and all submodules compile.

The OCaml gate `opam exec --switch=zxcaml-p1 -- dune runtest --force --root .`
exited 0. All four runners retained the nine PASS lines recorded above,
including 6983 substitution comparisons, 53 closed normalization comparisons,
and 415 open-term comparisons.

Remaining: `normalize_agrees_with_run` (section 11.5) is not yet declared.
`NormalizeAgree.lean` contains helper lemmas only. Claim C7 remains open:
no successful normalization fuel bound is proved. Strong normalization,
confluence, dependent calculus, and EVM compilation are also unproved.
The three public normalization corollaries assume a successful result and
therefore make no termination or successful-fuel claim.
Row Lemma2b holds under two names: `reduce_step_charge` of
`proofs/KanEvmProofs/Budget.lean` states the charge of a case of a tag, and
`reduce_rest_lt` of `proofs/KanEvmProofs/NormalizeCore.lean` states that each
entered node spends one unit of the budget.
