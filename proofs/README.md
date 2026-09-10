# Finite-fragment Lean proofs

Reusable Lean 4.33.1 package for kan-evm's nondependent finite-term embedding.
The separate OCaml `Dependent_term` library is not represented in this package;
none of the theorem claims below apply to its dependent syntax.
Build from the repository root:

```sh
lake +leanprover/lean4:v4.33.1 --dir proofs build
lake +leanprover/lean4:v4.33.1 --dir proofs env lean proofs/Axioms.lean
lake +leanprover/lean4:v4.33.1 --dir proofs env lean proofs/test/Agreement.lean
lake +leanprover/lean4:v4.33.1 --dir proofs env lean proofs/test/Conversion.lean
```

A downstream Lake project can use the local package:

```lean
import Lake
open Lake DSL
package client
require «kan-evm-proofs» from "/absolute/path/to/kan-evm/proofs"
@[default_target]
lean_lib Client
```

In `Client.lean`, `import KanEvmProofs` exposes `normalize_preserves_type`,
`normalize_output_checks`, `normalize_normal_form`, and
`normalize_agrees_with_run`. It also exposes `convert`, `convert_success_iff`,
`convert_true_iff`, `convert_inputs_typed`, and `convert_agrees_with_run`.
The conversion model uses one shared fuel budget and a proved structural
comparator, including annotations. The package pins kan-tactics and its transitive
dependency in `lake-manifest.json`.

The 42 names in `Axioms.lean` depend only on `propext`, `Classical.choice`,
and `Quot.sound`. See [validation](../docs/validation.md#m1-finite-conversion)
for measured results and [FIDELITY.md](FIDELITY.md) for embedding differences.
`normalize_agrees_with_run` equates a successful closed normal form with the
quoted `run` value, assuming both calls succeed at independent budgets. Strong
normalization, a successful normalization fuel bound, and confluence are unproved.
`convert_agrees_with_run` equates the quoted results of two successful closed
executions when conversion returns true. Both successful runs are premises;
this does not prove a successful fuel bound or correctness against a
declarative conversion judgment.
