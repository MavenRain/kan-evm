# Finite-fragment Lean proofs

Reusable Lean 4.33.1 package for kan-evm's nondependent finite-term embedding.
Build from the repository root:

```sh
lake +leanprover/lean4:v4.33.1 --dir proofs build
lake +leanprover/lean4:v4.33.1 --dir proofs env lean proofs/Axioms.lean
lake +leanprover/lean4:v4.33.1 --dir proofs env lean proofs/test/Agreement.lean
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
`normalize_agrees_with_run`. The package pins kan-tactics and its transitive
dependency in `lake-manifest.json`.

The 34 names in `Axioms.lean` depend only on `propext`, `Classical.choice`,
and `Quot.sound`. See [validation](../docs/validation.md#m1-mechanization)
for measured results and [FIDELITY.md](FIDELITY.md) for embedding differences.
`normalize_agrees_with_run` equates a successful closed normal form with the
quoted `run` value, assuming both calls succeed at independent budgets. Strong
normalization, a successful normalization fuel bound, and confluence are unproved.
