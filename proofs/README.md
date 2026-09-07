# Finite-fragment Lean proofs

Reusable Lean 4.33.1 package for kan-evm's nondependent finite-term embedding.
Build from the repository root:

```sh
lake +leanprover/lean4:v4.33.1 --dir proofs build
lake +leanprover/lean4:v4.33.1 --dir proofs env lean proofs/Axioms.lean
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

In `Client.lean`, `import KanEvmProofs` exposes the completed metatheory,
including `normalize_preserves_type`, `normalize_output_checks`, and
`normalize_normal_form`. The package pins kan-tactics and its transitive
dependency in `lake-manifest.json`.

The 33 names in `Axioms.lean` depend only on `propext`, `Classical.choice`,
and `Quot.sound`. See [validation](../docs/validation.md#m1-mechanization)
for measured results and [FIDELITY.md](FIDELITY.md) for embedding differences.
Normalization/evaluation agreement remains open in `NormalizeAgree.lean`,
which contains helpers only. Strong normalization, a successful normalization
fuel bound, and confluence are not proved.
