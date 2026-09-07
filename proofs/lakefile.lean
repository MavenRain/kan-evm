import Lake
open Lake DSL

package «kan-evm-proofs» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «kan-tactics» from git
  "https://github.com/MavenRain/kan-tactics.git" @ "3317f7ac5a22ca0d85b90a3286b8fe0c36cea8ac"

@[default_target]
lean_lib «KanEvmProofs» where
  roots := #[`KanEvmProofs]
  globs := #[.andSubmodules `KanEvmProofs]
