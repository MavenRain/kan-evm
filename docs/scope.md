# Scope decision — 2026-09-05

## Meaning of the requirements

1. **Kan-only logical core.** All logical constructors must have derivations from
   an explicitly specified Kan calculus. Binding, contexts, judgment forms and
   universe bookkeeping must be disclosed as structural infrastructure. Any
   additional axiom or primitive must be listed; calling it an encoding is not
   sufficient. Surface notation and backend IRs may contain derived constructs.
2. **Lean-level logical strength.** Target Lean 4's safe logical core, including
   universes, dependent functions, inductive families and elimination, Prop and
   quotients. Specify an axiom policy matching the source theory used in each
   comparison. Unsafe execution is not admitted into proofs. Tactics and macros
   are tooling milestones, not evidence of logical expressiveness.
3. **OCaml-class speed.** A benchmark acceptance criterion on pinned machines,
   compiler versions, workloads and compilation modes. No universal latency or
   complexity claim. Count checking and automation in clean source builds;
   separately report cached imports and backend-only performance.
4. **EVM target.** Executable entry points must have computational content and a
   specified ABI and storage layout. The proof language may contain noncomputable
   definitions, which cannot leak into executable terms. Pin a fork before code
   generation and charge gas according to that fork.

## Trust boundary

The future elaborator and tactics produce explicit certificates for an independent
kernel. No unchecked certificate, hole, external solver answer, or user axiom may
silently become a proved theorem. Record declared axioms transitively.

Source type safety, logical consistency relative to assumptions, compiler
correctness, and contract security are separate claims. State the assumptions
of each. A proof of a source invariant does not by itself establish that the
deployed bytecode maintains it. Imported artifacts require authenticated content
and a documented checking policy; a cache hit is not intrinsically trusted.

## Runtime design constraints

- Separate mathematical naturals from EVM 256-bit modular words. Checked
  arithmetic returns explicit errors unless a proof discharges the condition.
- Model storage changes, external calls, adversarial callbacks, revert, and
  out-of-gas in execution semantics. Choose an effect discipline after the pure
  calculus; do not presume Kan extensions imply reentrancy safety.
- Express correctness over successful and failed executions. Termination of
  mathematical recursion does not guarantee completion within transaction gas.
- Define proof erasure and permitted elimination from propositions before
  optimization. Runtime behavior must not depend on erased evidence.
- Specialization and recognized derived constructors are allowed only with a
  semantics-preservation obligation. Their gas and code-size costs are measured.

## Sources

- [Lean type system](https://lean-lang.org/doc/reference/latest/The-Type-System/)
  identifies the current comparison target's logical constructors.
- [Lean elaboration and compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
  describes independent kernel checking. Pin a Lean release at milestone M1;
  these moving documentation links do not pin a theory version.
- [OCaml native compilation](https://ocaml.org/manual/native.html) distinguishes
  native compilation from bytecode compilation and its cost tradeoffs.
- [Ethereum EVM](https://ethereum.org/developers/docs/evm/) describes the target
  execution model and gas metering.
