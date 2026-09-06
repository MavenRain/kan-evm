# Lean target for kan-evm

This document pins the Lean comparison release. It lists the safe kernel
features that count toward the comparison, what the safe core excludes,
and the remaining gap table. Read it after `docs/calculus.md` and
`docs/finite-terms.md`. It does not restate the kan-evm rules; it states
the Lean side of the comparison only.

## 1. Pinned release

Recommendation: Lean v4.33.1. It is the newest stable release at pin time
(2026-09-06). "Stable" means a tagged release, not a release candidate.

Verified (WebFetch of https://github.com/leanprover/lean4/releases,
2026-09-06, quoting the exact "released this ..." text per tag):
v4.33.1 released 2026-08-21; v4.33.0 released 2026-08-10; v4.32.2
released 2026-07-28. A first fetch of the same URL returned a different,
internally inconsistent result (wrong year, wrong patch number) and is
rejected in favor of the second, quoted fetch.

Local elan toolchains (v4.31.0, v4.33.0-rc1, v4.30.0-rc1) are not
candidates: v4.33.0-rc1 is a release candidate, and the other two predate
v4.33.1.

Policy: re-pin at the start of each later slice, with the new version,
date, and reason recorded the same way.

## 2. Safe kernel features

Each line is a feature Draft C must match or explicitly deviate from. This
document cites the reference-manual section it checked each line against.

**Universe levels.** `Sort u` is the universe at level `u`; `Prop`
abbreviates `Sort 0`; `Type u` abbreviates `Sort (u + 1)`. The Pi-type rule uses `imax`. For `A : Sort u` and `B : Sort v`, `(x : A) -> B`
has sort `Sort (imax u v)`. `imax u v` is `0` when `v` is `0`, and `max u v`
otherwise, so a proposition that quantifies over any type stays a proposition. Universes are not cumulative. Checked against
https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/
D3 sets kan-evm M1 to no universes; this section is the target for the
slice that adds them.

**Dependent functions.** `(x : A) -> B x` is the base type former.
Checked against the URL above (Pi sort rule) and against
https://lean-lang.org/doc/reference/latest/The-Type-System/ (application,
beta).

**Inductive types.** Families: indices vary across occurrences of the
type constructor, parameters stay uniform. Mutual types: parameters and
universe levels must match, positivity applies across the whole block.
Nested types: a constructor argument may contain the type being defined
inside another type former, under the same positivity rule. Structures
with eta: a structure is a single-constructor inductive type
(checked against https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/),
and the kernel treats a structure value as equal to the tuple of its own field
projections (checked against https://lean-lang.org/doc/reference/latest/The-Type-System/,
the page that carries the eta rule). Positivity: the type being defined may appear only in
strictly positive positions in constructor argument types. Universe
constraints: each constructor's argument types must live in universes
compatible with the inductive type's own universe. Checked against
https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/

**Recursors.** Each inductive type has a recursor: one minor premise per
constructor, reduced by the iota rule when applied to a constructor.
Checked against the Inductive Types URL above and against The Type
System page (iota reduction). Kan-evm's `Case` on `Tag` is this shape for
the finite label-indexed fragment: `Case` is the recursor, the branches
are the minor premises, `Tag` is the constructor.

**Quotients.** `Quot` is the primitive quotient former, over any relation
(not required to be an equivalence relation). `Quot.mk` injects an
element. `Quot.lift` lifts a function, given a proof it respects the
relation. `Quot.ind` proves a property of every quotient element by
proving it for every `Quot.mk` value. `Quot.sound` asserts that related
elements are equal (one of the three standard axioms, below). Quotient
reduction: `Quot.lift f h (Quot.mk r a)` is definitionally equal to
`f a`. Checked against
https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/

**Definitional equality.** Beta: function abstraction applied to an
argument reduces by substitution. Eta: a function equals the abstraction
over its own application; a structure value equals the tuple of its own
projections. Iota: a recursor on a constructor reduces to the matching
minor premise. Delta: a defined constant unfolds to its value. Zeta: a
`let`-bound variable unfolds to its bound value. Proof irrelevance: any
two proofs of the same proposition are definitionally equal. Quotient
reduction: as above. Checked against
https://lean-lang.org/doc/reference/latest/The-Type-System/

**Nat and String literal reduction.** The kernel has a fast path for `Nat` and
`String` literals. Arithmetic and string operations on literals do not
unfold through unary successor terms or character lists. UNVERIFIED: no
reference-manual page with the exact literal-reduction rule text was reached.

**The three standard axioms.** `propext`: propositions that imply each
other are equal. `Quot.sound`: related elements are equal in the
quotient. `Classical.choice`: a nonempty type has an element, without
constructive evidence of which one. A proof that depends on no axioms,
or only on these three, is accepted as sound under Lean's usual trust
model. Checked against https://lean-lang.org/doc/reference/latest/Axioms/

**Axiom accounting policy.** Run `#print axioms <name>` on every
top-level theorem before it counts as done. The command reports the full
transitive axiom set, not just the axioms named in the proof term
directly. Checked against the Axioms URL above. Policy for the D5
mechanization, the next M1 slice: no axiom beyond the three above.
`sorryAx` anywhere in the transitive set fails the theorem, with no
exception. `native_decide` anywhere in the set must be disclosed and
re-derived without it, because it trusts the compiler, not the kernel.

## 3. What the safe core excludes

The safe core excludes: `unsafe` definitions (the kernel does not
type-check or reduce through them); `partial` definitions (no
termination check); `@[implemented_by]` (swaps in a different
implementation the kernel never sees); `extern` definitions (foreign
code outside the kernel's view); `opaque` definitions whose underlying
value came from an unsafe or extern path; `sorryAx`; `native_decide` and
`Lean.ofReduceBool` (trust the compiler, not the kernel).

UNVERIFIED: no reference-manual page stating this exclusion list in one
place was reached. Two WebFetch attempts, against
https://lean-lang.org/doc/reference/latest/Run-Time-Code/ and
https://lean-lang.org/doc/reference/latest/Definitions/, each returned
only a table of contents, not body text. The list above states each
construct's commonly documented behavior and stays unverified against
the manual text until a fetch succeeds.

The D5 mechanization, the next M1 slice, must disclose any use of these
next to its axiom list (section 2), and the disclosure counts as a gap,
not as done.

## 4. Remaining gap table

| Lean feature | kan-evm status | Obligation that closes it |
|---|---|---|
| Universe levels (`Sort u`, `imax`) | Open. D3 sets M1 to no universes. | Add universe judgments and the `imax` Pi rule at M2. |
| Dependent functions | In fragment, non-dependent only (`Ran`/`Project`). Dependent Pi is specified in Draft C. | Implement Draft C's Ran-along-`p` formation, introduction, elimination, beta. |
| Inductive families | Open beyond the finite label-indexed fragment. | Draft C's D2 primitive inductive-family former, with the disclosed initiality assumption. |
| Mutual and nested inductive types | Open. | Not scoped for M1; record as M2+ in the roadmap. |
| Structure eta | Open; kan-evm has no eta at M1 (D4). | D4 defers Section/Ran eta to a later slice; disclosed gap until then. |
| Recursors | In fragment for the finite case (`Case` on `Tag`). | Draft C's Sigma/Pi elimination forms generalize this to the dependent case. |
| Quotients (`Quot`, `Quot.sound`) | Open; no quotient former in kan-evm. | Not scoped for M1 or Draft C; record as open in the roadmap. |
| Definitional equality: beta, iota | In fragment. Iota is `Case`-of-`Tag`; beta is `Project`-of-`Section`, which is `app` of `lam` at an enumeration (see the correspondence table in docs/dependent-calculus.md:137-145). Both steps run in `normalize` (lib/finite_term.ml:187-190, lib/finite_term.ml:205-206). | None; closed for the finite fragment, which has no other function former. |
| Definitional equality: eta | Open (D4: beta only at M1). | D4's disclosed gap; close when Pi/Sigma eta is scheduled. |
| Definitional equality: delta, zeta | Open; kan-evm has no let-binding or named-constant unfolding construct. | Add `let` and top-level definitions with delta/zeta rules; scope not yet assigned. |
| Proof irrelevance | Open; kan-evm has no `Prop`-like sort (D3, D6). | Depends on D3 (universes) and D6 (identity types); not scoped for M1. |
| Nat and String literal reduction | Open; kan-evm has no `Nat` or `String` primitive with literal reduction. | D2's Nat induction principle is a prerequisite; literal reduction is not yet scoped. |
| The three standard axioms | Applies to the D5 mechanization, the next M1 slice, under `proofs/`. A proof term may depend on `propext`, `Quot.sound` and `Classical.choice`, and on no other axiom. | The mechanization slice proves the metatheory.md propositions about the implemented finite fragment and reports its axiom set with `#print axioms`. |
| Axiom accounting (`#print axioms`) | Applies to the D5 mechanization slice. Every top-level theorem it adds must pass the check before it counts as done. | Run on every theorem the slice adds, per the policy in section 2. |
| Safe-core exclusions (`unsafe`, `partial`, `sorryAx`, `native_decide`) | Applies to the D5 mechanization slice. Its proofs must not depend on any excluded construct, and must not use `sorry`. | The slice's theorems must type-check with none of `unsafe`, `partial`, `sorryAx` or `native_decide` in the transitive axiom or definition set. |
