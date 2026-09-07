# Dependent calculus: the M1 extension specification

This document specifies the dependent extension planned for M1. It is a
specification, not a report of implemented code. The implemented code is the
nondependent finite fragment in `lib/finite_term.ml`, with rules in
[finite-terms.md](finite-terms.md). No rule below is implemented. The user
ruled on decisions D1 to D7 on 2026-09-06. This document states each ruled
option and its consequence.

## Judgments

    Γ ctx                  Γ is a well formed context
    Γ ⊢ A type             A is a type in Γ
    Γ ⊢ t : A              t has the type A in Γ
    Γ ⊢ A ≡ B type         A and B are equal types in Γ
    Γ ⊢ t ≡ u : A          t and u are equal terms of the type A in Γ

The kernel reads the third form as checking. The caller supplies the type, and
the kernel neither infers it nor searches. Both equality forms use the one
algorithm of the conversion section.

## Contexts and substitutions

A context is a list of types. Each entry may depend on the entries before it.
Variables are de Bruijn indices, and index 0 names the nearest binder. This
matches the implemented fragment (lib/finite_term.mli:30-31).

    -------- empty          Γ ctx    Γ ⊢ A type
    ⋄ ctx                   ------------------- extension
                            Γ.A ctx

The implemented fragment has the extension rule under a restriction. Its types
hold no term variables, so `Γ ⊢ A type` holds for every Γ there. The dependent
extension removes that restriction. A substitution σ from Δ to Γ is a list of
terms of the types of Γ.

    Δ ⊢ σ : Γ    Γ ⊢ A type          Δ ⊢ σ : Γ    Γ ⊢ t : A
    -----------------------          ----------------------
    Δ ⊢ A[σ] type                    Δ ⊢ t[σ] : A[σ]

`Finite_term.substitute` implements the single variable case of the term rule
(lib/finite_term.mli:46-47).

One notation convention holds for every rule below. When a type or a term
written in a context appears in a longer context, read it under the
weakening substitution, without writing the shift. For example `C` in
`Γ.(Σ_A B) ⊢ C type` appears in the elimination premise over `Γ.A.B`, and `A`
in `Γ ⊢ A type` appears in the Vec cons premise over `Γ.Nat.A`.

## Display maps and reindexing

Each type `Γ ⊢ A type` gives a context extension `Γ.A` and a projection
`p_A : Γ.A -> Γ`. Call `p_A` the display map of A. Reindexing along `p_A` is
weakening, and it acts between the fibers of the type fibration over the context
category. Two adjoints of `p_A*` give the dependent sum and the dependent
product.

    p_A* : Ty(Γ) -> Ty(Γ.A)        p_A* C = C[wk]        Σ_A ⊣ p_A* ⊣ Π_A

The requirement is the adjoint triple above. `Lan_p` and `Ran_p` are by
definition the adjoints of precomposition with p, so the names Lan and Ran
apply to `Σ_A` and `Π_A` only in a model where a type over Γ is a functor on Γ
and `p_A*` is precomposition with `p_A`. The finite discrete model of [calculus.md](calculus.md) gives the adjoint
triple `Lan_f ⊣ f* ⊣ Ran_f` for a map f of finite discrete categories with
values in FinSet (calculus.md:9-14). That model has no context category, no
context extension and no display map, and its finite sets and elements live
in the OCaml host model (calculus.md:16-18). It therefore justifies the Kan
names for the nondependent finite case only, with f in the place of p_A and
the target object b in the place of an object of Γ. This document exhibits no
model for the dependent case. The names Lan and Ran are used here under that
identification, and the identification is a requirement on any future model,
not a result.

Both adjoints must commute with substitution. That is the Beck-Chevalley
condition, stated here for `Δ ⊢ σ : Γ` and `Γ.A ⊢ B type`.

Write `σ.A` for the lift of σ to the extended context. If `Δ ⊢ σ : Γ` and
`Γ ⊢ A type`, then `Δ.A[σ] ⊢ σ.A : Γ.A`, where `σ.A` shifts every free index of
σ by one and adds index 0 for the new nearest binder. With that definition the
two stability equations read:

    Δ ⊢ (Σ_A B)[σ] ≡ Σ_{A[σ]} B[σ.A] type
    Δ ⊢ (Π_A B)[σ] ≡ Π_{A[σ]} B[σ.A] type

This document exhibits no model, so the condition is a requirement and not a
theorem here.

## Sigma as the left Kan extension along p

    Γ ⊢ A type    Γ.A ⊢ B type       Γ ⊢ a : A    Γ ⊢ b : B[a]
    -------------------------- form  ------------------------- intro
    Γ ⊢ Σ_A B type                   Γ ⊢ pair(a, b) : Σ_A B

    Γ.(Σ_A B) ⊢ C type    Γ.A.B ⊢ c : C[pair(1, 0)]    Γ ⊢ s : Σ_A B
    ---------------------------------------------------------------- elim
    Γ ⊢ split(C, c, s) : C[s]

    Γ ⊢ split(C, c, pair(a, b)) ≡ c[a, b] : C[pair(a, b)]              beta

    Γ ⊢ s : Σ_A B
    ---------------------------------- eta
    Γ ⊢ s ≡ pair(fst s, snd s) : Σ_A B

`split` binds two variables in c: index 1 is the first component, and index 0 is
the second. C is the motive, and `fst` and `snd` are `split` at the two
projection motives. The adjunction `Σ_A ⊣ p_A*` is the bijection between maps
out of `Σ_A B` in Γ and maps out of B in Γ.A. `split` is the direction that
turns a term under the two component binders into a term under the pair.

## Pi as the right Kan extension along p

    Γ ⊢ A type    Γ.A ⊢ B type       Γ.A ⊢ b : B
    -------------------------- form  ---------------------- intro
    Γ ⊢ Π_A B type                   Γ ⊢ lam(b) : Π_A B

    Γ ⊢ f : Π_A B    Γ ⊢ a : A
    -------------------------- elim   Γ ⊢ app(lam(b), a) ≡ b[a] : B[a]   beta
    Γ ⊢ app(f, a) : B[a]

    Γ ⊢ f : Π_A B
    ---------------------------------- eta
    Γ ⊢ f ≡ lam(app(f[wk], 0)) : Π_A B

The adjunction `p_A* ⊣ Π_A` is the bijection between maps into B in Γ.A and maps
into `Π_A B` in Γ. `lam` and `app` are its two directions.

## Eta at M1: the D4 decision

M1 does not implement either eta rule. The ruling on D4 is beta only, with
canonical label order in normal forms. Both eta rules stay here as the target.
This document discloses the gap against Lean: Lean has definitional eta for functions and
for structures, so a Lean term and its eta expansion are convertible there and
are not convertible here. That Lean claim is unverified here, and Draft A
verifies it against
<https://lean-lang.org/doc/reference/latest/The-Type-System/>.

## The finite fragment is the special case over a finite atom type

Fix a finite atom type `A = Atoms {a_1, ..., a_n}` and a family B given by its
n components `B(a_1)` to `B(a_n)`. Over each object γ of Γ the display map
`p_A` has one fiber, and that fiber holds the n atoms. That single target
fiber is the one the code describes (docs/finite-terms.md:9-10). Over that
fiber the two Kan extensions become a finite sum and a finite product.

    Σ_A B = B(a_1) + ... + B(a_n)          the fiber list of `Lan`
    Π_A B = B(a_1) × ... × B(a_n)          the fiber list of `Ran`

| Dependent form | Finite fragment (lib/finite_term.mli:21-28) |
|---|---|
| `A` a finite atom type | `Atoms labels` |
| `Σ_A B` | `Lan [(a_1, B_1); ...; (a_n, B_n)]` |
| `pair(a_i, x)` | `Tag (a_i, x)` |
| `split(C, c, s)` | `Case {scrutinee; scrutinee_type; branches}` |
| `Π_A B` | `Ran [(a_1, B_1); ...; (a_n, B_n)]` |
| `lam(b)` | `Section fields`, one field per fiber |
| `app(f, a_i)` | `Project {section; section_type; label}` |

`Case` eliminates the Σ over an enumeration. The first binder of `split` ranges
over n known atoms, so the rule splits into n branches, one per atom, and each
branch keeps only the payload binder. That is why a `Case` branch binds one
variable and not two. The checker checks every branch, including branches that
no execution reaches (docs/finite-terms.md:24-34). `Section` is `lam` at an
enumeration, because a function out of an enumeration is a tuple of its n
values, and `Project` is `app` at a literal atom.

The implemented fragment restricts this special case twice. The fibers B(a_i) do
not depend on the payload, because a `ty` holds no term variables. The motive C
does not depend on the scrutinee, because `Case` checks every branch against one
expected type. Removing the second restriction gives the dependent `Case`. That change needs
types that mention terms. So the first restriction must go first.

## Naturals and vectors are not finite Kan extensions

**Proposition (finite denotation).** Every type of the implemented fragment
denotes a finite set of closed values.

The proof is the induction below. Two further facts are needed for the
corollary about Nat, and they are separate from the proposition. First, every
Kan extension of the model in [calculus.md](calculus.md) is a finite sum or a
finite product over a finite fiber of finite sets (calculus.md:9-14), so no
such extension denotes an infinite set. Second, the standard presentation of
Nat is a Kan extension along a functor whose fiber is the infinite ordered
set omega. The first of these two facts, not the second, place Nat outside
the finite model.

*Paper proof, by induction on the type.* `Atoms L` denotes the labels of L,
which form a finite list. `Lan fibers` denotes the disjoint union of finitely
many fiber denotations, each finite by the induction hypothesis, and
`Ran fibers` denotes their product. Both stay finite. This proposition covers
only the implemented `Atoms`/`Lan`/`Ran` fragment. It does not cover the
dependent extension with Nat and Vec specified here. Its mechanization is
not included in the D5 scope below, which covers the propositions of
`docs/metatheory.md`; it remains a paper proof with no scheduled mechanization.

Nat denotes a countably infinite set, so by the proposition no type of the
fragment denotes Nat. More atom sets do not help, because each atom set is a
finite list of labels.

Nat is the initial algebra of the functor `F X = 1 + X` on Set. `F` is
finitary, so it preserves colimits of ω-chains. Adamek's theorem then gives
the carrier of the initial algebra as the colimit of the chain
`0 -> F 0 -> F² 0 -> F³ 0 -> ...`, which is a diagram `D : ω -> Set` on the
infinite ordered set ω. The side condition matters. A functor that does not
preserve ω-colimits gets no such presentation. That colimit is a left Kan
extension along the unique functor `! : ω -> 1`.

    Nat = (Lan_! D)(*) = colim D

Nat is therefore a Kan extension along a functor whose only fiber is infinite.
[calculus.md](calculus.md) covers finite discrete categories, and it declines to
assume existence or computability of Kan extensions for arbitrary diagrams. The
finite fiber enumeration that drives `Lan` and `Ran` in the code has no
counterpart here, because the fiber of `!` is ω.

Two gaps follow. The carrier gap: a countable colimit lies outside the finite
discrete model. The elimination gap: induction is the initiality of that algebra in the
fibered sense. For every motive over Nat, exactly one section satisfies the
two computation rules. Owning the carrier does not give that
property, so it is an extra principle. Length-indexed vectors repeat both gaps.
`Vec A n` is an inductive family over Nat. Its carrier is again an ω-colimit,
and its eliminator again needs initiality, taken in the fibration over Nat
instead of over the terminal context.

## Disclosed assumptions

calculus.md instructs: "If induction requires an extra existence or initiality
principle, record it as an additional assumption and assess whether it violates
the Kan-only criterion before extending the implementation."

**ASSUME-NAT.** A Nat type with a dependent eliminator. This is more than a
natural numbers object. A natural numbers object gives simple recursion only.
The rule below gives elimination into an arbitrary motive over Nat, which is
the fibered initiality property named above, and that is the part the finite
Kan extensions do not supply.

    ------------ form    Γ ⊢ zero : Nat    Γ ⊢ n : Nat ⇒ Γ ⊢ succ n : Nat
    Γ ⊢ Nat type

    Γ.Nat ⊢ C type   Γ ⊢ z : C[zero]   Γ.Nat.C ⊢ s : C[succ 1]   Γ ⊢ n : Nat
    ------------------------------------------------------------------------
    Γ ⊢ natrec(C, z, s, n) : C[n]

    natrec(C, z, s, zero)   ≡ z
    natrec(C, z, s, succ n) ≡ s[n, natrec(C, z, s, n)]

**ASSUME-VEC.** The indexed family Vec with two constructors and an eliminator.

    Γ ⊢ A type   Γ ⊢ n : Nat ⇒ Γ ⊢ Vec A n type
    Γ ⊢ nil : Vec A zero
    Γ ⊢ a : A   Γ ⊢ v : Vec A n ⇒ Γ ⊢ cons(n, a, v) : Vec A (succ n)

    motive     Γ.Nat.(Vec A 0) ⊢ C type
    nil case   Γ ⊢ cn : C[zero, nil]
    cons case  Γ.Nat.A.(Vec A 1).C[2, 0] ⊢ cc : C[succ 3, cons(3, 2, 1)]
    target     Γ ⊢ n : Nat    Γ ⊢ v : Vec A n
    ------------------------------------------------------------------
    Γ ⊢ vecrec(C, cn, cc, n, v) : C[n, v]

    vecrec(C, cn, cc, zero, nil)             ≡ cn
    vecrec(C, cn, cc, succ n, cons(n, a, v)) ≡ cc[n, a, v, vecrec(C, cn, cc, n, v)]

Assess both assumptions against the Kan-only criterion of [scope.md](scope.md).
Both violate the criterion as it reads today. Neither the carrier nor the
initiality property comes from a finite Kan extension. A criterion that
admits ω-colimits and their universal property would cover the carrier, and the
elimination rules would follow from initiality. calculus.md grants no such
admission, so both are extra rules and the obligations table says so.
The ruling on D2 takes option (a).

## Identity types at M1: the D6 decision

`vecrec` above uses no identity type. The motive takes the index as its own
argument, so the two computation rules match indices structurally. This is the
recursor presentation, which is also how Lean states eliminators for indexed
families. That Lean claim is unverified here, and Draft A verifies it against
<https://lean-lang.org/doc/reference/latest/The-Type-System/>. Identity types
are out of scope at M1. Two consequences need disclosure: constructor
injectivity and constructor disjointness for Nat and Vec go unstated, and any
later rule that transports along an index equation needs an identity type at M2.

## Conversion

Conversion is deterministic normalize-and-compare on the checked syntax. The
algorithm takes Γ, a type, two terms and a fuel budget.

1. Normalize both terms against the type in Γ under the shared budget.
   `normalize` checks its input against the expected type before it reduces,
   so conversion needs no separate check step (lib/finite_term.mli:49-50,
   lib/finite_term.ml:227-229). A typed error propagates.
2. Compare the two normal forms structurally, with labels in canonical order.

The answer is equal, not equal, or `Resource_exhausted`. Exhaustion is
inconclusive: it is never equality and never acceptance.

`Finite_term.normalize` is the reference implementation of step 1 for the
nondependent fragment (lib/finite_term.mli:69, lib/finite_term.ml:227-229). It
checks, reduces to beta normal form, keeps neutral forms, and emits canonical
label order. Step 2 has no implementation in the repository today. The
library exports no term comparison routine, so the structural compare stays
specification only. D7 confirms `normalize` as the reference for step 1. Type equality needs the same
treatment once types mention terms. The implemented fragment compares types
structurally, which is sound there because a `ty` holds no term variables. The
dependent extension needs a type normalizer, and the code has none today.

The algorithm is deterministic. The reduction traversal fixes the order of work,
and there is no search, no unification and no user hint. The same input with the
same fuel gives the same answer on every run.

Four properties stay unproved: soundness of the comparison against the equality
judgments, completeness against them, confluence, and strong normalization. The
algorithm returns an answer or reports `Resource_exhausted`, because each
visited node spends one fuel unit from a finite budget (lib/finite_term.mli:59-67).
Fuel meters visited term nodes only. The library states for `check` that fuel
does not bound elapsed time or host allocation (lib/finite_term.mli:32), and
for `substitute` that it meters term visits only, not host stack, allocation
or type operations (lib/finite_term.mli:43-44). `normalize` reuses the same
counter, so the same limits apply, and its own doc comment does not restate
them. Termination by fuel is not strong normalization, and it is not a bound
on host resources.

## Decisions D1 to D7

The user ruled on all seven decisions on 2026-09-06.
`~/Documents/kan-evm-m1/M1-DECISION-SHEET.md` records the ruling.

| Id | Options | Ruling 2026-09-06 | Consequence |
|---|---|---|---|
| D1 fibers as types | (a) Σ and Π as Lan and Ran along display maps, with the label-indexed finite fibers as the special case over a finite atom type; (b) two unrelated constructions | (a) | The implemented `Lan` and `Ran` stay valid as the finite instance, and no code changes before the dependent syntax lands |
| D2 induction | (a) primitive inductive family former with a disclosed initiality assumption and a not-Kan-only flag; (b) admit infinite diagrams; (c) defer Nat and Vec to M2 | (a) | M1 states the Nat and Vec rules and marks them as extra rules, so the core claim stays visible. (b) breaks the finiteness and computability assumptions of calculus.md. (c) hides the claim instead of testing it |
| D3 universes | (a) none at M1, type families carried by `Γ ⊢ A type`; (b) one universe now | (a) | This document writes no `U_l`, and the universe obligation stays open for M2 |
| D4 conversion strength | (a) beta only, canonical field order, eta disclosed as a gap; (b) beta plus eta now | (a) | The eta rules above stay unimplemented, and `docs/lean-target.md` carries the gap entry |
| D5 proof medium | (a) paper proofs now in `docs/metatheory.md` with a panel pass, Lean mechanization as a later slice in an in-repo `proofs/` lakefile project; (b) mechanize now | (b) | The in-repo Lean 4 package under `proofs/` mechanizes the finite-fragment theorem inventory of `docs/metatheory.md`, including successful closed normalization/evaluation agreement at independent budgets. Its toolchain is pinned per `docs/lean-target.md`, and kan-tactics is its only tactic dependency. The audited theorems have axiom accounting and no `sorry`, `unsafe`, `partial` or `native_decide`. These are proofs of the Lean deep embedding; `proofs/FIDELITY.md` records differences from OCaml. C7, strong normalization and confluence remain open. The finite denotation proposition in this document concerns only the implemented `Atoms`/`Lan`/`Ran` fragment; it remains a paper proof outside the mechanization scope |
| D6 identity types | (a) out of scope and disclosed, because the recursor form needs no index equality; (b) add them now for constructor injectivity | (a) | No transport rule and no no-confusion rule at M1 |
| D7 conversion reference | (a) confirm `Finite_term.normalize` as the reference for the fragment it covers; (b) veto it and specify a separate routine | (a) | The conversion obligation narrows to the dependent case and to the four unproved properties above |

## Obligations table rows

These four rows replace the matching rows of the table in
[calculus.md](calculus.md). The close step applies them after the ruling on D1
to D7. The Equality row of calculus.md stays Open, and this document narrows
it: D6 puts intensional identity out of scope at M1, and the conversion
section fixes the decision procedure but proves none of its four properties.
No other row changes.

| Obligation | Required evidence | Status |
|---|---|---|
| Primitive inventory | Complete syntax and rules, including all generators | Specified here for Π, Σ, Nat and Vec; not implemented; universes and identity types still absent |
| Dependent products/sums | Formation, intro, elim, beta/eta and substitution | Specified here with beta; eta stated and deferred by D4; substitution stability stated as Beck-Chevalley and unproved |
| Induction | Nat induction and indexed vector elimination, not just Church encodings | Rules stated as ASSUME-NAT and ASSUME-VEC; not Kan-only, because initiality is an extra principle |
| Conversion algorithm | Soundness, completeness for chosen equality, termination | Algorithm fixed as normalize-and-compare, implemented for the nondependent fragment by `normalize`; soundness, completeness, confluence and strong normalization unproved |

## Not established

- No rule here is implemented. The code covers the nondependent fragment only.
- The finite denotation proposition covers only the implemented
  `Atoms`/`Lan`/`Ran` fragment and remains a paper proof. Its mechanization
  is not scheduled; `proofs/` instead mechanizes the finite-fragment
  metatheory inventory, with C7 still open, for a Lean deep embedding.
- No model of this calculus is exhibited, so Beck-Chevalley is a requirement
  here and not a theorem.
- The two Lean claims (definitional eta; eliminators without identity types) are
  unverified in this document. Draft A verifies them.
- Consistency is not addressed. ASSUME-NAT and ASSUME-VEC make that question
  harder, not easier.
- Tests for this syntax, when they exist, are evidence and not theorems.

## References

- [calculus.md](calculus.md): finite adjunction, obligations table, and the
  instruction to record extra principles. [finite-terms.md](finite-terms.md):
  implemented rules. [roadmap.md](roadmap.md): the M1 exit criteria.
- [Riehl, Category Theory in Context](https://math.jhu.edu/~eriehl/context/):
  Kan extensions, adjunctions, and colimits of chains.
- [Gratzer and Sterling, Syntactic categories for dependent type theory](https://www.danielgratzer.com/papers/syntactic-categories-for-dependent-type-theory.pdf):
  display maps, context extension, and the Beck-Chevalley condition.
- [Lean type system](https://lean-lang.org/doc/reference/latest/The-Type-System/):
  the comparison target for definitional equality and for eliminators.
