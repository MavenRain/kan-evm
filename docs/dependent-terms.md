# M1 dependent reference fragment

`Dependent_term` implements the first executable subset of
[dependent-calculus.md](dependent-calculus.md). It is a separate library from
`Finite_term`. The existing finite Lean embedding and its 42 audited theorem
names do not cover this library. This is an experimental checker, not a proof
kernel or an EVM compiler.

## Primitive inventory

Types are `Atoms labels`, `Nat`, `Vec (element, length)`, `Pi (domain, codomain)`
and `Sigma (domain, codomain)`. Types and terms are mutually recursive: a vector
length is an object-language term, and eliminations carry type annotations.
There is no universe or type-valued term. Raw syntax is public; every checking
entry point validates it. Atom labels are metatheoretic inputs, duplicates are
errors, and type normalization sorts labels for structural comparison.

Terms are variables, atoms, `Zero`, `Succ`, `Nil`, `Cons`, `Lam`, annotated
`App`, `Pair`, and annotated `Split`. Nat and Vec formation and constructors
are extra primitives under the D2 decision. They are not derived from finite
Kan extensions. Their induction eliminators, ASSUME-NAT and ASSUME-VEC in the
full specification, are not implemented yet. Pi and Sigma follow the specified
display-map rules; a categorical model identifying them with dependent Kan
extensions remains an obligation.

## Contexts and binding

A context is nearest-binder first. Each stored type is written in its older
tail context. For example, `[Vec (a, Var 0); Nat]` represents a vector variable
whose length is the older natural variable. In the full context, `Var 0` has
type `Vec (a, Var 1)`. Variable lookup shifts the stored type by `index + 1`.
The checker validates the whole context, including unused entries, from older
entries to newer ones.

Pi and Sigma codomains bind one variable. Lambda bodies and application
codomain annotations also bind one variable. Split has these scopes:

| Field | Scope |
|---|---|
| `domain` | The caller's context Γ |
| `codomain` | Γ extended by the first component |
| `pair` | Γ, checked at `Sigma (domain, codomain)` |
| `motive` | Γ extended by the whole pair |
| `body` | Γ extended by both components; first is index 1, second is index 0 |

Both weakening and simultaneous substitution traverse types, vector indices,
all annotations, and all term children. Local bound variables remain fixed;
free variables move under every crossed binder. Removing a pair's two binders
substitutes `[second; first]` simultaneously, so one replacement is never
accidentally substituted into the other.

## Checking

The caller always supplies an expected type. There is no inference, unification
or proof search. `check_type` validates formation; `check` additionally checks
the supplied term. Public operations first validate the context and required
types. Application and split annotations are checked in their stated scopes.

| Term | Obligation |
|---|---|
| `Var i` | The weakened context entry converts to the expected type |
| `Atom label` | The expected atom set contains the label |
| `Zero`, `Succ n` | The expected type is Nat; check `n : Nat` for Succ |
| `Nil` | The expected type is `Vec (a, n)` and `n` reduces to Zero |
| `Cons {length; head; tail}` | The expected type is `Vec (a, n)`; check `length : Nat`, `n` convertible to `Succ length`, `head : a`, and `tail : Vec (a, length)` |
| `Lam body` | The expected type is `Pi (a, b)`; check the body at b under a |
| `App {fn; domain; codomain; argument}` | Form the annotated Pi; check fn and argument; instantiate the codomain and compare it with the expected type |
| `Pair (first, second)` | The expected type is `Sigma (a, b)`; check first at a, then second at `b[first/0]` |
| `Split {pair; domain; codomain; motive; body}` | Form annotations and motive; check pair; check body at the motive instantiated with `(1, 0)` under two binders; compare `motive[pair/0]` with the expected type |

All supplied components must check, including arguments unused by a lambda
and components discarded by a split. Wrong lengths, ill-typed indices,
malformed contexts and duplicate atom labels return explicit errors. Validating
an identical pair of malformed terms never produces a conversion answer.

For a concrete dependent example, with `a = Atoms ["x"]`:

```ocaml
let vector_identity_type =
  Pi (Nat, Pi (Vec (a, Var 0), Vec (a, Var 1)))
let vector_identity = Lam (Lam (Var 0))
let packed_vector_type = Sigma (Nat, Vec (a, Var 0))
let packed_vector =
  Pair (Succ Zero, Cons { length = Zero; head = Atom "x"; tail = Nil })
```

These examples contain actual term-dependent types. Replacing the packed
vector's first component with Zero makes its nonempty second component invalid.
Tests also use a split motive that mentions a projection of its bound pair.

## Normalization and comparison

`normalize_type` checks formation and then reduces every embedded term index.
`normalize` checks the term before reduction. The normalizer traverses binder
bodies and annotations and implements:

```text
app (lam body) argument       --> body[argument/0]
split C body (pair a b)       --> body[b/0, a/1]
```

Arguments and pair components normalize before substitution. Lambda bodies
normalize as well. A split on a pair substitutes into its checked body and
normalizes the result; a split on a neutral pair retains and normalizes its
body. Open variables, applications and splits stay neutral. Atom types and all
annotations have canonical normal forms. There is no eta expansion or
contraction, and no arithmetic or Nat/Vec recursion.

`convert_types` validates and normalizes its left type, then its right type.
`convert` validates the context and common expected type once, then checks and
normalizes the left term followed by the right term. Both compare resulting
syntax structurally, including normalized annotations. Beta-convertible vector
indices can therefore yield equal types. Errors propagate in that order.
`Ok false` requires two successful normalizations.

`substitute_type` checks a replacement and a type under its binder, then removes
the binder. `substitute` also checks a term body at a supplied dependent expected
type in that extended context. Its result has the instantiated expected type.
Neither operation reduces or rechecks its output internally. Regression tests
independently instantiate expected types and recheck results.

## Resource and proof boundaries

One shared budget covers context entries and every visited term/type node in
formation, checking, normalization, weakening, and substitution. Repeated
traversals spend fuel again. Each replacement occurrence pays one more visit
for every node of its replacement, at all depths, including depth zero where
the occurrence crosses no local binder. Nonpositive fuel yields
`Resource_exhausted`.
Budgets do not reset between phases, operands or siblings.

This policy includes type work that the finite fragment leaves unmetered.
It remains a node budget: label sorting, list lookup, structural comparison,
allocation and host stack usage are not metered. The API assumes finite acyclic
OCaml values and is not an untrusted serialization boundary.

Dependent checker soundness/completeness, weakening and substitution lemmas,
preservation, normalization guarantees, confluence and conversion correctness
remain unproved. Tests are bounded executable evidence. The next functional
slice is Nat induction and the length-indexed vector eliminator; the dependent
metatheory and its Lean embedding also remain required for M1 completion.
