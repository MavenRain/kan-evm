# M1 first slice: explicit finite-fiber terms

This fragment turns the M0 host callbacks into checked object-language branches.
It does not complete M1 or establish a Kan-only dependent logical core.

## Primitive inventory

Types are finite atom sets, `Lan [(label, type)]`, and `Ran [(label, type)]`.
The latter two describe a single target fiber of a finite discrete diagram:
the labels enumerate exactly those source indices mapping to that target.
Nested types are allowed. Atom sets and finite indexing labels are explicit
metatheoretic generators, not derived logical constructors. There are no
universes, recursive types, axioms, holes, function types or implicit coercions.

Structural infrastructure consists of nearest-binder-first contexts, de Bruijn
variables, and one payload binder per Lan elimination branch. Types contain no
term variables. The public type constructors reject duplicate labels and sort
labels recursively through already-constructed child types. Type equality is
structural equality of these canonical representations; it is not semantic
isomorphism or term conversion.

## Checking rules

The judgment is `Γ ⊢ term ⇐ type`. All calls supply an expected type. There is
no inference, search or unchecked callback in the checker.

| Term | Checking obligation |
|---|---|
| `Var i` | `i >= 0` and context entry `i` equals the expected type |
| `Atom x` | Expected type is an atom set containing `x` |
| `Tag (a, t)` | Expected type is Lan, with fiber `a : A`; check `t ⇐ A` |
| `Section fields` | Expected type is Ran; exactly one checked term per fiber |
| `Case {scrutinee; scrutinee_type; branches}` | Annotation is Lan; check scrutinee against it; for every fiber `a : A`, check its branch against the expected result type under `A :: Γ` |
| `Project {section; section_type; label}` | Annotation is Ran; selected fiber equals the expected type; check section against annotation |

Branch and section keys must match their fiber keys exactly, without duplicates.
Every branch is checked, including unexecuted branches. An empty Lan permits
elimination with zero branches but still requires a checked scrutinee. An empty
Ran admits the empty section. Equal payloads at different tags remain distinct.

## Computation

`run` first checks a closed term and then evaluates it using an environment.
Evaluation is eager. A section evaluates its components in sorted label order;
a case evaluates its scrutinee, then only its selected branch with the payload
prepended to the environment. Projection selects from the evaluated section.

The intended beta equations are:

```text
case (tag a v) of branches  -->  branches[a][v/0]
project (section fields) a -->  fields[a]
```

The evaluator realizes payload substitution by environment extension. A separate
checked syntactic substitution operation is described below. A fuel-bounded
open-term normalizer applies the same two equations. There is no eta conversion.
[Lean proofs](../proofs/README.md) establish preservation for the deep embedding;
OCaml beta tests and substitution comparisons remain executable evidence.

## Checked syntactic substitution

`substitute ~fuel ~context ~replacement ~replacement_type body expected` checks
`Γ ⊢ replacement ⇐ A` first, then `A :: Γ ⊢ body ⇐ B`, where `Γ = context`,
`A = replacement_type` and `B = expected`. On success it returns `body[replacement/0]`
with the removed context entry discharged. The typing property
`Γ ⊢ body[replacement/0] ⇐ B` is proved for the Lean embedding and tested in OCaml.

At depth `d` beneath Case branch binders, substitution maps a variable `i` to:

| Condition | Result |
|---|---|
| `i < d` | `Var i`, bound within the body |
| `i = d` | The replacement with its free indices increased by `d` |
| `i > d` | `Var (i - 1)`, accounting for the removed context entry |

Shifting the replacement tracks its own local binders: at local depth `c`, only
indices `i >= c` increase. Case scrutinees use the current depth and every branch
uses depth plus one. All other constructors preserve depth. Annotations contain
no term variables and remain unchanged; source field order is preserved.

The operation checks even an unused replacement, traverses every body branch,
and performs no beta reduction. One shared budget pays for both input checks,
one visit per body node, and one visit per replacement node at each substituted
occurrence. No replacement traversal is charged when it is unused. For example,
substituting `Atom "x"` into `Var 0` needs four visits: two checks, one body visit
and one replacement visit. Exhaustion at any phase returns `Resource_exhausted`.
The output is not rechecked internally; regression tests check output typing
and compare its evaluation against the original Case/environment computation.

## Normalization

`normalize ~fuel ~context term expected` checks `Γ ⊢ term ⇐ B` first, where
`Γ = context` and `B = expected`. It then reduces the term to beta normal form
with the remaining budget. The reduction is type directed: every subterm is
reduced at the type its parent gives it, taken from the Lan fiber, the Ran
fiber or the annotation.

| Term | Reduction |
|---|---|
| `Var i` | Itself |
| `Atom x` | Itself |
| `Tag (a, t)` | `Tag (a, t')`, with `t` reduced at fiber `a` |
| `Section fields` | Each field reduced at its fiber, in canonical order |
| `Case` on `Tag (a, v)` | Substitute the reduced `v` for index 0 in branch `a`, then reduce the result at the expected type |
| `Case` on a neutral scrutinee | Keep the Case; reduce each branch at the expected type. The binder fiber does not direct beta reduction in this nondependent fragment |
| `Project` of a `Section` | The already reduced field for the label |
| `Project` of a neutral section | Keep the Project with the reduced section |

Neutral forms are a variable, a Case on a neutral scrutinee, and a Project of a
neutral section. A normal form thus has no Case on a Tag and no Project of a
Section. Sections and branches in the output are in canonical label order, even
when the input order differs. Annotations do not change. The substitution for a
Case of a Tag is the internal, unchecked core of `substitute`; both operations
share it, so the shift rules in the substitution table apply unchanged.

A scrutinee that reduces to an Atom or a Section, and a projected section that
reduces to an Atom or a Tag, cannot occur after the initial check. Those cases
return `Expected_lan` and `Expected_ran`; the function never raises.

One budget pays for the check and the reduction. The check charges one unit per
node. The reduction charges one unit per visited node. A Case of a Tag charges
in addition one unit per node of the selected branch, one unit per replacement
node at each substituted occurrence, and then the units to reduce the
substituted body. For example, `normalize` of

```text
Case {scrutinee = Tag ("a", Atom "x");
      scrutinee_type = Lan [("a", Atoms ["x"])];
      branches = [("a", Var 0)]}
```

at `Atoms ["x"]` needs exactly ten units: four to check (Case, Tag, Atom, Var),
three to reduce the Case node and its scrutinee (Case, Tag, Atom), two to
substitute (the branch node `Var 0` and the replacement node `Atom "x"`), and
one to reduce the substituted body `Atom "x"`. Nine units return
`Resource_exhausted`. Two further measured examples: the projection of a
two-field section of atoms needs eight units, and a Case on a variable with one
variable branch needs six.

What this does not establish: there is no eta rule, so normal forms are equal
only up to beta and canonical label order. The output is not rechecked
internally. The Lean embedding has typing preservation and successful closed
agreement with `run` at independent budgets. Strong normalization and confluence
remain unproved. OCaml tests compare `run` values, recheck open normal forms,
and test idempotence; they do not prove equivalence with the Lean embedding.

## Resource and trust boundary

Each visited term node consumes one unit from a single budget. Siblings share
it. `run` shares the budget between checking and evaluation; `substitute` shares
it between both checks and the substitution traversals; `normalize` shares it
between the check and every reduction and substitution visit. A nonpositive
remaining budget yields `Resource_exhausted`; it never means acceptance.

This is a node-visit budget, not a hardened process resource limit. Sorting,
list traversals, type equality, type construction and host stack/allocation
are not metered. Inputs are assumed to be finite acyclic OCaml values; there
is no untrusted serialization boundary. A future kernel must bound those costs
and handle deep inputs before claiming robust resource control.

## Remaining M1 work

Lean 4.33.1 and its axiom policy are pinned; substitution and preservation are
proved for the [Lean embedding](../proofs/README.md). Implement the specified
[dependent calculus](dependent-calculus.md), including functions, pairs, naturals
and vectors with disclosed extra induction primitives; justify its conversion.
Successful normalization fuel bounds, strong normalization, confluence and OCaml/Lean
equivalence remain open. Finite-fiber Ran does not derive general dependent functions.
