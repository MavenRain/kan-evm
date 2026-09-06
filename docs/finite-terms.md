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
checked syntactic substitution operation is described below. There is no
open-term normalizer, eta conversion or proof of preservation. Beta tests and
substitution comparisons are executable evidence, not metatheory proofs.

## Checked syntactic substitution

`substitute ~fuel ~context ~replacement ~replacement_type body expected` checks
`Γ ⊢ replacement ⇐ A` first, then `A :: Γ ⊢ body ⇐ B`, where `Γ = context`,
`A = replacement_type` and `B = expected`. On success it returns `body[replacement/0]`
with the removed context entry discharged. The intended typing property is
`Γ ⊢ body[replacement/0] ⇐ B`. This is tested, not yet formally proved.

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

## Resource and trust boundary

Each visited term node consumes one unit from a single budget. Siblings share
it. `run` shares the budget between checking and evaluation; `substitute` shares
it between both checks and the substitution traversals. A nonpositive
remaining budget yields `Resource_exhausted`; it never means acceptance.

This is a node-visit budget, not a hardened process resource limit. Sorting,
list traversals, type equality, type construction and host stack/allocation
are not metered. Inputs are assumed to be finite acyclic OCaml values; there
is no untrusted serialization boundary. A future kernel must bound those costs
and handle deep inputs before claiming robust resource control.

## Remaining M1 work

Pin the Lean comparison release and enumerate its safe features and axiom
policy. Specify the dependent calculus and derive functions, pairs, naturals
with induction and indexed vectors, or disclose the extra required primitives.
Prove substitution and preservation for the implemented syntax. Define and
justify deterministic conversion for any extension needing it. The present
finite-fiber Ran is not a derivation of general dependent function types.
