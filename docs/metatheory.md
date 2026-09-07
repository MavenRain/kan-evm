# Metatheory of the implemented finite-fiber fragment

These are paper proofs about `lib/finite_term.ml`, with corresponding finite-fragment
theorems checked in the Lean deep embedding under `proofs/`. The runners in `test/`
are executable evidence, not proofs. Decision D5's mechanization package uses
kan-tactics, with the toolchain pinned per `docs/lean-target.md`. Its successful
normalization/evaluation agreement assumes both calls succeed at independent budgets;
Claim C7 stays open. [FIDELITY.md](../proofs/FIDELITY.md) records the OCaml/Lean differences. The
Lean reference manual is at https://lean-lang.org/doc/reference/latest/.

## 1. Notation and standing assumptions

`A`, `B` are types. `s`, `t`, `r`, `b` are terms. `G` is a context, a list of types,
nearest binder first, and `G(i)` is its entry at de Bruijn index `i`. `F` is a fiber
list of `(label, type)` pairs, and `F(a)` is its type at label `a`. Types contain no
term variables (`docs/finite-terms.md:16-17`), so no rule below substitutes into a type.
Type equality is OCaml structural equality (`lib/finite_term.ml:67`,
`lib/finite_term.ml:100`). Terms and types are finite acyclic values, so that equality
terminates.

## 2. Lemma 0, canonical types

Every reachable `ty` is canonical: each `Lan` and `Ran` fiber list is sorted by label,
holds no repeated label, and nests only canonical types. Proof: `ty` is abstract
(`lib/finite_term.mli:3`), and only `atoms`, `lan` and `ran` build one
(`lib/finite_term.mli:17-19`). Each of the three sorts its label list and then calls
`unique`, which rejects a duplicate (`lib/finite_term.ml:20-29`). Each nested argument
came from the same three functions, so induction on construction order gives its
canonicity. `check_term`, `substitute_core`, `reduce` and `evaluate` build no type and
copy annotations unchanged. Consequence: structural equality decides the intended type
equality, because two canonical representations are equal exactly when they carry the
same labels and the same fiber types. Unverified: no test asserts Lemma 0, and the
argument fails if a later change exports the constructors of `ty`.

## 3. The typing relation

`G |- t <= A` is the relation below. Each rule mirrors one arm of `check_term`
(`lib/finite_term.ml:62-105`). The relation carries no fuel.

    (VAR)      0 <= i < length G, G(i) = A  =>  G |- Var i <= A
    (ATOM)     A = Atoms ls, x in ls        =>  G |- Atom x <= A
    (TAG)      A = Lan F, (a, Aa) in F, G |- t <= Aa
                                            =>  G |- Tag (a, t) <= A
    (SECTION)  A = Ran F, keys(sort fields) = keys(F),
               G |- t <= F(a) for every (a, t) in fields
                                            =>  G |- Section fields <= A
    (CASE)     S = Lan F, keys(sort branches) = keys(F), G |- s <= S,
               F(a) :: G |- b <= A for every (a, b) in branches
                    =>  G |- Case {scrutinee = s; scrutinee_type = S; branches} <= A
    (PROJECT)  S = Ran F, (l, A) in F, G |- s <= S
                    =>  G |- Project {section = s; section_type = S; label = l} <= A

Key alignment. `keys(sort x) = keys(F)` means two things. The term list has no duplicate label. Its
sorted label sequence equals the fiber label sequence, element by element.
The checker gets this from `canonical` then `align` (`lib/finite_term.ml:20-23`,
`lib/finite_term.ml:51-60`): `canonical` sorts and rejects duplicates, and `align` walks
two sorted lists, reports `Missing_label` when the fiber key is smaller and
`Unexpected_label` when the term key is smaller. So `align` succeeds exactly on equal
sorted key sequences, and Lemma 0 already sorted the fibers. CASE checks every branch,
including a branch that no evaluation selects. An empty `Lan` allows a Case with zero
branches and still demands a checked scrutinee; an empty `Ran` allows the empty Section.

## 4. Value typing and environment typing

Values are `Atom_value | Tag_value | Section_value` (`lib/finite_term.ml:231-234`).

    (V-ATOM)     A = Atoms ls, x in ls   =>  Atom_value x : A
    (V-TAG)      A = Lan F, (a, Aa) in F, v : Aa  =>  Tag_value (a, v) : A
    (V-SECTION)  A = Ran F, keys(e) = keys(F), v : F(a) for every (a, v) in e
                                         =>  Section_value e : A

V-SECTION demands the sorted key sequence of `F`. The evaluator builds a `Section_value`
only from `canonical entries` (`lib/finite_term.ml:244-247`), so a well-typed section
value is sorted. Value typing needs no context, because a value holds no variable.
Environment typing is pointwise: `rho : G` holds when `length rho = length G` and
`rho(i) : G(i)` at every index in range. `run` uses the empty environment against the
empty context (`lib/finite_term.ml:268-270`).

## 5. Size and fuel

`size(t)` counts term nodes: `size(Var i) = size(Atom x) = 1`, `size(Tag (a, t)) = 1 +
size(t)`, `size(Section e) = 1 + sum of field sizes`, `size(Case) = 1 + size(scrutinee)
+ sum of branch sizes`, and `size(Project) = 1 + size(section)`. Every traversal calls
`tick` on entry (`lib/finite_term.ml:47`), so a successful traversal spends one unit per
visited node. Exhaustion returns `Resource_exhausted`, which is never acceptance.

Lemma 1, budget monotonicity. If a traversal returns `Ok (x, rest)` at budget `f`, it
returns `Ok (x, rest + f' - f)` at every budget `f' >= f`. Proof: induction on the call
tree. Only `tick` reads the budget, and only for the test `fuel <= 0`, so a larger
budget takes the same branch at every node and spends the same units.

Lemma 2, exact cost of checking. If `check_term f G t A = Ok rest` then `rest = f -
size(t)`. Proof: induction on `t`, with a simultaneous induction on entry lists for
`check_many` (`lib/finite_term.ml:103-105`). Each node ticks once and visits each child
once; CASE visits the scrutinee once and each branch once.

Lemma 2b, the charges of one reduction step. `reduce` spends one unit at each node it
enters. A Case of a Tag also pays `substitute_core`, which is `size(body) + n *
size(payload)` for the `n` occurrences in the selected branch of the index that the
traversal is replacing, that is `Var d` at binder depth `d` (`lib/finite_term.ml:140-149`),
and then pays
the reduction of the substituted body. So `reduce` may charge one input node more than
once, and the bound `size(t)` of Lemma 2 does not extend to it. Example: the Case with
scrutinee `Tag ("a", Atom "x")`, annotation `Lan ["a", Atoms ["x"]]` and branch `Var 0`
has size 4, and `normalize` needs ten units: four to check, three to reduce the Case node
and its scrutinee, two to substitute and one to reduce the substituted body
(`lib/finite_term.mli:58-67`, code comment at `lib/finite_term.ml:158-161`). Subsection
11.5 states why no total bound in `size(t)` is proved.

## 6. Theorem 1, checker soundness and completeness modulo fuel

(1) If `check ~fuel ~context:G t A = Ok ()` then `G |- t <= A`. (2) If `G |- t <= A`
then `check ~fuel:(size t) ~context:G t A = Ok ()`, and by Lemma 1 so does every larger
budget. Part 1 is structural induction on `t`, with a simultaneous induction on subterm
lists for `check_many`; its cases are Var, Atom, Tag, Section, Case and Project. Part 2
is induction on the derivation of `G |- t <= A`, one case per rule.

Var. `variable index context` rejects a negative index and returns `List.nth_opt`
(`lib/finite_term.ml:43-45`), so success gives `0 <= i < length G` and `G(i) = actual`.
The test `actual = expected` holds only for equal canonical types, by Lemma 0.

Section, aligned keys. `canonical entries` then `align fibers entries` give exactly the
SECTION side condition, and `align` returns the `(fiber type, term)` pairs in the shared
sorted order, so `check_many` supplies one premise per fiber.

Case, the extended context. The checker aligns the branches, checks the scrutinee
against the `Lan` annotation, then checks each branch by `check_term fuel (payload_type
:: context) body expected` (`lib/finite_term.ml:86-94`). The branch context is the fiber
type consed onto `G`, the expected type stays `A`, and `align` pairs a branch with the
fiber of its own label. That is CASE.

Part 2 rebuilds each arm from its rule. The side conditions make `canonical` and `align`
succeed, and Lemma 2 makes `size(t)` pay for the whole derivation. Corollary:
`check ~fuel` returns `Ok ()` exactly when `G |- t <= A` and `fuel >= size(t)`.
Claim C1, checked by execution. Which error `check` reports does depend on the budget,
because `tick` runs before every side-condition test (`lib/finite_term.ml:47`) and the
Case arm checks the scrutinee before the branches. Take `Case {scrutinee = Tag ("a",
Atom "x"); scrutinee_type = Lan ["a", Atoms ["x"]]; branches = [("a", Atom "y")]}` at
`Atoms ["x"]`: `check` returns `Resource_exhausted` at fuel 3 and `Invalid_atom "y"` at
fuel 4. Theorem 1 needs a weaker property, and that property holds: if `check_term`
returns an error other than `Resource_exhausted`, then `G |- t <= A` fails at every
budget, because each error arm reports a violated side condition of section 3. A
successful check spends exactly `size(t)`, by Lemma 2: the same term with branch
`Atom "x"` has `size(t) = 4`, and `check` returns `Resource_exhausted` at fuel 3 and `Ok`
at fuel 4.

## 7. Theorem 2, weakening with a cutoff shift

`shift(c, d, t)` maps `Var i` to `Var i` when `i < c` and to `Var (i + d)` when
`i >= c`. It raises the cutoff to `c + 1` inside every Case branch and keeps `c`
elsewhere; annotations and source field order do not change. The library has no
standalone shift. The inner callback of `substitute_core` computes
`shift(0, depth, replacement)`: it calls `map_variables` at depth 0 and maps `index` to
`Var (if index < cutoff then index else index + depth)` (`lib/finite_term.ml:146-148`).
`map_variables` raises the depth by one for Case branches and keeps it elsewhere
(`lib/finite_term.ml:112-135`), so `cutoff` counts the Case binders crossed.

Statement. Let `length G1 = c` and `length D = d`. If `G1 @ G2 |- t <= B` then
`G1 @ D @ G2 |- shift(c, d, t) <= B`. The proof is structural induction on `t`, with a
simultaneous induction on branch and field lists. Cases: Var below the cutoff, Var at or
above the cutoff, Atom, Tag, Section, Case and Project.

Var below the cutoff. `i < c`, so the entry lies in `G1` and the index does not move:
`(G1 @ D @ G2)(i) = G1(i) = (G1 @ G2)(i)`, and VAR gives the same type. Var at or above
the cutoff: `(G1 @ G2)(i) = G2(i - c)`, the shift gives `Var (i + d)`, and
`(G1 @ D @ G2)(i + d) = G2(i + d - c - d) = G2(i - c)`.

Case under the extended context. The branch premise is `F(a) :: G1 @ G2 |- b <= B`.
Apply the hypothesis with `G1' = F(a) :: G1`, so the cutoff becomes `c + 1`, which is
the `depth + 1` that `map_variables` passes to branches. The scrutinee keeps `c`.
Annotations and branch labels do not change, so the CASE side condition survives.

## 8. Theorem 3, substitution at binder depth d

`sub(d, r, b)` is what `substitute_core` computes (`lib/finite_term.ml:139-151`). It
traverses `b`, tracks `d`, the number of Case branch binders crossed, and rewrites
variables by the table below; annotations and source field order do not change.
`substitute` checks both inputs and then calls `substitute_core` with `d = 0` at the
root (`lib/finite_term.ml:153-156`).

| Condition | Result |
|---|---|
| `i < d` | `Var i` |
| `i = d` | `shift(0, d, r)` |
| `i > d` | `Var (i - 1)` |

Statement. Let `length D = d`. If `G |- r <= A` and `D @ (A :: G) |- b <= B` then
`D @ G |- sub(d, r, b) <= B`. The proof is structural induction on `b`, generalized over
`d` and `D`, with a simultaneous induction on branch and field lists; that
generalization is what makes the Case step go through. Cases: Var at `i < d`, at `i = d`
and at `i > d`, Atom, Tag, Section, Case and Project.

Var with `i = d`. The entry is `A`, the removed one, so `B = A`, and the result is
`shift(0, d, r)`. Theorem 2 with `c = 0`, empty `G1`, `G2 = G` and inserted block `D`
gives `D @ G |- shift(0, d, r) <= A`. The inner cutoff starts at zero and rises inside
each Case branch of `r`, so a variable bound inside `r` does not move and only the free
indices of `r` rise by `d`.

Var with `i < d` and with `i > d`. Below `d` the entry lies in the shared prefix:
`(D @ (A :: G))(i) = D(i) = (D @ G)(i)`. Above `d`, `(D @ (A :: G))(i) = G(i - d - 1)`,
the result is `Var (i - 1)`, and `(D @ G)(i - 1) = G(i - 1 - d)`. The subtraction of one
accounts for the removed context entry.

Case. The branch premise is `F(a) :: D @ (A :: G) |- b <= B`. Apply the hypothesis with
`D' = F(a) :: D`, so the depth becomes `d + 1`, matching `map_variables` for branches,
while the scrutinee keeps `d`. The traversal preserves branch labels and their source
order, so the CASE side condition survives.

Corollary, the property `substitute` claims: if `G |- r <= A` and `A :: G |- b <= B`
then `G |- b[r/0] <= B`. `docs/finite-terms.md:66-67` states it as tested; this is a
proof of it. Fuel: `substitute_core` spends `size(b) + n * size(r)` for `n` occurrences
of the substituted index, and `substitute` adds `size(r) + size(b)` for the two checks.
Claim C2, to verify: `2 * size(b) + (n + 1) * size(r)` always suffices, and at `n = 1`
it gives the four units that `docs/finite-terms.md:85-87` measures for `Atom "x"` into
`Var 0`.

## 9. Theorem 4, preservation for evaluation

If `G |- t <= A`, `rho : G` and `evaluate f rho t = Ok (v, rest)`, then `v : A`. The
proof is induction on the derivation of `G |- t <= A`, generalized over `rho` and the
budget; `evaluate` recurses only into subterms (`lib/finite_term.ml:236-266`), so each
recursive call uses a subderivation. Cases: Var, Atom, Tag, Section, Case on a tag
value, Project on a section value, and the two rejected value shapes. For Var,
`variable index environment` returns `rho(i)`, VAR gives `G(i) = A`, and `rho : G` gives
`rho(i) : G(i)`. For Section the evaluator sorts with `canonical` and evaluates in that
order (`lib/finite_term.ml:244-247`), which is the key sequence that V-SECTION demands.

Case on a tag value. The evaluator evaluates the scrutinee, demands
`Tag_value (label, payload)`, selects `lookup label branches` from the source list, and
evaluates that body in `payload :: rho` (`lib/finite_term.ml:248-253`). CASE gives
`G |- scrutinee <= Lan F`, so the hypothesis and V-TAG give `label` in `F` and
`payload : F(label)`. CASE aligned the sorted branch labels with the fiber labels and
rejected duplicates. So `lookup` on the unsorted source list finds the single branch of
that label. The evaluator needs no sort. The branch premise is `F(label) :: G |- body <=
A`. `payload :: rho : F(label) :: G` holds pointwise. The hypothesis gives `v : A`. The
checker and the value use the same fiber type, because
`align` pairs a branch with the fiber of its own label.

Rejected shapes. The two remaining arms return `Expected_lan` and `Expected_ran`
(`lib/finite_term.ml:254`, `lib/finite_term.ml:260`). V-TAG is the only value rule at a
`Lan` type and V-SECTION the only one at a `Ran` type, so those arms are unreachable
here and only keep `evaluate` total. Claim C3, to verify: `run` never reports
`Expected_lan` or `Expected_ran` after a successful check. Budget: `evaluate` visits each
node at most once, because it substitutes nothing and evaluates only the selected branch,
so `2 * size(t)` suffices for `run` whenever `run` succeeds at any budget. Claim C4, to
verify.

## 10. Theorem 5, substitution and environment coincidence

This is the beta equation that `test/finite_substitution_test.ml:110` compares.

Lemma 3, shifting keeps the value. Let `D` be a list of values with `length D = d`.
Generalized statement: let `E` be a list of values with `length E = c`. If
`evaluate (E @ rho) r = Ok (u, _)` at some budget, then at sufficiently large
budgets `evaluate (E @ D @ rho) (shift(c, d, r)) = Ok (u, _)`.
The lemma is the case `c = 0` and `E = []`, which gives
`evaluate (D @ rho) (shift(0, d, r)) = Ok (u, _)` when `evaluate rho r = Ok (u, _)`. Proof:
structural induction on `r`, generalized over `c` and `E`. A variable `i < c` reads `E(i)`
on both sides. A variable `i >= c` reads `(E @ D @ rho)(i + d) = (E @ rho)(i)`, because the
read skips the `d` inserted entries. Case: the scrutinee agrees by the induction
hypothesis, so both sides select the same label; apply the induction hypothesis to the
selected branch with `E' = payload :: E` and cutoff `c + 1`, which matches the depth that
`map_variables` passes to branches (`lib/finite_term.ml:125`) and the environment that
`evaluate` extends (`lib/finite_term.ml:253`). Every other constructor passes `c` and `E`
down.

Statement. Let `length D = d`. Suppose `evaluate rho r = Ok (u, _)` and
`evaluate (D @ (u :: rho)) b = Ok (v, _)` at some budgets. Then at sufficiently
large budgets `evaluate (D @ rho) (sub(d, r, b)) = Ok (v, _)`. At `d = 0`,
if `evaluate (u :: rho) b` succeeds, `evaluate rho (b[r/0])` returns the same value.
This claims preservation of successful evaluation, not agreement of errors.
For example, `D = rho = []`, `d = 0`, `r = Atom "x"` and `b = Var 1` fail the
body-evaluation premise: the environment side returns `Invalid_variable 1`,
while the substituted side returns `Invalid_variable 0`, at every positive budget.
The proof is structural induction on `b`, generalized over `d`, `D` and `rho`. Cases: Var
at `i < d`, at `i = d` and at `i > d`, Atom, Tag, Section, Case and Project.

Var. At `i = d` the left side evaluates `shift(0, d, r)` in `D @ rho`, which gives `u` by
Lemma 3, and the right side reads `(D @ (u :: rho))(d) = u`, because `D` holds exactly
`d` entries. At `i < d` both sides read `D(i)`. At `i > d` the left side reads
`(D @ rho)(i - 1) = rho(i - 1 - d)` and the right side reads
`(D @ (u :: rho))(i) = rho(i - d - 1)`.

Case, branch selection. The scrutinee agrees by the hypothesis, so both sides select the
same label. `sub` preserves branch labels and their source order, so `lookup label` finds
on the left the substituted copy of the branch that it finds unsubstituted on the right.
Apply the hypothesis to that branch with `D' = payload :: D` and depth `d + 1`, matching
`map_variables`. Claim C5, to verify: the budget hypothesis is real, because the left
side evaluates one copy of `r` per occurrence while the right side evaluates `r` once, so
the theorem states value agreement only.

## 11. Theorem 6, the normalizer

`normalize` checks the term, then calls the type-directed `reduce` with the rest of the
budget (`lib/finite_term.ml:162-229`). A normal form has no Case on a Tag and no Project
of a Section.

11.1 Termination and totality. `reduce` returns `Ok` or `Error` on every input; it never
diverges and never raises. Proof: strong induction on the budget. `reduce` ticks first,
so every recursive call runs at a budget of at most `n - 1`. The measure is the budget
alone, which also covers the call on the substituted body, a term that is not a subterm
of the input. `lookup`, `canonical` and `align` recurse on shorter lists.
No arm of `reduce` raises an OCaml exception of its own, and every failure it models is
a returned `Error`. Host stack exhaustion is outside this statement, see item 4 of
section 12: `tick` gives `Resource_exhausted`
(`lib/finite_term.ml:47`), `canonical` gives `Duplicate_label` through `unique`
(`lib/finite_term.ml:15-23`), `align` gives `Missing_label` or `Unexpected_label`
(`lib/finite_term.ml:51-60`), `lookup` gives `Unexpected_label` (`lib/finite_term.ml:40-41`),
the Project label test gives `Type_mismatch` (`lib/finite_term.ml:202`), a wrong
annotation shape gives `Expected_lan` or `Expected_ran` (`lib/finite_term.ml:172`,
`lib/finite_term.ml:180`, `lib/finite_term.ml:197`, `lib/finite_term.ml:210`), and the
rejected scrutinee and section shapes give `Expected_lan` and `Expected_ran`
(`lib/finite_term.ml:196`, `lib/finite_term.ml:209`).

11.2 Determinism. `reduce` is a function of its three arguments, the budget, the term
and the expected type (`lib/finite_term.ml:162`), and its output term does not depend on
the budget once the budget is large enough, by Lemma 1. The code holds no
mutable state and does no input or output. Structural equality is its only comparison,
and Lemma 0 makes that the intended type equality.

11.3 Typing preservation. If `G |- t <= A` and `reduce f t A = Ok (t', rest)` then
`G |- t' <= A`. `reduce` takes no context: the expected type and the annotations direct
every step, because the fragment is nondependent (`lib/finite_term.ml:158-162`). The
context `G` below is the ambient context of the typing judgment only. The proof is strong
induction on the budget, which covers the recursive call on the substituted body. Cases:
Var, Atom, Tag, Section, Case on a Tag, Case on a neutral scrutinee, Project of a Section,
Project of a neutral section.

Both Case sub-cases start from the reduced scrutinee. `reduce` rewrites it first
(`lib/finite_term.ml:185`), at the annotation `Lan F` and at a strictly smaller budget,
so the induction hypothesis gives `G |- s' <= Lan F` for the reduced scrutinee `s'`. The
Project arms are the same step at `Ran F` (`lib/finite_term.ml:204`).

Case on a Tag. The reduced scrutinee is `Tag (a, v)` at `Lan F`. TAG gives `G |- v <= F(a)`. CASE gives
`F(a) :: G |- body <= A` for the selected branch. Theorem 3 at `d = 0` gives
`G |- sub(0, v, body) <= A`. The hypothesis at the smaller budget types the reduction of
that body at `A`. The selected branch comes from `lookup label branches` on the canonical list, because
`reduce` rebinds `branches` to `canonical branches` before the lookup
(`lib/finite_term.ml:184`, `lib/finite_term.ml:188`). Sorting does not change the set of
pairs and `canonical` rejects duplicates, so the lookup returns the one branch of that
label, which is the branch that the checker checked. `evaluate` differs here: it looks the
label up in the source list (`lib/finite_term.ml:252`), and finds the same body for the
same reason.

Case on a neutral scrutinee, sorted keys. `reduce` rebuilds the Case from
`reduce_branches` over the aligned triples `(label, fiber, body)`
(`lib/finite_term.ml:219-225`). `reduce_branches` keeps the label that each triple
carries, and `align` built those triples by walking the sorted fiber list and the sorted
branch list in step and keeping the shared key (`lib/finite_term.ml:51-60`). The rebuilt
branch list is therefore sorted with the key sequence of `F`, the CASE side condition,
and each branch reduces under `fiber :: G` at `A`. `reduce_fields` rebuilds section
fields in that same sorted order, so a Section output meets the SECTION side condition
even when the input order differed.
Claim C6, to verify: `normalize` does not recheck its own output
(`docs/finite-terms.md:142`); this paper proof addresses the OCaml output typing claim.
Lean proves its embedded counterpart; OCaml tests recheck a bounded corpus as evidence.

11.4 Normal forms. If `reduce f t A = Ok (t', rest)` then `t'` has no Case with a Tag
scrutinee and no Project with a Section section. Proof: strong induction on the budget.
Cases: Var and Atom return the input, which is neutral or a constructor
(`lib/finite_term.ml:165`). Tag and Section rebuild from reduced parts
(`lib/finite_term.ml:166-180`). Case on a Tag returns the reduction of the substituted
body (`lib/finite_term.ml:190`), which is normal by the induction hypothesis, and
substitution can create a new redex only inside that body, which the same call reduces.
Case on a neutral scrutinee keeps a neutral scrutinee and normalized branches
(`lib/finite_term.ml:191-194`). Project of a Section returns a field of the reduced
section (`lib/finite_term.ml:205-206`); `reduce_fields` already normalized every field
(`lib/finite_term.ml:211-216`), so no further visit is needed. Project of a neutral
section keeps the neutral section (`lib/finite_term.ml:207-208`). The published contract
is `lib/finite_term.mli:50-53`.

11.5 Agreement with `run` on closed terms. Generalize first: if the free indices of `t`
are all below `k`, then the free indices of `reduce f t A = Ok (t', rest)` are all below
`k`. The Case on a Tag arm applies `sub(0, v, body)`, which removes index 0 from a body
whose free indices are below `k + 1`, with the free indices of `v` below `k`. The Case on
a neutral scrutinee arm reduces each branch body at `k + 1`, because `reduce_branches`
enters a body under one payload binder (`lib/finite_term.ml:219-225`). Every other arm
rebuilds a constructor from parts at the same `k`. At `k = 0` this says `reduce` maps a
closed term to a closed term. A closed normal form is a constructor term, because every neutral form has a
variable at its head. By 11.3, 11.4 and the value rules, it is an `Atom` at `Atoms ls`, a
`Tag` at `Lan F`, or a sorted `Section` at `Ran F`. So let `t` be closed with `[] |- t <= A`, let `run ~fuel t A = Ok
v`, and let `normalize ~fuel' ~context:[] t A = Ok t'` at large enough budgets. Then `t'`
equals `quote v`, where `quote` maps a value back to a term:
`quote (Atom_value x) = Atom x`,
`quote (Tag_value (a, v)) = Tag (a, quote v)` and `quote (Section_value e) = Section (map
quote e)`; equivalently `evaluate [] t' = Ok (v, _)`. Proof: induction on the budget of
`reduce`. Theorem 5 at `d = 0` matches the Case on a Tag step with the evaluator step,
because the reducer substitutes the reduced payload into the branch while the evaluator
extends the environment with the payload value. The two closedness results remove the
neutral arms, so the two runs take matching steps at every node, and section fields agree
because both sides use `canonical` order. `test/finite_normalize_test.ml:143-149` compares
the two. Claim C7, to verify: no finite budget is proved to suffice for `reduce`, because
the matching bound needs strong normalization, which section 12 lists as open.

## 12. Not established

1. Fuel is not part of the typing relation. The relation of section 3 carries no budget,
   and `check` decides it only at a budget of at least `size(t)`. A `Resource_exhausted`
   result is neither acceptance nor refutation.
2. The finite-fragment inventory is mechanized under `proofs/` on Lean 4.33.1. Its
   theorem names and their transitive axiom sets are recorded in
   [validation](validation.md#m1-mechanization). These prove properties of the
   Lean deep embedding, whose differences from OCaml are recorded in
   [FIDELITY.md](../proofs/FIDELITY.md). Section 11.5's `normalize_agrees_with_run`
   assumes successful closed normalization and evaluation at independent budgets.
   Claim C7 remains an open successful-fuel obligation with no theorem declaration.
3. Strong normalization is not proved, and confluence is not proved. Section 11.4 assumes
   successful reduction at a supplied budget.
4. The host stack is unbounded. Fuel meters term node visits only. It does not meter
   host stack depth, allocation, sorting, list traversal, or type equality
   (`docs/finite-terms.md:156-160`). A deep input can exhaust the host stack first.
5. There is no eta. Normal forms are equal up to beta and canonical label order only, so
   two terms that Lean identifies by eta for a structure stay distinct here. This is the
   disclosed gap of decision D4.
6. Type equality rests on Lemma 0, which rests on the abstraction boundary of the `.mli`.
   No test asserts it.
7. The tests are evidence. They compare beta results, recheck substituted and normalized
   terms, and compare closed normal forms with `run` values on a bounded corpus. They do
   not prove the theorems.
