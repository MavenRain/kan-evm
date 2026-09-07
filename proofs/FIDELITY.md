# Fidelity table of the Lean mechanization

Stage S2-S0 of the kan-evm M1 mechanization, 2026-09-06. Decision S2-D9 fixes this table.

The table holds one row per Lean definition that stage S2-S0 landed. `ml` is
lib/finite_term.ml and `mli` is lib/finite_term.mli. The columns are the Lean name, the OCaml
lines the definition mirrors, the recursion shape, the charge points and any difference from
the OCaml source. A charge point is a call of `tick`, which mirrors ml:47 and is the one place
that spends the budget, per decision S2-D4. The whole package holds five charge points:
`checkCore`, `shift`, `sub`, `evaluate` and `reduce`.

This table is a trusted artifact. A reviewer signs it in the build log. No proof depends on it.
The executable half of the fidelity claim is proofs/KanEvmProofs/Fidelity.lean, which gate
S2-G5 builds, and the measured fuel numbers of decision S2-D10 hold there through `rfl`.

## KanEvmProofs/Syntax.lean

| Lean name | OCaml lines | recursion shape | charge points | difference |
| --- | --- | --- | --- | --- |
| `Ty` | ml:1 | none, a nested inductive over `List (String x Ty)` | none | The constructors are exported, so a hand built type need not satisfy `Ty.Canonical`. Decision S2-D2 states that predicate wherever a proof needs it. |
| `Term` | mli:21-28, ml:31-38 | none, a nested inductive over `List (String x Term)` | none | `section` and `case` take the guillemet form, since each name is a Lean keyword. |
| `Err` | mli:4-13, ml:2-11 | none | none | `invalidVariable` carries a `Nat`, so the negative index test of ml:44 has no image. |
| `Res` | ml:13 | none | none | `Except Err` replaces the OCaml `result` type and the bind operator of ml:13. |
| `labelLe` | ml:21, ml:26 | none | none | It names the `String.compare` order that the two OCaml sorts use. |
| `insertLabel` | ml:26 | structural on the label list | none | It is the step of `sortLabels` and has no OCaml name. |
| `sortLabels` | ml:26 | structural on the label list | none | Insertion sort replaces `List.sort`. Decision S2-D5 names `List.mergeSort`, which is well founded at Lean v4.33.1 and does not reduce through `rfl`, and the examples of decision S2-D10 need that reduction. Both functions return one ascending order. |
| `insertFiber` | ml:21 | structural on the fiber list | none | It is the step of `sortFibers` and has no OCaml name. |
| `sortFibers` | ml:21 | structural on the fiber list | none | Insertion sort replaces `List.sort`, for the reason of `sortLabels`. |
| `Ty.beq` | ml:67, ml:100 | mutual structural with `Ty.beqFibers` | none | It is the structural image of the OCaml `=` at the two type comparisons. Lemma0 relates it to equality on canonical types. |
| `Ty.beqFibers` | ml:67, ml:100 | mutual structural with `Ty.beq` | none | It is the list partner that the nested inductive of decision S2-D1 needs. |
| `instance : BEq Ty` | ml:67, ml:100 | none | none | It gives the `==` notation for `Ty.beq`. |
| `Ty.SortedLabels` | ml:20-23 | structural on the label list | none | It states part one of decision S2-D2. The OCaml sort establishes the order and states nothing. |
| `Ty.DistinctLabels` | ml:15-18 | structural on the label list | none | It states the adjacent test of `unique` as a proposition. |
| `Ty.Canonical` | ml:20-23, mli:3 | mutual structural with `Ty.CanonicalFibers` | none | It states as a proposition what the abstraction boundary of mli:3 gives the OCaml checker. |
| `Ty.CanonicalFibers` | ml:20-23 | mutual structural with `Ty.Canonical` | none | It is the list partner for the nested inductive. |
| `unique` | ml:15-18 | structural on the label list | none | none |
| `canonical` | ml:20-23 | none | none | The sort cannot fail, so `duplicateLabel` is the one error of this function. |
| `atoms` | ml:25-27 | none | none | none |
| `lan` | ml:28 | none | none | A successful result is canonical when every fiber given is canonical. The sort reaches the outer label list alone, and the exported `Ty` constructors let a caller supply a noncanonical fiber, which ml:28 cannot receive. |
| `ran` | ml:29 | none | none | A successful result is canonical when every fiber given is canonical. The sort reaches the outer label list alone, and the exported `Ty` constructors let a caller supply a noncanonical fiber, which ml:29 cannot receive. |

## KanEvmProofs/Check.lean

| Lean name | OCaml lines | recursion shape | charge points | difference |
| --- | --- | --- | --- | --- |
| `tick` | ml:47 | none | itself, the one charge point of the package | The OCaml test `fuel <= 0` becomes a test against zero over `Nat`. |
| `lookup` | ml:40-41 | structural through `List.lookup` | none | It is total and returns `Res`, per decision S2-D3. A miss becomes `unexpectedLabel`, as ml:41 does. |
| `variable` | ml:43-45 | none, an index read | none | It is total and returns `Res`. The negative index test of ml:44 has no image over `Nat`. The name takes the guillemet form, since it is a Lean keyword. |
| `align` | ml:51-60 | structural on both lists | none | none |
| `insertEntry` | ml:21 | structural on the entry list | none | It is the step of `sortEntries` and has no OCaml name. |
| `sortEntries` | ml:21 | structural on the entry list | none | Insertion sort over an arbitrary payload replaces `List.sort`, for the reason of `sortLabels`. |
| `canonicalEntries` | ml:20-23 | none | none | It is `canonical` over a term payload, which the field sort of ml:81 and the branch sort of ml:89 need. |
| `size` | ml:31-38 | mutual structural with `sizeEntries` | none | It counts one unit per term node. It has no OCaml name and it is the measure of Lemma2. |
| `sizeEntries` | ml:31-38 | mutual structural with `size` | none | It is the list partner of `size`. |
| `checkCore` | ml:62-105 | mutual with `checkFields` and `checkBranches`, structural on the gas of decision S2-D5 | one `tick` per entered node, as ml:63 does | The gas parameter replaces a recursion that Lean rejects, since ml:81 and ml:89 visit a canonicalized list that is no syntactic sublist. `check_gas_irrelevant` of Budget.lean pays for it. |
| `checkFields` | ml:103-105 | mutual, structural on the gas and on the entry list | none | It replaces the higher order `check_many`, which structural recursion also rejects. |
| `checkBranches` | ml:103-105 | mutual, structural on the gas and on the entry list | none | It replaces `check_many` at the branch mode, which extends the context with the fiber type, as ml:92-93 does. |
| `check` | ml:107-108 | none | none | It calls `checkCore` at the gas `2 * fuel + 2`, per decision S2-D5. It drops the remaining budget, as ml:108 does. |

## KanEvmProofs/Subst.lean

| Lean name | OCaml lines | recursion shape | charge points | difference |
| --- | --- | --- | --- | --- |
| `shift` | ml:112-135 | mutual structural on the term with `shiftEntries` | one `tick` per term node, as ml:113 does | It is the first order raising instance of the higher order `map_variables`, per decision S2-D5. The cutoff rises one unit inside each `case` branch and nowhere else, as ml:125 does. |
| `shiftEntries` | ml:130-135 | mutual structural with `shift` | none, since the `tick` sits in `shift` | It mirrors the explicit recursion of `map_entries` at ml:130-135 one for one and threads the budget. |
| `sub` | ml:112-151 | mutual structural on the term with `subEntries` | one `tick` per term node, as ml:113 does | It is the first order replacing instance of `map_variables`. The hit arm calls `shift` on the replacement, which is a call of another function and needs no gas. |
| `subEntries` | ml:130-135 | mutual structural with `sub` | none, since the `tick` sits in `sub` | It mirrors the explicit recursion of `map_entries` at ml:130-135 one for one and threads the budget. |
| `occurrences` | none | mutual structural on the term with `occurrencesEntries` | none | It has no OCaml image. It counts `var d` at binder depth `d` and supplies the `n` of Lemma2b and of Theorem3-C2. |
| `occurrencesEntries` | none | mutual structural with `occurrences` | none | It is the list partner of `occurrences`. |
| `substituteCore` | ml:139-151 | none | none | The OCaml form builds a callback and hands it to `map_variables` at ml:151. The Lean form is one call of `sub` at depth zero, per decision S2-D5. |
| `substitute` | ml:153-156 | none | none | It threads one budget through two `checkCore` calls and `substituteCore`, and it adds no charge point, per decision S2-D4. The gas of each check is `2 * fuel + 2`. It drops the remaining budget. |

## KanEvmProofs/Eval.lean

| Lean name | OCaml lines | recursion shape | charge points | difference |
| --- | --- | --- | --- | --- |
| `Value` | ml:231-234 | none, a nested inductive over `List (String x Value)` | none | none |
| `evaluate` | ml:236-260 | mutual structural on the term with `evaluateEntries` and `evaluateBranch` | one `tick` per entered node, as ml:237 does | The OCaml form recurses on the result of a branch lookup, which is no subterm, and Lean rejects it. The mutual triple of decision S2-D5 replaces it. The OCaml arm evaluates the sorted field list at ml:246 and this arm evaluates the source list and sorts the values, which agrees on every success in value and in remaining budget and can name a different error when two fields fail with different errors. The contract of lib/finite_term.mli line 78, a section evaluated in canonical label order, holds on every success. `evaluate` is no exported name, and `run` at ml:268-270 checks the term first, so the reachable difference is one `resourceExhausted` report, which both orders return alike. |
| `evaluateEntries` | ml:261-266 | mutual structural with `evaluate` | none, since the `tick` sits in `evaluate` | It mirrors the explicit recursion of `evaluate_entries` at ml:261-266 one for one and threads the budget. |
| `evaluateBranch` | ml:252-253 | mutual structural on the branch list | none | It walks the syntactic branch list and takes the first label match, as `List.assoc_opt` does. It never ticks, so the charge count stays the OCaml one. |
| `run` | ml:268-270 | none | none | It threads one budget through `checkCore` and `evaluate` at the empty context and the empty environment, and it adds no charge point. It drops the remaining budget, as ml:270 does. |
| `quote` | none | mutual structural on the value with `quoteEntries` | none | It has no OCaml image in lib/finite_term.ml. It states the map of docs/metatheory.md lines 383 to 386, which Theorem6-11.5 needs. The test at test/finite_normalize_test.ml lines 17 to 21 holds the same map. |
| `quoteEntries` | none | mutual structural with `quote` | none | It is the list partner of `quote`. |

## KanEvmProofs/Typing.lean

Decision S2-D7 fixes these three inductives and their two companions. None of them carries fuel,
as docs/metatheory.md line 38 states, so none of them holds a charge point. The OCaml column
names the checker arm that each relation mirrors.

| Lean name | OCaml lines | recursion shape | charge points | difference |
| --- | --- | --- | --- | --- |
| `HasType` | ml:62-105 | mutual inductive with `HasTypeEntries` | none | It carries no fuel. No rule carries a `Ty.Canonical` side condition, since ml:62-105 tests no annotation and no context entry for canonicity, so a successful `check` states no canonicity fact and Theorem1 of the stage brief states its implication with no canonicity hypothesis. Decision S2-D7 asked for the side conditions, and the stage review of 2026-09-06 removed them. Canonicity stays a hypothesis of each theorem that needs it, as the Theorem4 row writes it. |
| `HasTypeEntries` | ml:103-105 | mutual inductive with `HasType` | none | Its `Option Ty` mode selects the field mode of ml:84 or the branch mode of ml:92-93. |
| `ValueHasType` | ml:231-234, ml:236-266 | mutual inductive with `ValueHasTypeEntries` | none | It states V-ATOM, V-TAG and V-SECTION of docs/metatheory.md lines 67 to 70. Value typing needs no context, since a value holds no variable. |
| `ValueHasTypeEntries` | ml:20-23 | mutual inductive with `ValueHasType` | none | It states the key equality of docs/metatheory.md line 69 as a pointwise walk of two lists that hold one ascending label order. |
| `EnvHasType` | ml:250-253, ml:268-270 | structural inductive on both lists | none | It states the pointwise environment rule of docs/metatheory.md lines 75 to 77. |

## KanEvmProofs/Reduce.lean

| Lean name | OCaml lines | recursion shape | charge points | difference |
| --- | --- | --- | --- | --- |
| `reduceFields` | ml:211-216 | structural on the field list, with the step as a parameter | none, since the `tick` sits in `reduce` | It takes the step `reduce gasPred` as a first order parameter and passes the gas unchanged, per decision S2-D6. |
| `reduceBranches` | ml:219-225 | structural on the branch list, with the step as a parameter | none, since the `tick` sits in `reduce` | It reduces each body at the expected type of the whole node, as ml:223 does, and the aligned fiber directs no step, as ml:217-218 states. It takes the step `reduce gasPred` as a first order parameter and passes the gas unchanged, per decision S2-D6. |
| `reduce` | ml:162-225 | structural on the gas of decision S2-D6 | one `tick` per entered node, as ml:163 does, and the `tick` runs ahead of every nested call | The OCaml form recurses on a substituted body, which is no subterm. The gas parameter replaces that recursion, and an empty gas returns `resourceExhausted`. `reduce_gas_irrelevant` of NormalizeCore.lean pays for it. The `checkCore` block of Check.lean and `reduce` hold the two gas disciplines, per decisions S2-D5 and S2-D6, so `checkFields`, `checkBranches` and `EntriesResult` of Checker.lean line 427 take a gas argument too. |
| `normalize` | ml:227-229 | none | none | It threads one budget through `checkCore` and `reduce`, and it adds no charge point. The gas of `reduce` is one unit above the budget that the check leaves, which is enough, since one nested call drops the gas one unit. |

## KanEvmProofs/Fidelity.lean

These definitions are the fixtures of the measured examples of decision S2-D10. Each one is test
data, not a model definition, so the OCaml column names test/finite_normalize_test.ml and the
last three columns are empty for every row. The examples that use them hold no name.

| Lean name | OCaml lines | recursion shape | charge points | difference |
| --- | --- | --- | --- | --- |
| `Fidelity.tyA` | test:24 | none | none | none |
| `Fidelity.tyOne` | test:26 | none | none | none |
| `Fidelity.tySum` | test:27 | none | none | none |
| `Fidelity.tyOneSum` | test:28 | none | none | none |
| `Fidelity.tyTwo` | test:30 | none | none | none |
| `Fidelity.tagCase` | test:51-52 | none | none | none |
| `Fidelity.sectionProject` | test:39, test:54 | none | none | none |
| `Fidelity.neutralCase` | test:47-48 | none | none | none |
| `Fidelity.innerRedex` | test:32-33, test:60 | none | none | none |
| `Fidelity.neutralBranchRedex` | test:61-62 | none | none | none |
| `Fidelity.shifting` | test:67 | none | none | none |
| `Fidelity.shiftingUnderNeutral` | test:68-69 | none | none | none |
| `Fidelity.neutralProject` | test:39, test:74 | none | none | none |
| `Fidelity.projectOfNeutralCase` | test:76-78 | none | none | none |
| `Fidelity.projectOfNeutralCaseReduced` | test:80-81 | none | none | none |

## Measured fuel numbers

The eleven fuel examples of proofs/KanEvmProofs/Fidelity.lean close with `rfl` at the fuel numbers
that test/finite_normalize_test.ml states, and five smart constructor examples of that module
close with `rfl` on the canonical forms. The boundary helper at test:42-46 asks for two runs
per case, one at the exact budget and one at that budget less one unit, so the table holds both.

| example | context | fuel | result |
| --- | --- | --- | --- |
| `tagCase` at `tyOne`, test:50-52 | empty | 10 | `Term.atom "x"` |
| `tagCase` at `tyOne`, test:43-44 | empty | 9 | `Err.resourceExhausted` |
| `sectionProject` at `tyA`, test:53-54 | empty | 8 | `Term.atom "y"` |
| `sectionProject` at `tyA`, test:43-44 | empty | 7 | `Err.resourceExhausted` |
| `neutralCase` at `tyA`, test:55-56 | `tySum` | 6 | `Fidelity.neutralCase` |
| `neutralCase` at `tyA`, test:43-44 | `tySum` | 5 | `Err.resourceExhausted` |
| `neutralBranchRedex` at `tyA`, test:61-64 | `tySum` | 100000 | `Fidelity.neutralCase` |
| `shiftingUnderNeutral` at `tyA`, test:68-70 | `tySum` | 100000 | `Fidelity.neutralCase` |
| `shifting` at `tyA`, test:71-72 | `tyA` and `tySum` | 100000 | `Term.var 0` |
| `neutralProject` at `tyA`, test:74-75 | `tyTwo` | 100000 | `Fidelity.neutralProject` |
| `projectOfNeutralCase` at `tyA`, test:76-82 | `tyTwo` and `tySum` | 100000 | `Fidelity.projectOfNeutralCaseReduced` |

The fuel 100000 is the budget of the `norm` helper at test:31. It is no minimal budget, and the
five cases at fuel 100000 of decision S2-D10 use it as the test does.

## Recursion shapes that do not transfer

Three OCaml shapes have no structural image in Lean, and decision S2-D5 fixes the replacement of
each one. `evaluate` recurses on the result of a branch lookup, and the mutual triple with
`evaluateBranch` replaces it. `check_term` visits a canonicalized entry list that is no syntactic
sublist, and the gas parameter of `checkCore` with `checkFields` and `checkBranches` replaces it.
`map_variables` is higher order and `substitute_core` calls it on a term that is no subterm, and
the two first order pairs `shift` with `shiftEntries` and `sub` with `subEntries` replace it.
`reduce` recurses on a substituted body, and the gas parameter of decision S2-D6 replaces that
recursion. The gas parameter is never observable, which `check_gas_irrelevant` and
`reduce_gas_irrelevant` state.

## Signature

A reviewer of stage S2-S0 signs this table in the build log, per decision S2-D9.
