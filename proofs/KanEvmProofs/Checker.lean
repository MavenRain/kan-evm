import KanEvmProofs.Syntax
import KanEvmProofs.Check
import KanEvmProofs.Typing
import KanEvmProofs.Canonical
import KanEvmProofs.Budget

/-! # Checker soundness and completeness

This module holds row Theorem1 and row Theorem1-C1 of the stage brief.
`check_sound` and `check_complete` state docs/metatheory.md lines 110 to 134 for the checker of lib/finite_term.ml lines 62 to 108.
`check_error_not_typable` and `check_error_choice_varies` state claim C1 of docs/metatheory.md lines 135 to 146.
The proofs reuse Lemma0 of Canonical.lean and the size lemmas of Budget.lean, which is the module of Lemma1 and
Lemma2. Soundness runs on the structural gas of decision S2-D5, and completeness runs on the derivation.
Every proof here stays in term mode, so the module holds no tactic block at all.
-/

namespace Checker

/-- `ite_hit` reads the first arm of one two way branch of a definition.
`checkCore` at lib/finite_term.ml lines 62 to 105 tests one type equality and one label membership, and each test picks one arm.
-/
theorem ite_hit {c : Prop} [inst : Decidable c] {α : Type} {x y : α} (hc : c) :
    (if c then x else y) = x :=
  ite_elim (P := fun u : α => u = x) (fun _hc => rfl) (fun hn => absurd hc hn)

/-- `ite_miss` reads the second arm of one two way branch of a definition.
It is the partner of `ite_hit` for the failing test of lib/finite_term.ml lines 62 to 105.
-/
theorem ite_miss {c : Prop} [inst : Decidable c] {α : Type} {x y : α} (hc : ¬ c) :
    (if c then x else y) = y :=
  ite_elim (P := fun u : α => u = y) (fun h => absurd h hc) (fun _hn => rfl)

/-- `beq_notation` names the structural comparison that the `==` notation carries.
The comparison serves lib/finite_term.ml lines 67 and 100.
-/
theorem beq_notation (t u : Ty) : (t == u) = Ty.beq t u := rfl

/-- `beq_self` states that the comparison of lib/finite_term.ml lines 67 and 100 accepts one type against itself.
It reads Lemma0 of Canonical.lean, which docs/metatheory.md line 32 states.
-/
theorem beq_self (t : Ty) : (t == t) = true := (ty_beq_iff t t).mpr rfl

/-- `beq_eq` reads a successful comparison of lib/finite_term.ml lines 67 and 100 as an equality.
It reads Lemma0 of Canonical.lean, which docs/metatheory.md line 32 states.
-/
theorem beq_eq {t u : Ty} (h : (t == u) = true) : t = u := (ty_beq_iff t u).mp h

/-- `checkResult` is the result that a well typed term gives at one budget. docs/metatheory.md lines 132 to 134 state that
`check` returns success exactly when the term is well typed and the budget reaches `size(t)`, and Lemma2 of
Budget.lean fixes the spent amount. A budget under the size of the term stops at the tick of lib/finite_term.ml line 47.
-/
def checkResult (fuel n : Nat) : Res Nat :=
  if n ≤ fuel then .ok (fuel - n) else .error .resourceExhausted

/-- `nat_not_le_zero` refutes one positive bound at the empty budget.
The tick of lib/finite_term.ml line 47 stops at the empty budget.
-/
theorem nat_not_le_zero (n : Nat) : ¬ (1 + n ≤ 0) :=
  fun h => Nat.not_succ_le_zero n (cast (congrArg (fun z : Nat => z ≤ 0) (Nat.add_comm 1 n)) h)

/-- `nat_succ_pair` raises one bound over the node unit of `size`.
Each entered node of lib/finite_term.ml lines 62 to 105 pays one unit of the budget.
-/
theorem nat_succ_pair {n fuel : Nat} (h : n ≤ fuel) : 1 + n ≤ fuel + 1 :=
  cast (congrArg (fun z : Nat => z ≤ fuel + 1) (Nat.add_comm n 1)) (Nat.succ_le_succ h)

/-- `nat_pair_succ` lowers one bound over the node unit of `size`.
It is the partner of `nat_succ_pair` for the failing test of docs/metatheory.md lines 132 to 134.
-/
theorem nat_pair_succ {n fuel : Nat} (h : 1 + n ≤ fuel + 1) : n ≤ fuel :=
  Nat.le_of_succ_le_succ (cast (congrArg (fun z : Nat => z ≤ fuel + 1) (Nat.add_comm 1 n)) h)

/-- `nat_sub_pair` drops the node unit from both sides of one budget difference.
The tick of lib/finite_term.ml line 47 spends that unit before the arms run.
-/
theorem nat_sub_pair (fuel n : Nat) : fuel + 1 - (1 + n) = fuel - n :=
  (congrArg (fun z : Nat => fuel + 1 - z) (Nat.add_comm 1 n)).trans (Nat.succ_sub_succ fuel n)

/-- `checkResult_nil` gives the result of one empty walk of lib/finite_term.ml lines 103 to 105.
An empty entry list spends nothing, as Lemma2 of Budget.lean states.
-/
theorem checkResult_nil (fuel : Nat) : checkResult fuel 0 = .ok fuel := ite_hit (Nat.zero_le fuel)

/-- `checkResult_one` gives the result of one leaf of lib/finite_term.ml lines 65 to 72.
A leaf spends the one unit that the tick of line 47 takes.
-/
theorem checkResult_one (fuel : Nat) : checkResult (fuel + 1) 1 = .ok fuel :=
  ite_hit (Nat.succ_le_succ (Nat.zero_le fuel))

/-- `checkResult_zero_pos` gives the result of any term at the empty budget.
`size_pos` of Budget.lean gives one node at least, and the tick of lib/finite_term.ml line 47 stops at the empty budget.
-/
theorem checkResult_zero_pos {n : Nat} (h : 1 ≤ n) : checkResult 0 n = .error .resourceExhausted :=
  ite_miss (fun hbad => Nat.not_succ_le_zero 0 (Nat.le_trans h hbad))

/-- `checkResult_ok` reads one successful result as a bound and a difference. docs/metatheory.md lines 132 to 134 pair success with a budget that reaches the size.
-/
theorem checkResult_ok {fuel n r : Nat} (h : checkResult fuel n = .ok r) :
    n ≤ fuel ∧ r = fuel - n :=
  ite_elim (P := fun u : Res Nat => u = .ok r → n ≤ fuel ∧ r = fuel - n)
    (fun hc hq => ⟨hc, (Except.ok.inj hq).symm⟩)
    (fun _hc hq => (res_error_ne_ok hq).elim) h

/-- `checkResult_tick` moves one node unit across the result of one entered node.
The tick of lib/finite_term.ml line 47 runs first, so the node pays one unit at each arm.
-/
theorem checkResult_tick (fuel n : Nat) : checkResult (fuel + 1) (1 + n) = checkResult fuel n :=
  ite_elim (P := fun u : Res Nat => checkResult (fuel + 1) (1 + n) = u)
    (fun hc =>
      (ite_hit (nat_succ_pair hc)).trans
        (congrArg (fun z : Nat => (Except.ok z : Res Nat)) (nat_sub_pair fuel n)))
    (fun hn => ite_miss (fun hbad => hn (nat_pair_succ hbad)))

/-- `nat_add_le_of_sub` joins one head bound with one tail bound.
The chain of lib/finite_term.ml lines 103 to 105 spends the head amount first.
-/
theorem nat_add_le_of_sub {n m fuel : Nat} (hn : n ≤ fuel) (hm : m ≤ fuel - n) : n + m ≤ fuel :=
  Nat.le_trans (Nat.add_le_add_left hm n) (Nat.le_of_eq (Nat.add_sub_cancel' hn))

/-- `nat_sub_of_add_le` splits one joint bound into the tail bound.
It is the partner of `nat_add_le_of_sub` for the failing test of the same chain.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem nat_sub_of_add_le {n m fuel : Nat} (h : n + m ≤ fuel) : m ≤ fuel - n :=
  Nat.le_sub_of_add_le (cast (congrArg (fun z : Nat => z ≤ fuel) (Nat.add_comm n m)) h)

/-- `checkResult_comp` composes two results of one chain of lib/finite_term.ml lines 103 to 105.
The second run starts at the budget that the first run leaves, and the two spent amounts add.
Lemma2 of Budget.lean states that same sum for the entry lists.
-/
theorem checkResult_comp (fuel n m : Nat) :
    (checkResult fuel n >>= fun x => checkResult x m) = checkResult fuel (n + m) :=
  ite_elim (P := fun u : Res Nat => (u >>= fun x => checkResult x m) = checkResult fuel (n + m))
    (fun hc =>
      ite_elim (P := fun u : Res Nat => u = checkResult fuel (n + m))
        (fun hc2 =>
          (congrArg (fun z : Nat => (Except.ok z : Res Nat)) (Nat.sub_sub fuel n m)).trans
            (ite_hit (nat_add_le_of_sub hc hc2)).symm)
        (fun hn2 => (ite_miss (fun hbad => hn2 (nat_sub_of_add_le hbad))).symm))
    (fun hn =>
      (ite_miss (fun hbad => hn (Nat.le_trans (Nat.le_add_right n m) hbad))).symm)

/-- `gas_list` gives the gas of one entry list walk under the gas of the entered node.
Decision S2-D5 sets the gas of `check` at lib/finite_term.ml line 108 at two units per budget unit, and one list step follows each entered node.
-/
theorem gas_list {fuel gasPred : Nat} (h : 2 * (fuel + 1) + 1 ≤ gasPred + 1) :
    2 * fuel + 2 ≤ gasPred :=
  cast (congrArg (fun z : Nat => z ≤ gasPred) (Nat.mul_succ 2 fuel)) (Nat.le_of_succ_le_succ h)

/-- `gas_core` gives the gas of one nested node under the gas of the entered node.
Decision S2-D5 passes `gas - 1` at each nested call of lib/finite_term.ml lines 62 to 105.
-/
theorem gas_core {fuel gasPred : Nat} (h : 2 * (fuel + 1) + 1 ≤ gasPred + 1) :
    2 * fuel + 1 ≤ gasPred :=
  Nat.le_of_succ_le (gas_list h)

/-- `gas_core_of_list` gives the gas of one entry under the gas of the entry list.
`checkFields` and `checkBranches` of lib/finite_term.ml lines 103 to 105 pass `gas - 1` too.
-/
theorem gas_core_of_list {fuel gasPred : Nat} (h : 2 * fuel + 2 ≤ gasPred + 1) :
    2 * fuel + 1 ≤ gasPred :=
  Nat.le_of_succ_le_succ h

/-- `gas_drop` holds the gas bound at a budget that no run raises.
The branch walk of lib/finite_term.ml lines 86 to 95 starts at the budget that the scrutinee leaves, and that budget never rises.
-/
theorem gas_drop {x fuel gasPred : Nat} (hx : x ≤ fuel) (h : 2 * fuel + 2 ≤ gasPred) :
    2 * x + 2 ≤ gasPred :=
  Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul (Nat.le_refl 2) hx) 2) h

/-- `gas_step` holds the gas bound at a budget that one entry lowers.
Each entry of lib/finite_term.ml lines 103 to 105 spends one unit at least, per `size_pos` of
Budget.lean.
-/
theorem gas_step {x fuel gasPred : Nat} (hx : x + 1 ≤ fuel) (h : 2 * fuel + 1 ≤ gasPred) :
    2 * x + 2 ≤ gasPred :=
  Nat.le_trans
    (cast (congrArg (fun z : Nat => z ≤ 2 * fuel) (Nat.mul_succ 2 x))
      (Nat.mul_le_mul (Nat.le_refl 2) hx))
    (Nat.le_trans (Nat.le_succ (2 * fuel)) h)

/-- `sub_step` states that one spent entry leaves a strictly smaller budget.
The tick of lib/finite_term.ml line 47 runs at each entered node of an entry.
-/
theorem sub_step {fuel s : Nat} (hs : 1 ≤ s) (hle : s ≤ fuel) : fuel - s + 1 ≤ fuel :=
  Nat.sub_lt (Nat.lt_of_lt_of_le hs hle) hs

/-- `rest_le` reads the budget that one successful run leaves as no larger than the start.
Lemma1 of Budget.lean states that same order for the fueled functions of decision S2-D4.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem rest_le {x fuel n : Nat} (h : n ≤ fuel ∧ x = fuel - n) : x ≤ fuel :=
  cast (congrArg (fun z : Nat => z ≤ fuel) h.2.symm) (Nat.sub_le fuel n)

/-- `rest_lt` reads the budget that one successful entry leaves as strictly smaller.
`size_pos` of Budget.lean gives one node at least for the term of that entry.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem rest_lt {x fuel : Nat} (t : Term) (h : size t ≤ fuel ∧ x = fuel - size t) :
    x + 1 ≤ fuel :=
  cast (congrArg (fun z : Nat => z + 1 ≤ fuel) h.2.symm) (sub_step (size_pos t) h.1)

/-- `pairs_size` states that the aligned list carries the size of the written entry list.
`canonical` at lib/finite_term.ml lines 20 to 23 sorts the entries and `align` at lines 51 to 60 pairs each one with its fiber, and neither step changes the total size.
The three steps are `align_size`, `canonical_sorted` and `sort_size` of Budget.lean.
-/
theorem pairs_size (fibers : List (String × Ty)) (entries sorted : List (String × Term))
    (pairs : List (String × Ty × Term)) (hcanon : canonicalEntries entries = .ok sorted)
    (halign : align fibers sorted = .ok pairs) : sizePairs pairs = sizeEntries entries :=
  (align_size fibers sorted pairs halign).trans
    ((congrArg sizeEntries (canonical_sorted entries sorted hcanon)).trans (sort_size entries))

mutual
/-- `check_core_sound` is part one of row Theorem1 for `checkCore`.
It states docs/metatheory.md lines 112 to 117 for lib/finite_term.ml lines 62 to 105.
A successful run at any gas and at any budget gives one typing derivation of the rules of docs/metatheory.md lines 40 to 51.
The recursion runs on the structural gas of decision S2-D5, together with the two list partners, since the sorted entry list of lines 81 and 89 is no syntactic sublist.
-/
theorem check_core_sound : ∀ (gas fuel : Nat) (ctx : List Ty) (t : Term) (a : Ty) (rest : Nat),
    checkCore gas fuel ctx t a = .ok rest → HasType ctx t a
  | 0, _fuel, _ctx, _t, _a, _rest, h => (res_error_ne_ok h).elim
  | gasPred + 1, _fuel, ctx, t, a, rest, h =>
      match res_bind_ok h with
      | ⟨fuel2, _htick, h2⟩ =>
          match t, h2 with
          | .var index, hh =>
              match res_bind_ok hh with
              | ⟨_actual, hact, h3⟩ =>
                  ite_elim (P := fun u : Res Nat => u = .ok rest → HasType ctx (.var index) a)
                    (fun hc _hq =>
                      HasType.var ctx index a
                        (hact.trans
                          (congrArg (fun z : Ty => (Except.ok z : Res Ty)) (beq_eq hc))))
                    (fun _hc hq => (res_error_ne_ok hq).elim) h3
          | .atom name, hh =>
              match a, hh with
              | .atoms labels, h3 =>
                  ite_elim
                    (P := fun u : Res Nat =>
                      u = .ok rest → HasType ctx (.atom name) (.atoms labels))
                    (fun hc _hq => HasType.atom ctx name labels hc)
                    (fun _hc hq => (res_error_ne_ok hq).elim) h3
              | .lan .., h3 => (res_error_ne_ok h3).elim
              | .ran .., h3 => (res_error_ne_ok h3).elim
          | .tag label payload, hh =>
              match a, hh with
              | .lan fibers, h3 =>
                  match res_bind_ok h3 with
                  | ⟨fiber, hfiber, h4⟩ =>
                      HasType.tag ctx label payload fibers fiber hfiber
                        (check_core_sound gasPred fuel2 ctx payload fiber rest h4)
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .ran .., h3 => (res_error_ne_ok h3).elim
          | .«section» entries, hh =>
              match a, hh with
              | .ran fibers, h3 =>
                  match res_bind_ok h3 with
                  | ⟨sorted, hsorted, h4⟩ =>
                      match res_bind_ok h4 with
                      | ⟨pairs, hpairs, h5⟩ =>
                          HasType.«section» ctx entries fibers sorted pairs hsorted hpairs
                            (check_fields_sound gasPred fuel2 ctx pairs rest h5)
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .lan .., h3 => (res_error_ne_ok h3).elim
          | .«case» scrutinee st branches, hh =>
              match st, hh with
              | .lan fibers, h3 =>
                  match res_bind_ok h3 with
                  | ⟨sorted, hsorted, h4⟩ =>
                      match res_bind_ok h4 with
                      | ⟨pairs, hpairs, h5⟩ =>
                          match res_bind_ok h5 with
                          | ⟨fuel3, hscrut, h6⟩ =>
                              HasType.«case» ctx scrutinee fibers branches sorted pairs a
                                hsorted hpairs
                                (check_core_sound gasPred fuel2 ctx scrutinee (.lan fibers) fuel3
                                  hscrut)
                                (check_branches_sound gasPred fuel3 ctx pairs a rest h6)
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .ran .., h3 => (res_error_ne_ok h3).elim
          | .project field st label, hh =>
              match st, hh with
              | .ran fibers, h3 =>
                  match res_bind_ok h3 with
                  | ⟨_actual, hact, h4⟩ =>
                      ite_elim
                        (P := fun u : Res Nat =>
                          u = .ok rest → HasType ctx (.project field (.ran fibers) label) a)
                        (fun hc hq =>
                          HasType.project ctx field fibers label a
                            (hact.trans
                              (congrArg (fun z : Ty => (Except.ok z : Res Ty)) (beq_eq hc)))
                            (check_core_sound gasPred fuel2 ctx field (.ran fibers) rest hq))
                        (fun _hc hq => (res_error_ne_ok hq).elim) h4
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .lan .., h3 => (res_error_ne_ok h3).elim

/-- `check_fields_sound` is the field list partner of `check_core_sound`.
`checkFields` replaces the higher order walk of lib/finite_term.ml lines 103 to 105, which docs/metatheory.md lines 118 to 121 name the aligned key premise of
SECTION.
-/
theorem check_fields_sound : ∀ (gas fuel : Nat) (ctx : List Ty)
    (pairs : List (String × Ty × Term)) (rest : Nat),
    checkFields gas fuel ctx pairs = .ok rest → HasTypeEntries ctx pairs .none
  | 0, _fuel, _ctx, _pairs, _rest, h => (res_error_ne_ok h).elim
  | _gasPred + 1, _fuel, ctx, [], _rest, _h => HasTypeEntries.nil ctx .none
  | gasPred + 1, fuel, ctx, (label, fiber, field) :: more, rest, h =>
      match res_bind_ok h with
      | ⟨fuel2, hhead, h2⟩ =>
          HasTypeEntries.field ctx label fiber field more
            (check_core_sound gasPred fuel ctx field fiber fuel2 hhead)
            (check_fields_sound gasPred fuel2 ctx more rest h2)

/-- `check_branches_sound` is the branch list partner of `check_core_sound`.
`checkBranches` replaces the higher order walk of lib/finite_term.ml lines 103 to 105, and each body runs at the extended context of docs/metatheory.md lines 122 to 128.
-/
theorem check_branches_sound : ∀ (gas fuel : Nat) (ctx : List Ty)
    (pairs : List (String × Ty × Term)) (expected : Ty) (rest : Nat),
    checkBranches gas fuel ctx pairs expected = .ok rest →
      HasTypeEntries ctx pairs (.some expected)
  | 0, _fuel, _ctx, _pairs, _expected, _rest, h => (res_error_ne_ok h).elim
  | _gasPred + 1, _fuel, ctx, [], expected, _rest, _h =>
      HasTypeEntries.nil ctx (.some expected)
  | gasPred + 1, fuel, ctx, (label, payloadType, body) :: more, expected, rest, h =>
      match res_bind_ok h with
      | ⟨fuel2, hhead, h2⟩ =>
          HasTypeEntries.branch ctx label payloadType body more expected
            (check_core_sound gasPred fuel (payloadType :: ctx) body expected fuel2 hhead)
            (check_branches_sound gasPred fuel2 ctx more expected rest h2)
end

/-- `nat_shift_assoc` regroups the node unit of one case term.
`size` at Check.lean writes the case node as `1 + size scrutinee + sizeEntries branches`, and the tick of lib/finite_term.ml line 47 takes the node unit alone.
-/
theorem nat_shift_assoc (s b : Nat) : 1 + s + b = 1 + (s + b) := Nat.add_assoc 1 s b

/-- `core_zero_fuel` gives the run of any term at the empty budget.
The tick of lib/finite_term.ml line 47 stops there, and `size_pos` of
Budget.lean gives one node at least, so the two sides agree.
-/
theorem core_zero_fuel (gasPred : Nat) (ctx : List Ty) (t : Term) (a : Ty) :
    checkCore (gasPred + 1) 0 ctx t a = checkResult 0 (size t) :=
  (checkResult_zero_pos (size_pos t)).symm

/-- `core_var` reads the var arm of lib/finite_term.ml lines 65 to 67 after the tick of line 47. -/
theorem core_var (gasPred f : Nat) (ctx : List Ty) (index : Nat) (a : Ty) :
    checkCore (gasPred + 1) (f + 1) ctx (.var index) a
      = («variable» index ctx >>= fun actual =>
          if actual == a then .ok f else .error .typeMismatch) := rfl

/-- `core_atom` reads the atom arm of lib/finite_term.ml lines 68 to 72 after the tick of line 47. -/
theorem core_atom (gasPred f : Nat) (ctx : List Ty) (name : String) (labels : List String) :
    checkCore (gasPred + 1) (f + 1) ctx (.atom name) (.atoms labels)
      = (if labels.contains name then .ok f else .error (.invalidAtom name)) := rfl

/-- `core_tag` reads the tag arm of lib/finite_term.ml lines 73 to 77 after the tick of line 47. -/
theorem core_tag (gasPred f : Nat) (ctx : List Ty) (label : String) (payload : Term)
    (fibers : List (String × Ty)) :
    checkCore (gasPred + 1) (f + 1) ctx (.tag label payload) (.lan fibers)
      = (lookup label fibers >>= fun fiber => checkCore gasPred f ctx payload fiber) := rfl

/-- `core_section` reads the section arm of lib/finite_term.ml lines 78 to 85 after the tick. -/
theorem core_section (gasPred f : Nat) (ctx : List Ty) (entries : List (String × Term))
    (fibers : List (String × Ty)) :
    checkCore (gasPred + 1) (f + 1) ctx (.«section» entries) (.ran fibers)
      = (canonicalEntries entries >>= fun sorted =>
          align fibers sorted >>= fun pairs => checkFields gasPred f ctx pairs) := rfl

/-- `core_case` reads the case arm of lib/finite_term.ml lines 86 to 95 after the tick. -/
theorem core_case (gasPred f : Nat) (ctx : List Ty) (scrutinee : Term)
    (fibers : List (String × Ty)) (branches : List (String × Term)) (expected : Ty) :
    checkCore (gasPred + 1) (f + 1) ctx (.«case» scrutinee (.lan fibers) branches) expected
      = (canonicalEntries branches >>= fun sorted =>
          align fibers sorted >>= fun pairs =>
            checkCore gasPred f ctx scrutinee (.lan fibers) >>= fun rest =>
              checkBranches gasPred rest ctx pairs expected) := rfl

/-- `core_project` reads the project arm of lib/finite_term.ml lines 96 to 102 after the tick. -/
theorem core_project (gasPred f : Nat) (ctx : List Ty) (field : Term)
    (fibers : List (String × Ty)) (label : String) (expected : Ty) :
    checkCore (gasPred + 1) (f + 1) ctx (.project field (.ran fibers) label) expected
      = (lookup label fibers >>= fun actual =>
          if actual == expected then checkCore gasPred f ctx field (.ran fibers)
          else .error .typeMismatch) := rfl

/-- `fields_nil` reads the empty field walk of lib/finite_term.ml lines 103 to 105. -/
theorem fields_nil (gasPred fuel : Nat) (ctx : List Ty) :
    checkFields (gasPred + 1) fuel ctx [] = .ok fuel := rfl

/-- `fields_cons` reads one step of the field walk of lib/finite_term.ml lines 103 to 105. -/
theorem fields_cons (gasPred fuel : Nat) (ctx : List Ty) (label : String) (fiber : Ty)
    (field : Term) (rest : List (String × Ty × Term)) :
    checkFields (gasPred + 1) fuel ctx ((label, fiber, field) :: rest)
      = (checkCore gasPred fuel ctx field fiber >>= fun left =>
          checkFields gasPred left ctx rest) := rfl

/-- `branches_nil` reads the empty branch walk of lib/finite_term.ml lines 103 to 105. -/
theorem branches_nil (gasPred fuel : Nat) (ctx : List Ty) (expected : Ty) :
    checkBranches (gasPred + 1) fuel ctx [] expected = .ok fuel := rfl

/-- `branches_cons` reads one step of the branch walk of lib/finite_term.ml lines 103 to 105.
The body runs at the context that the payload type extends, as lines 92 and 93 do.
-/
theorem branches_cons (gasPred fuel : Nat) (ctx : List Ty) (label : String) (payloadType : Ty)
    (body : Term) (rest : List (String × Ty × Term)) (expected : Ty) :
    checkBranches (gasPred + 1) fuel ctx ((label, payloadType, body) :: rest) expected
      = (checkCore gasPred fuel (payloadType :: ctx) body expected >>= fun left =>
          checkBranches gasPred left ctx rest expected) := rfl

/-- `EntriesResult` names the run of one entry list at the mode of `HasTypeEntries`.
The field mode of decision S2-D7 runs `checkFields` and the branch mode runs
`checkBranches`, which are the two images of `check_many` at lib/finite_term.ml lines 103 to 105.
One name for both runs gives one list partner of the completeness induction.
-/
def EntriesResult (mode : Option Ty) (gas fuel : Nat) (ctx : List Ty)
    (pairs : List (String × Ty × Term)) : Res Nat :=
  match mode with
  | .none => checkFields gas fuel ctx pairs
  | .some expected => checkBranches gas fuel ctx pairs expected

mutual
/-- `check_core_complete` is part two of row Theorem1 for `checkCore`.
It states docs/metatheory.md lines 118 to 134 for lib/finite_term.ml lines 62 to 105.
One derivation of the rules of docs/metatheory.md lines 40 to 51 gives the exact result of the checker at every gas that reaches the bound and at every budget, which is success at a budget that reaches the size of the term and
`Err.resourceExhausted` under that size. The recursion runs on the derivation, together with the entry list partner, and
Lemma2 of Budget.lean gives the spent amount that `checkResult` writes.
-/
theorem check_core_complete : ∀ (ctx : List Ty) (t : Term) (a : Ty), HasType ctx t a →
    ∀ (gas fuel : Nat), 2 * fuel + 1 ≤ gas →
      checkCore gas fuel ctx t a = checkResult fuel (size t)
  | _ctx, _t, _a, _d, 0, fuel, hg => absurd hg (Nat.not_succ_le_zero (2 * fuel))
  | ctx, t, a, _d, gasPred + 1, 0, _hg => core_zero_fuel gasPred ctx t a
  | ctx, .var index, a, HasType.var _ _ _ h, gasPred + 1, f + 1, _hg =>
      (core_var gasPred f ctx index a).trans
        ((congrArg (fun z : Res Ty =>
            z >>= fun actual =>
              if actual == a then (Except.ok f : Res Nat) else .error .typeMismatch) h).trans
          ((ite_hit (beq_self a)).trans (checkResult_one f).symm))
  | ctx, .atom name, .atoms labels, HasType.atom _ _ _ h, gasPred + 1, f + 1, _hg =>
      (core_atom gasPred f ctx name labels).trans
        ((ite_hit h).trans (checkResult_one f).symm)
  | ctx, .tag label payload, .lan fibers, HasType.tag _ _ _ _ fiber hlook hpayload,
      gasPred + 1, f + 1, hg =>
      (core_tag gasPred f ctx label payload fibers).trans
        ((congrArg (fun z : Res Ty => z >>= fun fb => checkCore gasPred f ctx payload fb)
            hlook).trans
          ((check_core_complete ctx payload fiber hpayload gasPred f (gas_core hg)).trans
            (checkResult_tick f (size payload)).symm))
  | ctx, .«section» entries, .ran fibers,
      HasType.«section» _ _ _ sorted pairs hcanon halign hentries,
      gasPred + 1, f + 1, hg =>
      (core_section gasPred f ctx entries fibers).trans
        ((congrArg (fun z : Res (List (String × Term)) =>
            z >>= fun s => align fibers s >>= fun p => checkFields gasPred f ctx p) hcanon).trans
          ((congrArg (fun z : Res (List (String × Ty × Term)) =>
              z >>= fun p => checkFields gasPred f ctx p) halign).trans
            ((check_entries_complete ctx pairs .none hentries gasPred f (gas_list hg)).trans
              ((congrArg (fun z : Nat => checkResult f z)
                  (pairs_size fibers entries sorted pairs hcanon halign)).trans
                (checkResult_tick f (sizeEntries entries)).symm))))
  | ctx, .«case» scrutinee (.lan fibers) branches, expected,
      HasType.«case» _ _ _ _ sorted pairs _ hcanon halign hscrut hbranches,
      gasPred + 1, f + 1, hg =>
      (core_case gasPred f ctx scrutinee fibers branches expected).trans
        ((congrArg (fun z : Res (List (String × Term)) =>
            z >>= fun s => align fibers s >>= fun p =>
              checkCore gasPred f ctx scrutinee (.lan fibers) >>= fun left =>
                checkBranches gasPred left ctx p expected) hcanon).trans
          ((congrArg (fun z : Res (List (String × Ty × Term)) =>
              z >>= fun p =>
                checkCore gasPred f ctx scrutinee (.lan fibers) >>= fun left =>
                  checkBranches gasPred left ctx p expected) halign).trans
            ((congrArg (fun z : Res Nat =>
                z >>= fun left => checkBranches gasPred left ctx pairs expected)
                (check_core_complete ctx scrutinee (.lan fibers) hscrut gasPred f
                  (gas_core hg))).trans
              ((bind_congr_ok (fun x hx =>
                  check_entries_complete ctx pairs (.some expected) hbranches gasPred x
                    (gas_drop (rest_le (checkResult_ok hx)) (gas_list hg)))).trans
                ((checkResult_comp f (size scrutinee) (sizePairs pairs)).trans
                  ((congrArg (fun z : Nat => checkResult f (size scrutinee + z))
                      (pairs_size fibers branches sorted pairs hcanon halign)).trans
                    ((checkResult_tick f (size scrutinee + sizeEntries branches)).symm.trans
                      (congrArg (fun z : Nat => checkResult (f + 1) z)
                        (nat_shift_assoc (size scrutinee) (sizeEntries branches)).symm))))))))
  | ctx, .project sectionTerm (.ran fibers) label, a,
      HasType.project _ _ _ _ _ hlook hsec,
      gasPred + 1, f + 1, hg =>
      (core_project gasPred f ctx sectionTerm fibers label a).trans
        ((congrArg (fun z : Res Ty =>
            z >>= fun actual =>
              if actual == a then checkCore gasPred f ctx sectionTerm (.ran fibers)
              else .error .typeMismatch) hlook).trans
          ((ite_hit (beq_self a)).trans
            ((check_core_complete ctx sectionTerm (.ran fibers) hsec gasPred f
                (gas_core hg)).trans
              (checkResult_tick f (size sectionTerm)).symm)))

/-- `check_entries_complete` is the entry list partner of `check_core_complete`.
It covers the field walk and the branch walk of lib/finite_term.ml lines 103 to 105 at one statement, per the mode of decision
S2-D7, and it states the sum of docs/metatheory.md lines 118 to 128 for the aligned entry list.
-/
theorem check_entries_complete : ∀ (ctx : List Ty) (pairs : List (String × Ty × Term))
    (mode : Option Ty), HasTypeEntries ctx pairs mode →
    ∀ (gas fuel : Nat), 2 * fuel + 2 ≤ gas →
      EntriesResult mode gas fuel ctx pairs = checkResult fuel (sizePairs pairs)
  | _ctx, _pairs, _mode, _d, 0, fuel, hg =>
      absurd hg (Nat.not_succ_le_zero (2 * fuel + 1))
  | ctx, [], .none, HasTypeEntries.nil _ _, gasPred + 1, fuel, _hg =>
      (fields_nil gasPred fuel ctx).trans (checkResult_nil fuel).symm
  | ctx, [], .some expected, HasTypeEntries.nil _ _, gasPred + 1, fuel, _hg =>
      (branches_nil gasPred fuel ctx expected).trans (checkResult_nil fuel).symm
  | ctx, (label, fiber, fieldTerm) :: rest, .none,
      HasTypeEntries.field _ _ _ _ _ hfield hrest,
      gasPred + 1, fuel, hg =>
      (fields_cons gasPred fuel ctx label fiber fieldTerm rest).trans
        ((congrArg (fun z : Res Nat => z >>= fun left => checkFields gasPred left ctx rest)
            (check_core_complete ctx fieldTerm fiber hfield gasPred fuel
              (gas_core_of_list hg))).trans
          ((bind_congr_ok (fun x hx =>
              check_entries_complete ctx rest .none hrest gasPred x
                (gas_step (rest_lt fieldTerm (checkResult_ok hx)) (gas_core_of_list hg)))).trans
            (checkResult_comp fuel (size fieldTerm) (sizePairs rest))))
  | ctx, (label, payloadType, body) :: rest, .some expected,
      HasTypeEntries.branch _ _ _ _ _ _ hbody hrest,
      gasPred + 1, fuel, hg =>
      (branches_cons gasPred fuel ctx label payloadType body rest expected).trans
        ((congrArg (fun z : Res Nat =>
            z >>= fun left => checkBranches gasPred left ctx rest expected)
            (check_core_complete (payloadType :: ctx) body expected hbody gasPred fuel
              (gas_core_of_list hg))).trans
          ((bind_congr_ok (fun x hx =>
              check_entries_complete ctx rest (.some expected) hrest gasPred x
                (gas_step (rest_lt body (checkResult_ok hx)) (gas_core_of_list hg)))).trans
            (checkResult_comp fuel (size body) (sizePairs rest))))
end

/-- `check_of_derivation` reads the public `check` of lib/finite_term.ml lines 107 and 108 at one typable term.
The gas of decision S2-D5 reaches the bound of `check_core_complete` at every budget, so the run is the result that
`checkResult` writes.
-/
theorem check_of_derivation (fuel : Nat) (g : List Ty) (t : Term) (a : Ty) (d : HasType g t a) :
    check fuel g t a
      = (checkResult fuel (size t) >>= fun (_remaining : Nat) => (Except.ok () : Res Unit)) :=
  congrArg (fun z : Res Nat => z >>= fun (_remaining : Nat) => (Except.ok () : Res Unit))
    (check_core_complete g t a d (2 * fuel + 2) fuel (Nat.le_succ (2 * fuel + 1)))

end Checker

/-- `check_sound` is part one of row Theorem1 of the stage brief.
It states docs/metatheory.md lines 112 to 117. A successful run of `check` at lib/finite_term.ml lines 107 and 108 gives one derivation of the rules of docs/metatheory.md lines 40 to 51 at the same context, term and type.
The budget of decision S2-D4 leaves no trace in the derivation, so the statement holds at every budget.
-/
theorem check_sound (fuel : Nat) (g : List Ty) (t : Term) (a : Ty)
    (h : check fuel g t a = .ok ()) : HasType g t a :=
  match res_bind_ok h with
  | ⟨rest, hcore, _hk⟩ => Checker.check_core_sound (2 * fuel + 2) fuel g t a rest hcore

/-- `check_complete` is part two of row Theorem1 of the stage brief.
It states docs/metatheory.md lines 118 to 134. `check_core_complete` of Checker.lean line 442 gives the exact result of the checker at every gas above the bound and at every budget, and
`Checker.ite_hit` closes the hypothesis `size t ≤ fuel` of this statement.
-/
theorem check_complete (fuel : Nat) (g : List Ty) (t : Term) (a : Ty) (d : HasType g t a)
    (hle : size t ≤ fuel) : check fuel g t a = .ok () :=
  (Checker.check_of_derivation fuel g t a d).trans
    (congrArg (fun z : Res Nat => z >>= fun (_remaining : Nat) => (Except.ok () : Res Unit))
      (Checker.ite_hit hle))

/-- `check_error_not_typable` is part one of row Theorem1-C1 of the stage brief.
It states claim C1 of docs/metatheory.md lines 135 to 146. An error other than
`Err.resourceExhausted` refutes the typing judgement at every budget, since a typable term gives success or gives
`Err.resourceExhausted` alone.
-/
theorem check_error_not_typable (fuel : Nat) (g : List Ty) (t : Term) (a : Ty) (e : Err)
    (hne : e ≠ .resourceExhausted) (h : check fuel g t a = .error e) : ¬ HasType g t a :=
  fun d =>
    ite_elim
      (P := fun u : Res Nat =>
        (u >>= fun (_remaining : Nat) => (Except.ok () : Res Unit)) = .error e → False)
      (fun _hc hq => res_error_ne_ok hq.symm)
      (fun _hn hq => hne (Except.error.inj hq).symm)
      ((Checker.check_of_derivation fuel g t a d).symm.trans h)

/-- `witnessTerm` is the term of claim C1 at docs/metatheory.md lines 135 to 146.
It is one case term at a tagged scrutinee, and its one branch returns an atom that the expected type does not hold.
Its size is four nodes.
-/
def witnessTerm : Term :=
  .«case» (.tag "a" (.atom "x")) (.lan [("a", .atoms ["x"])]) [("a", .atom "y")]

/-- `witnessType` is the expected type of claim C1 at docs/metatheory.md lines 135 to 146. -/
def witnessType : Ty := .atoms ["x"]

/-- `check_error_choice_varies` is part two of row Theorem1-C1 of the stage brief.
It states the concrete pair of budgets of docs/metatheory.md lines 135 to 146.
The budget three stops at the tick of lib/finite_term.ml line 47 inside the branch walk and reports
`Err.resourceExhausted`, and the budget four reaches the branch body and reports
`Err.invalidAtom`, so one term reports two errors at two budgets.
-/
theorem check_error_choice_varies :
    check 3 [] witnessTerm witnessType = .error .resourceExhausted
      ∧ check 4 [] witnessTerm witnessType = .error (.invalidAtom "y") := ⟨rfl, rfl⟩
