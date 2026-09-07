import KanEvmProofs.Budget
import KanEvmProofs.Typing
import KanEvmProofs.Weakening

/-! # Substitution at binder depth

This module holds row Theorem3, row Theorem3-Cor and row Theorem3-C2 of the stage brief.
`substitution_at_depth` states docs/metatheory.md lines 187 to 208.
`substitution_zero` states the corollary of docs/metatheory.md lines 209 to 212.
`substitute_budget_sufficient` states claim C2 of docs/metatheory.md lines 213 to 216.
`sub` of Subst.lean mirrors `substitute_core` at lib/finite_term.ml lines 139 to 151, and it threads a budget, so each row theorem reads the term of one successful run.
The proofs reuse `weakening_shift` of Weakening.lean for the index at the depth, per the depends_on column of row
Theorem3, and they reuse the cost lemmas of Budget.lean.
-/

namespace Substitution

/-- `tickOne` spends one unit of a budget that holds one unit above the rest.
`tick` of Check.lean is the one charge point of decision S2-D4.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem tickOne (j : Nat) : tick (1 + j) = .ok j :=
  (congrArg tick (Nat.add_comm 1 j)).trans rfl

/-- `natOneShift` moves the leading unit of a budget out of one sum.
It carries the arithmetic of docs/metatheory.md lines 79 to 91 in term mode.
-/
theorem natOneShift (k j : Nat) : 1 + k + j = 1 + (k + j) := Nat.add_assoc 1 k j

/-- `tickShape` spends one unit of a budget that one node and one rest describe.
It reads the size of one term node, as docs/metatheory.md lines 79 to 91 state.
-/
theorem tickShape (k j : Nat) : tick (1 + k + j) = .ok (k + j) :=
  (congrArg tick (natOneShift k j)).trans (tickOne (k + j))

/-- `natTwoShift` moves the leading unit of a budget out of two summands.
The `case` node of lib/finite_term.ml lines 86 to 95 reads one scrutinee and one branch list.
-/
theorem natTwoShift (s b j : Nat) : 1 + s + b + j = 1 + (s + b + j) :=
  (congrArg (fun z : Nat => z + j) (Nat.add_assoc 1 s b)).trans (Nat.add_assoc 1 (s + b) j)

/-- `tickTwo` spends one unit of a budget that two summands and one rest describe.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem tickTwo (s b j : Nat) : tick (1 + s + b + j) = .ok (s + b + j) :=
  (congrArg tick (natTwoShift s b j)).trans (tickOne (s + b + j))

/-- `natListFuel` splits the budget of one entry list between the head and the tail.
The replacement cost of docs/metatheory.md lines 209 to 216 counts one occurrence at a time, so the head cost and the tail cost of one list add.
-/
theorem natListFuel (bS bB bP bQ m j : Nat) :
    bS + bB + (bP + bQ) * m + j = bS + bP * m + (bB + bQ * m + j) :=
  (congrArg (fun z : Nat => bS + bB + z + j) (Nat.add_mul bP bQ m)).trans
    ((congrArg (fun z : Nat => z + j)
        ((Nat.add_assoc (bS + bB) (bP * m) (bQ * m)).symm.trans
          (congrArg (fun z : Nat => z + bQ * m) (Nat.add_right_comm bS bB (bP * m))))).trans
      ((congrArg (fun z : Nat => z + j) (Nat.add_assoc (bS + bP * m) bB (bQ * m))).trans
        (Nat.add_assoc (bS + bP * m) (bB + bQ * m) j)))

/-- `natCaseFuel` splits the budget of one `case` node between the scrutinee and the branches.
The depth rises inside each branch, per decision S2-D8, and the two occurrence counts add.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem natCaseFuel (s b p q m j : Nat) :
    1 + s + b + (p + q) * m + j = 1 + (s + p * m + (b + q * m + j)) :=
  (natListFuel (1 + s) b p q m j).trans
    ((congrArg (fun z : Nat => z + (b + q * m + j)) (Nat.add_assoc 1 s (p * m))).trans
      (Nat.add_assoc 1 (s + p * m) (b + q * m + j)))

/-- `tickCaseFuel` spends the one unit of a `case` node and splits the rest of the budget.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem tickCaseFuel (s b p q m j : Nat) :
    tick (1 + s + b + (p + q) * m + j) = .ok (s + p * m + (b + q * m + j)) :=
  (congrArg tick (natCaseFuel s b p q m j)).trans (tickOne (s + p * m + (b + q * m + j)))

/-- `natEqOfNotLt` reads the third arm of the table of docs/metatheory.md lines 181 to 185.
An index that is neither below the depth nor above it equals the depth.
-/
theorem natEqOfNotLt (i k : Nat) (h1 : ¬ i < k) (h2 : ¬ k < i) : i = k :=
  match Nat.lt_or_ge i k with
  | .inl hlt => (h1 hlt).elim
  | .inr hge =>
      match Nat.lt_or_ge k i with
      | .inl hgt => (h2 hgt).elim
      | .inr hge2 => Nat.le_antisymm hge2 hge

/-- `natZeroFuel` reads the budget of one node that holds no occurrence of the depth.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem natZeroFuel (m j : Nat) : 1 + 0 * m + j = 1 + j :=
  (congrArg (fun z : Nat => 1 + z + j) (Nat.zero_mul m)).trans
    (congrArg (fun z : Nat => z + j) (Nat.add_zero 1))

/-- `natOneFuel` reads the budget of one variable node that holds the depth itself.
The replacement raises the term `r`, and that raise spends `size r`, per Budget.lean.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem natOneFuel (m j : Nat) : 1 + 1 * m + j = 1 + (m + j) :=
  (congrArg (fun z : Nat => 1 + z + j) (Nat.one_mul m)).trans (natOneShift m j)

/-- `natNilFuel` reads the budget of the empty entry list, which spends nothing.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem natNilFuel (m j : Nat) : 0 + 0 * m + j = j :=
  (congrArg (fun z : Nat => 0 + z + j) (Nat.zero_mul m)).trans (Nat.zero_add j)

/-- `natTwoMul` reads the doubled body size of claim C2 of docs/metatheory.md lines 213 to 216.
`substitute` reads the body twice, once in the check and once in the replacement.
-/
theorem natTwoMul (n : Nat) : 2 * n = n + n :=
  (Nat.succ_mul 1 n).trans (congrArg (fun z : Nat => z + n) (Nat.one_mul n))

/-- `natSplitTwo` orders the three costs of claim C2 as one run of `substitute` spends them.
The run spends the body size, then the replacement cost, then the body size again.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem natSplitTwo (sb bB p : Nat) : 2 * sb + bB + p = p + (sb + bB) + sb :=
  (congrArg (fun z : Nat => z + bB + p) (natTwoMul sb)).trans
    ((Nat.add_right_comm (sb + sb) bB p).trans
      ((congrArg (fun z : Nat => z + bB)
          ((Nat.add_right_comm sb sb p).trans
            (congrArg (fun z : Nat => z + sb) (Nat.add_comm sb p)))).trans
        ((Nat.add_right_comm (p + sb) sb bB).trans
          (congrArg (fun z : Nat => z + sb) (Nat.add_assoc p sb bB)))))

/-- `natSuccMul` reads the occurrence factor of claim C2 as one sum.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem natSuccMul (p m : Nat) : (p + 1) * m = p * m + m :=
  (Nat.add_mul p 1 m).trans (congrArg (fun z : Nat => p * m + z) (Nat.one_mul m))

/-- `fuelHead` splits the budget of claim C2 at the check of the replacement.
That check spends `size r`, as `check_core_cost` of Budget.lean states.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem fuelHead (sb sr occ : Nat) : 2 * sb + (occ + 1) * sr = sr + (2 * sb + occ * sr) :=
  (congrArg (fun z : Nat => 2 * sb + z) (natSuccMul occ sr)).trans
    ((Nat.add_assoc (2 * sb) (occ * sr) sr).symm.trans
      (Nat.add_comm (2 * sb + occ * sr) sr))

/-- `fuelBody` splits the budget that the check of the replacement leaves at the body check.
That check spends `size b`, as `check_core_cost` of Budget.lean states.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem fuelBody (sb bB : Nat) : 2 * sb + bB = sb + (sb + bB) :=
  (congrArg (fun z : Nat => z + bB) (natTwoMul sb)).trans (Nat.add_assoc sb sb bB)

/-- `fuelSplit` states that the budget of claim C2 plus one rest equals a budget that runs.
The three costs are the replacement cost, the body size and the replacement size.
It states claim C2 of docs/metatheory.md lines 213 to 216 as one equation.
-/
theorem fuelSplit (sb sr occ p : Nat) :
    2 * sb + (occ + 1) * sr + p = p + (sb + occ * sr) + sb + sr :=
  ((congrArg (fun z : Nat => 2 * sb + z + p) (natSuccMul occ sr)).trans
      (congrArg (fun z : Nat => z + p) (Nat.add_assoc (2 * sb) (occ * sr) sr).symm)).trans
    ((Nat.add_right_comm (2 * sb + occ * sr) sr p).trans
      (congrArg (fun z : Nat => z + sr) (natSplitTwo sb (occ * sr) p)))

mutual
/-- `shiftRun` runs `shift` of Subst.lean at the exact budget that the raise spends.
`shift_cost` of Budget.lean states that cost, and this lemma builds the run itself.
The raise of docs/metatheory.md lines 193 to 198 needs one run at a budget that no run exceeds.
-/
theorem shiftRun : ∀ (t : Term) (c d j : Nat),
    shift c d (size t + j) t = .ok (Weakening.shiftPure c d t, j)
  | .var _index, _c, _d, j => res_bind_mk (a := j) (tickOne j) rfl
  | .atom _label, _c, _d, j => res_bind_mk (a := j) (tickOne j) rfl
  | .tag _label payload, c, d, j =>
      res_bind_mk (a := size payload + j) (tickShape (size payload) j)
        (res_bind_mk (a := (Weakening.shiftPure c d payload, j)) (shiftRun payload c d j) rfl)
  | .«section» fields, c, d, j =>
      res_bind_mk (a := sizeEntries fields + j) (tickShape (sizeEntries fields) j)
        (res_bind_mk (a := (Weakening.shiftPureEntries c d fields, j))
          (shiftEntriesRun fields c d j) rfl)
  | .«case» scrutinee _scrutineeType branches, c, d, j =>
      res_bind_mk (a := size scrutinee + sizeEntries branches + j)
        (tickTwo (size scrutinee) (sizeEntries branches) j)
        (res_bind_mk (a := (Weakening.shiftPure c d scrutinee, sizeEntries branches + j))
          ((congrArg (fun z : Nat => shift c d z scrutinee)
            (Nat.add_assoc (size scrutinee) (sizeEntries branches) j)).trans
            (shiftRun scrutinee c d (sizeEntries branches + j)))
          (res_bind_mk (a := (Weakening.shiftPureEntries (c + 1) d branches, j))
            (shiftEntriesRun branches (c + 1) d j) rfl))
  | .project field _sectionType _label, c, d, j =>
      res_bind_mk (a := size field + j) (tickShape (size field) j)
        (res_bind_mk (a := (Weakening.shiftPure c d field, j)) (shiftRun field c d j) rfl)

/-- `shiftEntriesRun` is the entry list partner of `shiftRun`.
`shiftEntries` of Subst.lean holds no charge point, so the list cost is the sum of the fields.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem shiftEntriesRun : ∀ (entries : List (String × Term)) (c d j : Nat),
    shiftEntries c d (sizeEntries entries + j) entries
      = .ok (Weakening.shiftPureEntries c d entries, j)
  | [], _c, _d, j =>
      congrArg
        (fun z : Nat =>
          (Except.ok (([] : List (String × Term)), z) : Res (List (String × Term) × Nat)))
        (Nat.zero_add j)
  | (_label, field) :: rest, c, d, j =>
      res_bind_mk (a := (Weakening.shiftPure c d field, sizeEntries rest + j))
        ((congrArg (fun z : Nat => shift c d z field)
          (Nat.add_assoc (size field) (sizeEntries rest) j)).trans
          (shiftRun field c d (sizeEntries rest + j)))
        (res_bind_mk (a := (Weakening.shiftPureEntries c d rest, j))
          (shiftEntriesRun rest c d j) rfl)
end

mutual
/-- `subPure` is the replacement of `sub` of Subst.lean with no budget.
It reads the table of docs/metatheory.md lines 181 to 185 at the depth `d`.
An index below the depth stays, an index above it drops one unit, and the index at the depth becomes the replacement raised
`d` units.
The depth rises one unit inside each `case` branch, per decision S2-D8.
-/
def subPure (d : Nat) (r : Term) (t : Term) : Term :=
  match t with
  | .var index =>
      if index < d then .var index
      else if d < index then .var (index - 1) else Weakening.shiftPure 0 d r
  | .atom label => .atom label
  | .tag label payload => .tag label (subPure d r payload)
  | .«section» fields => .«section» (subPureEntries d r fields)
  | .«case» scrutinee scrutineeType branches =>
      .«case» (subPure d r scrutinee) scrutineeType (subPureEntries (d + 1) r branches)
  | .project field sectionType label => .project (subPure d r field) sectionType label

/-- `subPureEntries` is the entry list partner of `subPure` for the nested inductive of S2-D1.
It keeps the source order of the labels, as `map_entries` at lib/finite_term.ml lines 130 to 135 does, and the depth reaches each entry unchanged.
-/
def subPureEntries (d : Nat) (r : Term) (entries : List (String × Term)) : List (String × Term) :=
  match entries with
  | [] => []
  | (label, field) :: rest => (label, subPure d r field) :: subPureEntries d r rest
end

/-- `subPureVar` names the variable arm of `subPure` as one conditional term.
It states the three rows of the table of docs/metatheory.md lines 181 to 185.
-/
theorem subPureVar (d : Nat) (r : Term) (index : Nat) :
    subPure d r (Term.var index)
      = if index < d then Term.var index
        else if d < index then Term.var (index - 1) else Weakening.shiftPure 0 d r := rfl

/-- `subVarRun` runs `sub` of Subst.lean on one variable node at the exact budget it spends.
The budget of the arm at the depth carries the raise of the replacement, which spends `size r`.
It states the table of docs/metatheory.md lines 181 to 185 with the cost of `sub_cost`.
-/
theorem subVarRun (index d : Nat) (r : Term) (j : Nat) :
    sub d r (size (Term.var index) + occurrences d (Term.var index) * size r + j) (Term.var index)
      = .ok (subPure d r (Term.var index), j) :=
  match Nat.decLt index d with
  | .isTrue hlt =>
      (congrArg (fun z : Nat => sub d r z (Term.var index))
        ((congrArg (fun z : Nat => 1 + z * size r + j) (if_neg (Nat.ne_of_lt hlt))).trans
          (natZeroFuel (size r) j))).trans
        (res_bind_mk (a := j) (tickOne j)
          ((if_pos hlt).trans
            (congrArg (fun z : Term => (Except.ok (z, j) : Res (Term × Nat)))
              (if_pos hlt).symm)))
  | .isFalse hnlt =>
      match Nat.decLt d index with
      | .isTrue hgt =>
          (congrArg (fun z : Nat => sub d r z (Term.var index))
            ((congrArg (fun z : Nat => 1 + z * size r + j) (if_neg (Nat.ne_of_gt hgt))).trans
              (natZeroFuel (size r) j))).trans
            (res_bind_mk (a := j) (tickOne j)
              (((if_neg hnlt).trans (if_pos hgt)).trans
                (congrArg (fun z : Term => (Except.ok (z, j) : Res (Term × Nat)))
                  ((if_neg hnlt).trans (if_pos hgt)).symm)))
      | .isFalse hngt =>
          (congrArg (fun z : Nat => sub d r z (Term.var index))
            ((congrArg (fun z : Nat => 1 + z * size r + j)
              (if_pos (natEqOfNotLt index d hnlt hngt))).trans
              (natOneFuel (size r) j))).trans
            (res_bind_mk (a := size r + j) (tickOne (size r + j))
              (((if_neg hnlt).trans (if_neg hngt)).trans
                ((shiftRun r 0 d j).trans
                  (congrArg (fun z : Term => (Except.ok (z, j) : Res (Term × Nat)))
                    ((if_neg hnlt).trans (if_neg hngt)).symm))))

mutual
/-- `subRun` runs `sub` of Subst.lean at the exact budget that the replacement spends.
`sub_cost` of Budget.lean states that cost, and this lemma builds the run itself.
The cost is `size t + occurrences d t * size r`, which claim C2 of docs/metatheory.md lines 213 to 216 reads.
-/
theorem subRun : ∀ (t : Term) (d : Nat) (r : Term) (j : Nat),
    sub d r (size t + occurrences d t * size r + j) t = .ok (subPure d r t, j)
  | .var index, d, r, j => subVarRun index d r j
  | .atom label, d, r, j =>
      (congrArg (fun z : Nat => sub d r z (Term.atom label)) (natZeroFuel (size r) j)).trans
        (res_bind_mk (a := j) (tickOne j) rfl)
  | .tag _label payload, d, r, j =>
      res_bind_mk (a := size payload + occurrences d payload * size r + j)
        (tickTwo (size payload) (occurrences d payload * size r) j)
        (res_bind_mk (a := (subPure d r payload, j)) (subRun payload d r j) rfl)
  | .«section» fields, d, r, j =>
      res_bind_mk (a := sizeEntries fields + occurrencesEntries d fields * size r + j)
        (tickTwo (sizeEntries fields) (occurrencesEntries d fields * size r) j)
        (res_bind_mk (a := (subPureEntries d r fields, j)) (subEntriesRun fields d r j) rfl)
  | .«case» scrutinee _scrutineeType branches, d, r, j =>
      res_bind_mk
        (a := size scrutinee + occurrences d scrutinee * size r
          + (sizeEntries branches + occurrencesEntries (d + 1) branches * size r + j))
        (tickCaseFuel (size scrutinee) (sizeEntries branches) (occurrences d scrutinee)
          (occurrencesEntries (d + 1) branches) (size r) j)
        (res_bind_mk
          (a := (subPure d r scrutinee,
            sizeEntries branches + occurrencesEntries (d + 1) branches * size r + j))
          (subRun scrutinee d r
            (sizeEntries branches + occurrencesEntries (d + 1) branches * size r + j))
          (res_bind_mk (a := (subPureEntries (d + 1) r branches, j))
            (subEntriesRun branches (d + 1) r j) rfl))
  | .project field _sectionType _label, d, r, j =>
      res_bind_mk (a := size field + occurrences d field * size r + j)
        (tickTwo (size field) (occurrences d field * size r) j)
        (res_bind_mk (a := (subPure d r field, j)) (subRun field d r j) rfl)

/-- `subEntriesRun` is the entry list partner of `subRun`.
`subEntries` of Subst.lean holds no charge point, so the list cost is the sum of the fields.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem subEntriesRun : ∀ (entries : List (String × Term)) (d : Nat) (r : Term) (j : Nat),
    subEntries d r (sizeEntries entries + occurrencesEntries d entries * size r + j) entries
      = .ok (subPureEntries d r entries, j)
  | [], _d, r, j =>
      congrArg
        (fun z : Nat =>
          (Except.ok (([] : List (String × Term)), z) : Res (List (String × Term) × Nat)))
        (natNilFuel (size r) j)
  | (_label, field) :: rest, d, r, j =>
      res_bind_mk (a := (subPure d r field,
          sizeEntries rest + occurrencesEntries d rest * size r + j))
        ((congrArg (fun z : Nat => sub d r z field)
          (natListFuel (size field) (sizeEntries rest) (occurrences d field)
            (occurrencesEntries d rest) (size r) j)).trans
          (subRun field d r (sizeEntries rest + occurrencesEntries d rest * size r + j)))
        (res_bind_mk (a := (subPureEntries d r rest, j)) (subEntriesRun rest d r j) rfl)
end

/-- `subRunAt` rewrites one successful run of `sub` at the budget that `sub_cost` reads.
The budget of a successful run is the cost plus the remaining budget, so `subRun` applies.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem subRunAt (d : Nat) (r t : Term) (fuel remaining : Nat) (t' : Term)
    (h : sub d r fuel t = Except.ok (t', remaining)) :
    sub d r fuel t = Except.ok (subPure d r t, remaining) :=
  Eq.mp
    (congrArg (fun z : Nat => sub d r z t = Except.ok (subPure d r t, remaining))
      ((Nat.add_comm (size t + occurrences d t * size r) remaining).trans
        (sub_cost t d r fuel t' remaining h)))
    (subRun t d r remaining)

/-- `subOkPure` relates `sub` of Subst.lean to `subPure` at every budget that succeeds.
`sub` threads a budget and returns one pair, and the term of that pair is the replacement alone.
It mirrors `map_variables` at lib/finite_term.ml lines 112 to 151, whose budget carries no term.
-/
theorem subOkPure (d : Nat) (r t : Term) (fuel remaining : Nat) (t' : Term)
    (h : sub d r fuel t = Except.ok (t', remaining)) : t' = subPure d r t :=
  congrArg Prod.fst (Except.ok.inj (h.symm.trans (subRunAt d r t fuel remaining t' h)))

/-- `subTriples` replaces the term of each aligned triple at the depth `d`.
The triple list is the one `align` returns at lib/finite_term.ml lines 51 to 60.
-/
def subTriples (d : Nat) (r : Term) (pairs : List (String × Ty × Term)) :
    List (String × Ty × Term) :=
  match pairs with
  | [] => []
  | (label, fiber, body) :: rest => (label, fiber, subPure d r body) :: subTriples d r rest

/-- `labelsSub` states that the replacement keeps every label of one entry list.
It mirrors `map_entries` at lib/finite_term.ml lines 130 to 135, which reads no label.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the replacement.
-/
theorem labelsSub (d : Nat) (r : Term) :
    ∀ (entries : List (String × Term)),
      (subPureEntries d r entries).map Prod.fst = entries.map Prod.fst
  | [] => rfl
  | (label, _field) :: rest =>
      congrArg (fun (z : List String) => label :: z) (labelsSub d r rest)

/-- `insertSub` moves the replacement across one insertion step of the sort.
The insertion reads the labels alone, and the replacement keeps every label.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem insertSub (d : Nat) (r : Term) (label : String) (field : Term) :
    ∀ (entries : List (String × Term)),
      insertEntry (label, subPure d r field) (subPureEntries d r entries)
        = subPureEntries d r (insertEntry (label, field) entries)
  | [] => rfl
  | (key, payload) :: tail =>
      (Weakening.iteCongr rfl
          (congrArg (fun (z : List (String × Term)) => (key, subPure d r payload) :: z)
            (insertSub d r label field tail))).trans
        (Weakening.iteMap (subPureEntries d r) ((label, field) :: (key, payload) :: tail)
          ((key, payload) :: insertEntry (label, field) tail)).symm

/-- `sortSub` moves the replacement across the whole sort of `sortEntries` of Check.lean.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem sortSub (d : Nat) (r : Term) :
    ∀ (entries : List (String × Term)),
      sortEntries (subPureEntries d r entries) = subPureEntries d r (sortEntries entries)
  | [] => rfl
  | (label, field) :: rest =>
      (congrArg (insertEntry (label, subPure d r field)) (sortSub d r rest)).trans
        (insertSub d r label field (sortEntries rest))

/-- `canonicalSub` moves the replacement across `canonicalEntries` of Check.lean.
The canonical step reads the labels alone, and the replacement keeps every label.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem canonicalSub (d : Nat) (r : Term) (entries : List (String × Term)) :
    canonicalEntries (subPureEntries d r entries)
      = (canonicalEntries entries).map (subPureEntries d r) :=
  (congrArg (fun (z : List (String × Term)) => Weakening.canonicalStep (z.map Prod.fst) z)
      (sortSub d r entries)).trans
    ((congrArg
        (fun (ls : List String) =>
          Weakening.canonicalStep ls (subPureEntries d r (sortEntries entries)))
        (labelsSub d r (sortEntries entries))).trans
      (Weakening.bindConstMap (unique ((sortEntries entries).map Prod.fst)) (sortEntries entries)
        (subPureEntries d r)))

/-- `alignStepSub` moves the replacement across one aligned entry of `align`.
It mirrors the successful arm of `align` at lib/finite_term.ml lines 51 to 60.
-/
theorem alignStepSub (m : Res (List (String × Ty × Term))) (d : Nat) (r : Term)
    (key : String) (fiber : Ty) (field : Term) :
    (m.map (subTriples d r) >>= fun (z : List (String × Ty × Term)) =>
        Except.ok ((key, fiber, subPure d r field) :: z))
      = (m >>= fun (z : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, field) :: z)).map (subTriples d r) :=
  Except.rec
    (motive := fun (w : Res (List (String × Ty × Term))) =>
      (w.map (subTriples d r) >>= fun (z : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, subPure d r field) :: z))
        = (w >>= fun (z : List (String × Ty × Term)) =>
            Except.ok ((key, fiber, field) :: z)).map (subTriples d r))
    (fun (_e : Err) => rfl) (fun (_a : List (String × Ty × Term)) => rfl) m

/-- `alignSub` moves the replacement across the whole walk of `align`.
It mirrors `align` at lib/finite_term.ml lines 51 to 60, which reads the labels alone.
-/
theorem alignSub (d : Nat) (r : Term) :
    ∀ (fibers : List (String × Ty)) (entries : List (String × Term)),
      align fibers (subPureEntries d r entries) = (align fibers entries).map (subTriples d r)
  | [], [] => rfl
  | .cons .., [] => rfl
  | [], .cons .. => rfl
  | (key, fiber) :: types, (label, field) :: terms =>
      Weakening.ordMap (Except.map (subTriples d r))
        (Except.error (Err.missingLabel key))
        (align types terms >>= fun (z : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, field) :: z))
        (Except.error (Err.unexpectedLabel label))
        (Except.error (Err.missingLabel key))
        (align types (subPureEntries d r terms) >>= fun (z : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, subPure d r field) :: z))
        (Except.error (Err.unexpectedLabel label)) rfl
        ((congrArg
            (fun (w : Res (List (String × Ty × Term))) =>
              w >>= fun (z : List (String × Ty × Term)) =>
                Except.ok ((key, fiber, subPure d r field) :: z))
            (alignSub d r types terms)).trans
          (alignStepSub (align types terms) d r key fiber field)) rfl
        (compare key label)

/-- `varBelow` reads one index below the depth at the context that drops the removed entry.
It states the first row of docs/metatheory.md lines 199 to 203, where the entry lies in the shared prefix of both contexts.
-/
theorem varBelow : ∀ (dd g : List Ty) (a : Ty) (i : Nat) (bt : Ty),
    «variable» i (dd ++ a :: g) = Except.ok bt → i < dd.length →
      «variable» i (dd ++ g) = Except.ok bt
  | [], _g, _a, i, _bt, _hv, hlt => (Nat.not_lt_zero i hlt).elim
  | x :: dd', g, a, i, bt, hv, hlt =>
      match i, hlt, hv with
      | 0, _h0, hv0 =>
          (Weakening.variableZero x (dd' ++ g)).trans
            (congrArg (fun (z : Ty) => (Except.ok z : Res Ty))
              (Weakening.headEq x bt (dd' ++ a :: g) hv0))
      | k + 1, hk, hvk =>
          Weakening.variableStep x (dd' ++ g) k bt
            (varBelow dd' g a k bt
              (Weakening.variableStepBack x (dd' ++ a :: g) k bt hvk)
              (Nat.lt_of_succ_lt_succ hk))

/-- `varAbove` reads one index above the depth at the context that drops the removed entry.
It states the second row of docs/metatheory.md lines 199 to 203, where the index drops one unit.
-/
theorem varAbove : ∀ (dd g : List Ty) (a : Ty) (i : Nat) (bt : Ty), dd.length ≤ i →
    «variable» (i + 1) (dd ++ a :: g) = Except.ok bt → «variable» i (dd ++ g) = Except.ok bt
  | [], g, a, i, bt, _hle, hv => Weakening.variableStepBack a g i bt hv
  | x :: dd', g, a, i, bt, hle, hv =>
      match i, hv, hle with
      | 0, _hv0, h0 => (Nat.not_succ_le_zero dd'.length h0).elim
      | k + 1, hvk, hk =>
          Weakening.variableStep x (dd' ++ g) k bt
            (varAbove dd' g a k bt (Nat.le_of_succ_le_succ hk)
              (Weakening.variableStepBack x (dd' ++ a :: g) (k + 1) bt hvk))

/-- `varAboveIndex` reads the index above the depth in the shape that `subPure` returns.
`subPure` returns `Term.var (index - 1)` there, so this lemma names that index.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem varAboveIndex (dd g : List Ty) (a : Ty) (index : Nat) (bt : Ty)
    (hgt : dd.length < index) (hv : «variable» index (dd ++ a :: g) = Except.ok bt) :
    «variable» (index - 1) (dd ++ g) = Except.ok bt :=
  match index, hv, hgt with
  | 0, _hv0, h0 => (Nat.not_lt_zero dd.length h0).elim
  | k + 1, hvk, hk => varAbove dd g a k bt (Nat.le_of_lt_succ hk) hvk

/-- `varMid` reads the index at the depth, which names the removed context entry.
It states the type equality of docs/metatheory.md lines 193 to 198.
-/
theorem varMid : ∀ (dd g : List Ty) (a bt : Ty),
    «variable» dd.length (dd ++ a :: g) = Except.ok bt → a = bt
  | [], g, a, bt, hv => Weakening.headEq a bt g hv
  | x :: dd', g, a, bt, hv =>
      varMid dd' g a bt (Weakening.variableStepBack x (dd' ++ a :: g) dd'.length bt hv)

/-- `varSub` states row Theorem3 on one variable node. The three arms are the three rows of the table of docs/metatheory.md lines 181 to 185.
The arm at the depth reuses `Weakening.weakeningPure` with the empty prefix, which is the step that docs/metatheory.md lines 193 to 198 asks for.
-/
theorem varSub (dd g : List Ty) (a : Ty) (index : Nat) (bt : Ty) (r : Term)
    (hv : «variable» index (dd ++ a :: g) = Except.ok bt) (hr : HasType g r a) :
    HasType (dd ++ g) (subPure dd.length r (Term.var index)) bt :=
  match Nat.decLt index dd.length with
  | .isTrue hlt =>
      Eq.mp
        (congrArg (fun (z : Term) => HasType (dd ++ g) z bt)
          ((subPureVar dd.length r index).trans (if_pos hlt)).symm)
        (.var (dd ++ g) index bt (varBelow dd g a index bt hv hlt))
  | .isFalse hnlt =>
      match Nat.decLt dd.length index with
      | .isTrue hgt =>
          Eq.mp
            (congrArg (fun (z : Term) => HasType (dd ++ g) z bt)
              ((subPureVar dd.length r index).trans
                ((if_neg hnlt).trans (if_pos hgt))).symm)
            (.var (dd ++ g) (index - 1) bt (varAboveIndex dd g a index bt hgt hv))
      | .isFalse hngt =>
          Eq.mp
            (congrArg (fun (z : Term) => HasType (dd ++ g) z bt)
              ((subPureVar dd.length r index).trans
                ((if_neg hnlt).trans (if_neg hngt))).symm)
            (Eq.mp
              (congrArg
                (fun (z : Ty) => HasType (dd ++ g) (Weakening.shiftPure 0 dd.length r) z)
                (varMid dd g a bt
                  (Eq.mp
                    (congrArg
                      (fun (i : Nat) => «variable» i (dd ++ a :: g) = Except.ok bt)
                      (natEqOfNotLt index dd.length hnlt hngt))
                    hv)))
              (Weakening.weakeningPure g r a hr [] g rfl dd))

mutual
/-- `substitutionPure` states row Theorem3 of the stage brief on the replacement alone.
It walks the derivation of `HasType`, generalized over the depth and over the prefix `dd`, as docs/metatheory.md lines 187 to 192 asks.
Each rule of that relation mirrors one arm of `check_term` at lib/finite_term.ml lines 62 to 105.
The `case` step raises the depth one unit inside each branch, per docs/metatheory.md lines 204 to 208, and the scrutinee keeps the depth.
-/
theorem substitutionPure : ∀ (ctx : List Ty) (t : Term) (bt : Ty), HasType ctx t bt →
    ∀ (dd g : List Ty) (a : Ty) (r : Term), HasType g r a → ctx = dd ++ a :: g →
      HasType (dd ++ g) (subPure dd.length r t) bt
  | _, _, _, .var _ctx index bt hvv, dd, g, a, r, hr, heq =>
      varSub dd g a index bt r
        (Eq.mp
          (congrArg (fun (z : List Ty) => «variable» index z = Except.ok bt) heq) hvv)
        hr
  | _, _, _, .atom _ctx name labels hm, dd, g, _a, _r, _hr, (_heq) =>
      .atom (dd ++ g) name labels hm
  | _, _, _, .tag ctx label payload fibers fiber hlookup hpayload, dd, g, a, r, hr, heq =>
      .tag (dd ++ g) label (subPure dd.length r payload) fibers fiber hlookup
        (substitutionPure ctx payload fiber hpayload dd g a r hr heq)
  | _, _, _, .«section» ctx entries fibers sorted pairs hcanon halign hentries,
      dd, g, a, r, hr, heq =>
      .«section» (dd ++ g) (subPureEntries dd.length r entries) fibers
        (subPureEntries dd.length r sorted) (subTriples dd.length r pairs)
        ((canonicalSub dd.length r entries).trans
          (congrArg
            (fun (z : Res (List (String × Term))) => z.map (subPureEntries dd.length r))
            hcanon))
        ((alignSub dd.length r fibers sorted).trans
          (congrArg
            (fun (z : Res (List (String × Ty × Term))) => z.map (subTriples dd.length r))
            halign))
        (substitutionPureEntries ctx pairs .none hentries dd g a r hr heq)
  | _, _, _,
      .«case» ctx scrutinee fibers branches sorted pairs expected hcanon halign hscrut hbranches,
      dd, g, a, r, hr, heq =>
      .«case» (dd ++ g) (subPure dd.length r scrutinee) fibers
        (subPureEntries (dd.length + 1) r branches)
        (subPureEntries (dd.length + 1) r sorted)
        (subTriples (dd.length + 1) r pairs) expected
        ((canonicalSub (dd.length + 1) r branches).trans
          (congrArg
            (fun (z : Res (List (String × Term))) => z.map (subPureEntries (dd.length + 1) r))
            hcanon))
        ((alignSub (dd.length + 1) r fibers sorted).trans
          (congrArg
            (fun (z : Res (List (String × Ty × Term))) => z.map (subTriples (dd.length + 1) r))
            halign))
        (substitutionPure ctx scrutinee (.lan fibers) hscrut dd g a r hr heq)
        (substitutionPureEntries ctx pairs (.some expected) hbranches dd g a r hr heq)
  | _, _, _, .project ctx sectionTerm fibers label bt hlookup hsection, dd, g, a, r, hr, heq =>
      .project (dd ++ g) (subPure dd.length r sectionTerm) fibers label bt hlookup
        (substitutionPure ctx sectionTerm (.ran fibers) hsection dd g a r hr heq)

/-- `substitutionPureEntries` is the entry list companion of `substitutionPure`.
The mode of `HasTypeEntries` fixes the depth, which `Weakening.cutoffFor` reads.
The field mode keeps the depth of the term, and the branch mode raises it one unit, which is the extended context of lib/finite_term.ml lines 92 and 93.
-/
theorem substitutionPureEntries : ∀ (ctx : List Ty) (pairs : List (String × Ty × Term))
    (mode : Option Ty), HasTypeEntries ctx pairs mode →
    ∀ (dd g : List Ty) (a : Ty) (r : Term), HasType g r a → ctx = dd ++ a :: g →
      HasTypeEntries (dd ++ g) (subTriples (Weakening.cutoffFor mode dd.length) r pairs) mode
  | _, _, _, .nil _ctx mode, dd, g, _a, _r, _hr, (_heq) => .nil (dd ++ g) mode
  | _, _, _, .field ctx label fiber fieldTerm rest hfield hrest, dd, g, a, r, hr, heq =>
      .field (dd ++ g) label fiber (subPure dd.length r fieldTerm)
        (subTriples dd.length r rest)
        (substitutionPure ctx fieldTerm fiber hfield dd g a r hr heq)
        (substitutionPureEntries ctx rest .none hrest dd g a r hr heq)
  | _, _, _, .branch ctx label payloadType body rest expected hbody hrest, dd, g, a, r, hr, heq =>
      .branch (dd ++ g) label payloadType (subPure (dd.length + 1) r body)
        (subTriples (dd.length + 1) r rest) expected
        (substitutionPure (payloadType :: ctx) body expected hbody (payloadType :: dd) g a r hr
          (congrArg (fun (z : List Ty) => payloadType :: z) heq))
        (substitutionPureEntries ctx rest (.some expected) hrest dd g a r hr heq)
end

end Substitution

/-- Row Theorem3 of the stage brief, the substitution lemma at an arbitrary depth.
It states docs/metatheory.md lines 187 to 208: if `r` checks at `a` in `g`, and `b` checks at
`bt` in `dd ++ a :: g`, and the prefix `dd` has length `d`, then every term that
`sub d r` returns for `b` checks at `bt` in `dd ++ g`.
The hypothesis reads a run of `sub`, as row Theorem2 does for `shift`, since `sub` of
Subst.lean threads fuel and returns a pair. `Substitution.subOkPure` shows that the returned term is
`Substitution.subPure d r b`, so the run hypothesis and the pure statement agree.
-/
theorem substitution_at_depth (dd g : List Ty) (a bt : Ty) (d fuel remaining : Nat)
    (r b b' : Term) (replacement : HasType g r a) (body : HasType (dd ++ a :: g) b bt)
    (hd : dd.length = d) (substituted : sub d r fuel b = Except.ok (b', remaining)) :
    HasType (dd ++ g) b' bt :=
  Eq.mp
    (congrArg (fun (z : Term) => HasType (dd ++ g) z bt)
      ((Substitution.subOkPure d r b fuel remaining b' substituted).trans
        (congrArg (fun (n : Nat) => Substitution.subPure n r b) hd).symm).symm)
    (Substitution.substitutionPure (dd ++ a :: g) b bt body dd g a r replacement rfl)

/-- Row Theorem3-Cor of the stage brief, the property that `substitute` claims.
It states the corollary of docs/metatheory.md lines 209 to 212 at depth zero, with the fuel cost that the same lines state:
`sub` at depth zero spends `size b + occurrences 0 b * size r`.
The first component is row Theorem3 at the empty prefix, and the second component is `sub_cost` of
Budget.lean.
-/
theorem substitution_zero (g : List Ty) (a bt : Ty) (fuel remaining : Nat) (r b b' : Term)
    (replacement : HasType g r a) (body : HasType (a :: g) b bt)
    (substituted : sub 0 r fuel b = Except.ok (b', remaining)) :
    HasType g b' bt ∧ remaining + (size b + occurrences 0 b * size r) = fuel :=
  ⟨substitution_at_depth [] g a bt 0 fuel remaining r b b' replacement body rfl substituted,
    sub_cost b 0 r fuel b' remaining substituted⟩

namespace Substitution

/-- `entriesSize` reads the node count of one aligned entry list from the source entry list.
The section rule and the case rule of
Typing.lean sort the entries, then they align them against the fiber list, and neither step changes the node count, as
`canonical_sorted`, `align_size` and `sort_size` of Budget.lean state.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem entriesSize (entries sorted : List (String × Term)) (fibers : List (String × Ty))
    (pairs : List (String × Ty × Term)) (hcanon : canonicalEntries entries = .ok sorted)
    (halign : align fibers sorted = .ok pairs) : sizePairs pairs = sizeEntries entries :=
  (align_size fibers sorted pairs halign).trans
    ((congrArg sizeEntries (canonical_sorted entries sorted hcanon)).trans (sort_size entries))

/-- `fieldsAt` rewrites the budget of one `checkFields` run along an equal node count.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem fieldsAt (gas : Nat) (ctx : List Ty) (pairs : List (String × Ty × Term)) (n j : Nat)
    (h : checkFields gas (sizePairs pairs + j) ctx pairs = Except.ok j)
    (hn : sizePairs pairs = n) : checkFields gas (n + j) ctx pairs = Except.ok j :=
  Eq.mp (congrArg (fun (z : Nat) => checkFields gas (z + j) ctx pairs = Except.ok j) hn) h

/-- `branchesAt` rewrites the budget of one `checkBranches` run along an equal node count.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem branchesAt (gas : Nat) (ctx : List Ty) (pairs : List (String × Ty × Term)) (a : Ty)
    (n j : Nat) (h : checkBranches gas (sizePairs pairs + j) ctx pairs a = Except.ok j)
    (hn : sizePairs pairs = n) : checkBranches gas (n + j) ctx pairs a = Except.ok j :=
  Eq.mp (congrArg (fun (z : Nat) => checkBranches gas (z + j) ctx pairs a = Except.ok j) hn) h

mutual
/-- `checkFuelSet` sets the budget of one successful `checkCore` run to the exact node count.
`check_core_cost` of Budget.lean states that a successful run spends
`size t`, and this statement is the constructive partner of that count: a run at
`size t + j` succeeds and leaves `j`.
Row Theorem3-C2 needs the exact remainder, since the fuel of the second check of
`substitute` is the remainder of the first check.
The gas parameter of decision S2-D5 stays fixed, since gas is no budget.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem checkFuelSet : ∀ (gas : Nat) (t : Term) (f j : Nat) (ctx : List Ty) (a : Ty) (out : Nat),
    checkCore gas f ctx t a = .ok out → checkCore gas (size t + j) ctx t a = .ok j
  | 0, _t, _f, _j, _ctx, _a, _out, h => (res_error_ne_ok h).elim
  | gasPred + 1, t, f, j, ctx, a, out, h =>
      match res_bind_ok h with
      | ⟨g, _ht, h2⟩ =>
          match t, h2 with
          | .var _index, hh =>
              res_bind_mk (a := j) (tickOne j)
                (match res_bind_ok hh with
                  | ⟨actual, hv, h3⟩ =>
                      res_bind_mk (a := actual) hv
                        (ite_case (P := fun (u w : Res Nat) => u = .ok out → w = .ok j)
                          (fun _hc (_h4 : _) => rfl)
                          (fun _hc h4 => (res_error_ne_ok h4).elim) h3))
          | .atom _name, hh =>
              res_bind_mk (a := j) (tickOne j)
                (match a, hh with
                  | .atoms .., h3 =>
                      ite_case (P := fun (u w : Res Nat) => u = .ok out → w = .ok j)
                        (fun _hc (_h4 : _) => rfl)
                        (fun _hc h4 => (res_error_ne_ok h4).elim) h3
                  | .lan .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim)
          | .tag _label payload, hh =>
              res_bind_mk (a := size payload + j) (tickShape (size payload) j)
                (match a, hh with
                  | .lan .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨fiber, hf, h4⟩ =>
                          res_bind_mk (a := fiber) hf
                            (checkFuelSet gasPred payload g j ctx fiber out h4)
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim)
          | .«section» entries, hh =>
              res_bind_mk (a := sizeEntries entries + j) (tickShape (sizeEntries entries) j)
                (match a, hh with
                  | .ran fibers, h3 =>
                      match res_bind_ok h3 with
                      | ⟨sorted, hs, h4⟩ =>
                          res_bind_mk (a := sorted) hs
                            (match res_bind_ok h4 with
                              | ⟨pairs, hp, h5⟩ =>
                                  res_bind_mk (a := pairs) hp
                                    (fieldsAt gasPred ctx pairs (sizeEntries entries) j
                                      (checkFieldsFuelSet gasPred pairs g j ctx out h5)
                                      (entriesSize entries sorted fibers pairs hs hp)))
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .lan .., h3 => (res_error_ne_ok h3).elim)
          | .«case» scrutinee st branches, hh =>
              res_bind_mk (a := size scrutinee + sizeEntries branches + j)
                (tickTwo (size scrutinee) (sizeEntries branches) j)
                (match st, hh with
                  | .lan fibers, h3 =>
                      match res_bind_ok h3 with
                      | ⟨sorted, hs, h4⟩ =>
                          res_bind_mk (a := sorted) hs
                            (match res_bind_ok h4 with
                              | ⟨pairs, hp, h5⟩ =>
                                  res_bind_mk (a := pairs) hp
                                    (match res_bind_ok h5 with
                                      | ⟨f2, hf2, h6⟩ =>
                                          res_bind_mk (a := sizeEntries branches + j)
                                            ((congrArg
                                                (fun (z : Nat) =>
                                                  checkCore gasPred z ctx scrutinee (Ty.lan fibers))
                                                (Nat.add_assoc (size scrutinee)
                                                  (sizeEntries branches) j)).trans
                                              (checkFuelSet gasPred scrutinee g
                                                (sizeEntries branches + j) ctx (Ty.lan fibers) f2
                                                hf2))
                                            (branchesAt gasPred ctx pairs a (sizeEntries branches) j
                                              (checkBranchesFuelSet gasPred pairs f2 j ctx a out h6)
                                              (entriesSize branches sorted fibers pairs hs hp))))
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim)
          | .project field st _label, hh =>
              res_bind_mk (a := size field + j) (tickShape (size field) j)
                (match st, hh with
                  | .ran fibers, h3 =>
                      match res_bind_ok h3 with
                      | ⟨actual, hl, h4⟩ =>
                          res_bind_mk (a := actual) hl
                            (ite_case (P := fun (u w : Res Nat) => u = .ok out → w = .ok j)
                              (fun _hc h5 =>
                                checkFuelSet gasPred field g j ctx (Ty.ran fibers) out h5)
                              (fun _hc h5 => (res_error_ne_ok h5).elim) h4)
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .lan .., h3 => (res_error_ne_ok h3).elim)

/-- `checkFieldsFuelSet` is the field list partner of `checkFuelSet`.
`checkFields` of
Check.lean holds no charge point of its own, so the node count of the aligned list is the whole cost, as
`check_fields_cost` of Budget.lean states.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem checkFieldsFuelSet : ∀ (gas : Nat) (pairs : List (String × Ty × Term)) (f j : Nat)
    (ctx : List Ty) (out : Nat), checkFields gas f ctx pairs = .ok out →
    checkFields gas (sizePairs pairs + j) ctx pairs = .ok j
  | 0, _pairs, _f, _j, _ctx, _out, h => (res_error_ne_ok h).elim
  | gasPred + 1, pairs, f, j, ctx, out, h =>
      match pairs, h with
      | [], hh =>
          (fun (_hnil : _) =>
            congrArg (fun (z : Nat) => (Except.ok z : Res Nat)) (Nat.zero_add j)) hh
      | (_label, fiber, field) :: rest, hh =>
          match res_bind_ok hh with
          | ⟨f2, hf2, h3⟩ =>
              res_bind_mk (a := sizePairs rest + j)
                ((congrArg (fun (z : Nat) => checkCore gasPred z ctx field fiber)
                    (Nat.add_assoc (size field) (sizePairs rest) j)).trans
                  (checkFuelSet gasPred field f (sizePairs rest + j) ctx fiber f2 hf2))
                (checkFieldsFuelSet gasPred rest f2 j ctx out h3)

/-- `checkBranchesFuelSet` is the branch list partner of `checkFuelSet`.
Each body runs at the context that the payload type extends, as lib/finite_term.ml lines 92 and 93 do, and the node count of the aligned list is the whole cost.
-/
theorem checkBranchesFuelSet : ∀ (gas : Nat) (pairs : List (String × Ty × Term)) (f j : Nat)
    (ctx : List Ty) (a : Ty) (out : Nat), checkBranches gas f ctx pairs a = .ok out →
    checkBranches gas (sizePairs pairs + j) ctx pairs a = .ok j
  | 0, _pairs, _f, _j, _ctx, _a, _out, h => (res_error_ne_ok h).elim
  | gasPred + 1, pairs, f, j, ctx, a, out, h =>
      match pairs, h with
      | [], hh =>
          (fun (_hnil : _) =>
            congrArg (fun (z : Nat) => (Except.ok z : Res Nat)) (Nat.zero_add j)) hh
      | (_label, payloadType, body) :: rest, hh =>
          match res_bind_ok hh with
          | ⟨f2, hf2, h3⟩ =>
              res_bind_mk (a := sizePairs rest + j)
                ((congrArg (fun (z : Nat) => checkCore gasPred z (payloadType :: ctx) body a)
                    (Nat.add_assoc (size body) (sizePairs rest) j)).trans
                  (checkFuelSet gasPred body f (sizePairs rest + j) (payloadType :: ctx) a f2 hf2))
                (checkBranchesFuelSet gasPred rest f2 j ctx a out h3)
end

end Substitution

namespace Substitution

/-- `gasBound` raises one budget comparison to the gas expression of decision S2-D5.
`check` and `substitute` of Check.lean and Subst.lean pass
`2 * fuel + 2` gas, so a budget that one rest describes gives the gas order that
`check_gas_irrelevant` of Budget.lean reads.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem gasBound (x y p : Nat) (h : x + p = y) : 2 * x + 2 ≤ 2 * y + 2 :=
  Nat.le.intro (k := 2 * p)
    ((Nat.add_right_comm (2 * x) 2 (2 * p)).trans
      (congrArg (fun (z : Nat) => z + 2)
        ((Nat.left_distrib 2 x p).symm.trans (congrArg (fun (z : Nat) => 2 * z) h))))

end Substitution

/-- Row Theorem3-C2 of the stage brief, the budget that `substitute` needs.
It states claim C2 of docs/metatheory.md lines 213 to 216: `2 * size b + (n + 1) * size r`, for `n` the occurrence count of index zero in
`b`, always suffices. Every run of `substitute` that succeeds at some budget succeeds at that budget and returns the same term.
The three steps of `substitute` are the check of the replacement, the check of the body and the replacement itself, and the budget covers
`size r` for the first check, `size b` for the second check and `size b + n * size r` for the replacement, which is the count of docs/metatheory.md lines 211 and 212.
-/
theorem substitute_budget_sufficient (fuel : Nat) (ctx : List Ty) (r : Term) (rt : Ty) (b : Term)
    (bt : Ty) (result : Term) (ran : substitute fuel ctx r rt b bt = Except.ok result) :
    substitute (2 * size b + (occurrences 0 b + 1) * size r) ctx r rt b bt = Except.ok result :=
  match res_bind_ok ran with
  | ⟨f1, h1, hr1⟩ =>
      match res_bind_ok hr1 with
      | ⟨f2, h2, hr2⟩ =>
          match res_bind_ok hr2 with
          | ⟨pair, h3, hr3⟩ =>
              let c1 : f1 + size r = fuel :=
                check_core_cost (2 * fuel + 2) r fuel ctx rt f1 h1
              let c2 : f2 + size b = f1 :=
                check_core_cost (2 * f1 + 2) b f1 (rt :: ctx) bt f2 h2
              let c3 : pair.2 + (size b + occurrences 0 b * size r) = f2 :=
                sub_cost b 0 r f2 pair.1 pair.2 h3
              let hsum : 2 * size b + (occurrences 0 b + 1) * size r + pair.2 = fuel :=
                (Substitution.fuelSplit (size b) (size r) (occurrences 0 b) pair.2).trans
                  ((congrArg (fun (z : Nat) => z + size b + size r) c3).trans
                    ((congrArg (fun (z : Nat) => z + size r) c2).trans c1))
              let hsum1 : 2 * size b + occurrences 0 b * size r + pair.2 = f1 :=
                (Substitution.natSplitTwo (size b) (occurrences 0 b * size r) pair.2).trans
                  ((congrArg (fun (z : Nat) => z + size b) c3).trans c2)
              let hA1 : checkCore (2 * fuel + 2) (2 * size b + (occurrences 0 b + 1) * size r)
                  ctx r rt = Except.ok (2 * size b + occurrences 0 b * size r) :=
                Eq.mp
                  (congrArg
                    (fun (z : Nat) => checkCore (2 * fuel + 2) z ctx r rt
                      = Except.ok (2 * size b + occurrences 0 b * size r))
                    (Substitution.fuelHead (size b) (size r) (occurrences 0 b)).symm)
                  (Substitution.checkFuelSet (2 * fuel + 2) r fuel
                    (2 * size b + occurrences 0 b * size r) ctx rt f1 h1)
              let hA : checkCore (2 * (2 * size b + (occurrences 0 b + 1) * size r) + 2)
                  (2 * size b + (occurrences 0 b + 1) * size r) ctx r rt
                  = Except.ok (2 * size b + occurrences 0 b * size r) :=
                (check_gas_irrelevant (2 * fuel + 2)
                  (2 * (2 * size b + (occurrences 0 b + 1) * size r) + 2)
                  (2 * size b + (occurrences 0 b + 1) * size r) ctx r rt
                  (Substitution.gasBound (2 * size b + (occurrences 0 b + 1) * size r) fuel pair.2
                    hsum)
                  (Nat.le_refl (2 * (2 * size b + (occurrences 0 b + 1) * size r) + 2))).symm.trans
                  hA1
              let hB1 : checkCore (2 * f1 + 2) (2 * size b + occurrences 0 b * size r)
                  (rt :: ctx) b bt = Except.ok (size b + occurrences 0 b * size r) :=
                Eq.mp
                  (congrArg
                    (fun (z : Nat) => checkCore (2 * f1 + 2) z (rt :: ctx) b bt
                      = Except.ok (size b + occurrences 0 b * size r))
                    (Substitution.fuelBody (size b) (occurrences 0 b * size r)).symm)
                  (Substitution.checkFuelSet (2 * f1 + 2) b f1
                    (size b + occurrences 0 b * size r) (rt :: ctx) bt f2 h2)
              let hB : checkCore (2 * (2 * size b + occurrences 0 b * size r) + 2)
                  (2 * size b + occurrences 0 b * size r) (rt :: ctx) b bt
                  = Except.ok (size b + occurrences 0 b * size r) :=
                (check_gas_irrelevant (2 * f1 + 2)
                  (2 * (2 * size b + occurrences 0 b * size r) + 2)
                  (2 * size b + occurrences 0 b * size r) (rt :: ctx) b bt
                  (Substitution.gasBound (2 * size b + occurrences 0 b * size r) f1 pair.2 hsum1)
                  (Nat.le_refl (2 * (2 * size b + occurrences 0 b * size r) + 2))).symm.trans hB1
              let hC : sub 0 r (size b + occurrences 0 b * size r) b
                  = Except.ok (Substitution.subPure 0 r b, 0) :=
                Eq.mp
                  (congrArg
                    (fun (z : Nat) => sub 0 r z b = Except.ok (Substitution.subPure 0 r b, 0))
                    (Nat.add_zero (size b + occurrences 0 b * size r)))
                  (Substitution.subRun b 0 r 0)
              let hfinal : (Except.ok (Substitution.subPure 0 r b) : Res Term) = Except.ok result :=
                (congrArg (fun (z : Term) => (Except.ok z : Res Term))
                  (Substitution.subOkPure 0 r b f2 pair.2 pair.1 h3).symm).trans hr3
              res_bind_mk (a := 2 * size b + occurrences 0 b * size r) hA
                (res_bind_mk (a := size b + occurrences 0 b * size r) hB
                  (res_bind_mk (a := (Substitution.subPure 0 r b, 0)) hC hfinal))
