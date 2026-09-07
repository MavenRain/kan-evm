import KanEvmProofs.Budget
import KanEvmProofs.Weakening
import KanEvmProofs.Substitution

/-! # Evaluation under shifting and under substitution

This module holds row Lemma3, row Theorem5 and row Theorem5-C5 of the stage brief.
`shift_preserves_value` states docs/metatheory.md lines 252 to 265.
`evaluate_sub_env` states docs/metatheory.md lines 267 to 287.
`evaluate_sub_budget_gap` states claim C5 of docs/metatheory.md lines 288 to 290.
`shift` and `sub` of Subst.lean mirror `map_variables` and `substitute_core` at lib/finite_term.ml lines 112 to 151, and
`evaluate` of Eval.lean mirrors `evaluate` at lib/finite_term.ml lines 236 to 266.
Both rows claim preservation of a successful evaluation only, per docs/metatheory.md lines 271 to 274, and both fuels stay existential, per docs/metatheory.md lines 254 and 268.
Every proof runs in term mode, so the file opens no tactic block.
-/

namespace EvalSubst

/-- `iteSplit` proves a property of an `if` term from one proof per side.
The index map of `map_variables` at lib/finite_term.ml line 148 and the depth test of
`substitute_core` at lib/finite_term.ml lines 141 to 142 both reach the reader as an
`if`, so the index cases of docs/metatheory.md lines 258 to 259 and 278 to 282 need this split.
-/
theorem iteSplit {α : Type} {p : Prop} [inst : Decidable p] {x y : α} {P : α → Prop}
    (ht : p → P x) (hf : ¬ p → P y) : P (if p then x else y) :=
  match inst with
  | isTrue hp => ht hp
  | isFalse hp => hf hp

/-- `lengthAppend` adds the two lengths of an appended environment.
The environment `E @ D @ rho` of docs/metatheory.md line 255 needs this count, and the environment itself mirrors the list that
`evaluate` extends at lib/finite_term.ml line 253.
-/
theorem lengthAppend : ∀ (front back : List Value),
    (front ++ back).length = front.length + back.length
  | [], back => (Nat.zero_add back.length).symm
  | _x :: front, back =>
      (congrArg (fun (z : Nat) => z + 1) (lengthAppend front back)).trans
        (nat_one_shift front.length back.length).symm

/-- `getAppendLeft` reads an index below the front length from the front list.
This is the case `i < c` of docs/metatheory.md line 258, and the read mirrors
`variable` at lib/finite_term.ml lines 43 to 46.
-/
theorem getAppendLeft : ∀ (front back : List Value) (i : Nat), i < front.length →
    (front ++ back)[i]? = front[i]?
  | [], _back, i, hlt => (Nat.not_lt_zero i hlt).elim
  | _x :: _front, _back, 0, _hlt => rfl
  | _x :: front, back, i + 1, hlt => getAppendLeft front back i (Nat.lt_of_succ_lt_succ hlt)

/-- `getAppendRight` reads an index at or above the front length from the back list.
This is the case `i >= c` of docs/metatheory.md lines 259 to 260, and the read mirrors
`variable` at lib/finite_term.ml lines 43 to 46. -/
theorem getAppendRight : ∀ (front back : List Value) (i : Nat), front.length ≤ i →
    (front ++ back)[i]? = back[i - front.length]?
  | [], _back, _i, _hle => rfl
  | _x :: front, _back, 0, hle => (Nat.not_succ_le_zero front.length hle).elim
  | _x :: front, back, i + 1, hle =>
      (getAppendRight front back i (Nat.le_of_succ_le_succ hle)).trans
        (congrArg (fun (z : Nat) => back[z]?) (Nat.succ_sub_succ i front.length).symm)

/-- `natGapCancel` cancels the inserted width from a shifted index.
The equation `(E @ D @ rho)(i + d) = (E @ rho)(i)` of docs/metatheory.md lines 259 to 260 reduces to this arithmetic, and the shift itself is lib/finite_term.ml line 148.
-/
theorem natGapCancel (i a b : Nat) : i + b - (a + b) = i - a := Nat.add_sub_add_right i b a

/-- `lengthLe` bounds the front length through the appended length.
The bound serves the index cases of docs/metatheory.md lines 258 to 260 for the environment that
`evaluate` reads at lib/finite_term.ml line 240.
-/
theorem lengthLe (front back : List Value) : front.length ≤ (front ++ back).length :=
  Nat.le_trans (Nat.le_add_right front.length back.length)
    (Nat.le_of_eq (lengthAppend front back).symm)

/-- `shiftIndex` states that the shifted index reads the same entry.
This is the variable case of docs/metatheory.md lines 258 to 260 for the index map of
`map_variables` at lib/finite_term.ml line 148. -/
theorem shiftIndex (e dd rho : List Value) (i : Nat) :
    ((e ++ dd) ++ rho)[if i < e.length then i else i + dd.length]? = (e ++ rho)[i]? :=
  iteSplit (P := fun (idx : Nat) => ((e ++ dd) ++ rho)[idx]? = (e ++ rho)[i]?)
    (fun (hlt : i < e.length) =>
      ((getAppendLeft (e ++ dd) rho i (Nat.lt_of_lt_of_le hlt (lengthLe e dd))).trans
          (getAppendLeft e dd i hlt)).trans
        (getAppendLeft e rho i hlt).symm)
    (fun (hge : ¬ i < e.length) =>
      ((getAppendRight (e ++ dd) rho (i + dd.length)
              (Nat.le_trans (Nat.le_of_eq (lengthAppend e dd))
                (Nat.add_le_add_right (Nat.le_of_not_lt hge) dd.length))).trans
          (congrArg (fun (z : Nat) => rho[z]?)
            ((congrArg (fun (z : Nat) => i + dd.length - z) (lengthAppend e dd)).trans
              (natGapCancel i e.length dd.length)))).trans
        (getAppendRight e rho i (Nat.le_of_not_lt hge)).symm)

/-- `varStep` carries a successful variable read to a second index name.
The read of `evaluate` at lib/finite_term.ml line 239 reports the index inside the error of `variable` at lib/finite_term.ml lines 43 to 46, and docs/metatheory.md lines 258 to 260 keeps the value only.
-/
theorem varStep : ∀ (o : Option Value) (i j g : Nat) (u : Value) (rest : Nat),
    o.elim (Except.error (Err.invalidVariable i))
        (fun (w : Value) => (Except.ok (w, g) : Res (Value × Nat))) = .ok (u, rest) →
      o.elim (Except.error (Err.invalidVariable j))
        (fun (w : Value) => (Except.ok (w, g) : Res (Value × Nat))) = .ok (u, rest)
  | none, _i, _j, _g, _u, _rest, h => (res_error_ne_ok h).elim
  | some _w, _i, _j, _g, _u, _rest, h => h

/-- `caseTransfer` moves a successful branch selection to a second environment.
The scrutinee agrees on both sides of docs/metatheory.md lines 260 to 262, so the same label selects on both sides, and the selection mirrors lib/finite_term.ml lines 248 to 254.
-/
theorem caseTransfer : ∀ (w : Value) (fuelL fuelR : Nat) (rhoL rhoR : List Value)
    (bsL bsR : List (String × Term)) (u : Value) (restL restR : Nat),
    (∀ (l : String) (p : Value),
        evaluateBranch fuelL rhoL l p bsL = .ok (u, restL) →
          evaluateBranch fuelR rhoR l p bsR = .ok (u, restR)) →
    (match w with
      | .tag l p => evaluateBranch fuelL rhoL l p bsL
      | .atom .. => (Except.error Err.expectedLan : Res (Value × Nat))
      | .«section» .. => (Except.error Err.expectedLan : Res (Value × Nat))) = .ok (u, restL) →
    (match w with
      | .tag l p => evaluateBranch fuelR rhoR l p bsR
      | .atom .. => (Except.error Err.expectedLan : Res (Value × Nat))
      | .«section» .. => (Except.error Err.expectedLan : Res (Value × Nat))) = .ok (u, restR)
  | .atom _n, _fL, _fR, _rL, _rR, _bL, _bR, _u, _sL, _sR, _k, h => (res_error_ne_ok h).elim
  | .«section» _fs, _fL, _fR, _rL, _rR, _bL, _bR, _u, _sL, _sR, _k, h => (res_error_ne_ok h).elim
  | .tag l p, _fL, _fR, _rL, _rR, _bL, _bR, _u, _sL, _sR, k, h => k l p h

/-- `projectTransfer` moves a successful field read to a second remaining budget.
The field read of lib/finite_term.ml lines 255 to 260 holds no environment, so only the budget changes, and the value stands per docs/metatheory.md lines 264 to 265.
-/
theorem projectTransfer : ∀ (w : Value) (label : String) (restL restR : Nat) (u : Value)
    (rest : Nat),
    (match w with
      | .«section» entries =>
          lookup label entries >>= fun (value : Value) =>
            (Except.ok (value, restL) : Res (Value × Nat))
      | .atom .. => (Except.error Err.expectedRan : Res (Value × Nat))
      | .tag .. => (Except.error Err.expectedRan : Res (Value × Nat))) = .ok (u, rest) →
    (match w with
      | .«section» entries =>
          lookup label entries >>= fun (value : Value) =>
            (Except.ok (value, restR) : Res (Value × Nat))
      | .atom .. => (Except.error Err.expectedRan : Res (Value × Nat))
      | .tag .. => (Except.error Err.expectedRan : Res (Value × Nat))) = .ok (u, restR)
  | .atom _n, _label, _restL, _restR, _u, _rest, h => (res_error_ne_ok h).elim
  | .tag _l _p, _label, _restL, _restR, _u, _rest, h => (res_error_ne_ok h).elim
  | .«section» _entries, _label, _restL, restR, _u, _rest, h =>
      match res_bind_ok h with
      | ⟨w2, hl, h4⟩ =>
          res_bind_mk (a := w2) hl
            (congrArg (fun (z : Value) => (Except.ok (z, restR) : Res (Value × Nat)))
              (congrArg Prod.fst (Except.ok.inj h4)))

mutual

/-- `evalShift` states the generalized Lemma 3 of docs/metatheory.md lines 253 to 265 for the pure shift form of
Weakening.lean. The recursion is structural on the term, and it mirrors `map_variables` at lib/finite_term.ml lines 112 to 129 against
`evaluate` at lib/finite_term.ml lines 236 to 260. A shift adds no node, so the same fuel serves and the remaining budget stays equal.
-/
theorem evalShift : ∀ (t : Term) (f : Nat) (e dd rho : List Value) (u : Value) (rest : Nat),
    evaluate f (e ++ rho) t = .ok (u, rest) →
      evaluate f ((e ++ dd) ++ rho) (Weakening.shiftPure e.length dd.length t) = .ok (u, rest)
  | .var index, _f, e, dd, rho, u, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          res_bind_mk (a := g) ht
            ((congrArg
                (fun (o : Option Value) =>
                  o.elim
                    (Except.error
                      (Err.invalidVariable
                        (if index < e.length then index else index + dd.length)))
                    (fun (w : Value) => (Except.ok (w, g) : Res (Value × Nat))))
                (shiftIndex e dd rho index)).trans
              (varStep ((e ++ rho)[index]?) index
                (if index < e.length then index else index + dd.length) g u rest h2))
  | .atom _name, _f, _e, _dd, _rho, _u, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, hv⟩ => res_bind_mk (a := g) ht hv
  | .tag _label payload, _f, e, dd, rho, _u, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨p, hp, h3⟩ =>
              res_bind_mk (a := g) ht
                (res_bind_mk (a := p) (evalShift payload g e dd rho p.1 p.2 hp) h3)
  | .«section» fields, _f, e, dd, rho, _u, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨sorted, hcan, h3⟩ =>
              match res_bind_ok h3 with
              | ⟨res, hres, h4⟩ =>
                  res_bind_mk (a := g) ht
                    (res_bind_mk (a := Weakening.shiftPureEntries e.length dd.length sorted)
                      ((Weakening.canonicalShift e.length dd.length fields).trans
                        (congrArg
                          (fun (z : Res (List (String × Term))) =>
                            z.map (Weakening.shiftPureEntries e.length dd.length))
                          hcan))
                      (res_bind_mk (a := res)
                        (evalShiftEntries fields g e dd rho res.1 res.2 hres) h4))
  | .«case» scrutinee _scrutineeType branches, _f, e, dd, rho, u, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨res, hres, h3⟩ =>
              res_bind_mk (a := g) ht
                (res_bind_mk (a := res) (evalShift scrutinee g e dd rho res.1 res.2 hres)
                  (caseTransfer res.1 res.2 res.2 (e ++ rho) ((e ++ dd) ++ rho) branches
                    (Weakening.shiftPureEntries (e.length + 1) dd.length branches) u rest rest
                    (fun (l : String) (p : Value) =>
                      evalShiftBranch branches res.2 e dd rho l p u rest)
                    h3))
  | .project field _sectionType _label, _f, e, dd, rho, _u, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨res, hres, h3⟩ =>
              res_bind_mk (a := g) ht
                (res_bind_mk (a := res) (evalShift field g e dd rho res.1 res.2 hres) h3)

/-- `evalShiftEntries` states `evalShift` for a section field list.
It mirrors `map_entries` at lib/finite_term.ml lines 130 to 135 against `evaluate_entries` at lib/finite_term.ml lines 261 to 266, and it serves the section case of docs/metatheory.md lines 264 to 265.
-/
theorem evalShiftEntries : ∀ (es : List (String × Term)) (f : Nat) (e dd rho : List Value)
    (vs : List (String × Value)) (rest : Nat),
    evaluateEntries f (e ++ rho) es = .ok (vs, rest) →
      evaluateEntries f ((e ++ dd) ++ rho) (Weakening.shiftPureEntries e.length dd.length es)
        = .ok (vs, rest)
  | [], _f, _e, _dd, _rho, _vs, _rest, h => h
  | (_label, field) :: more, f, e, dd, rho, _vs, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              res_bind_mk (a := head) (evalShift field f e dd rho head.1 head.2 hhead)
                (res_bind_mk (a := tail)
                  (evalShiftEntries more head.2 e dd rho tail.1 tail.2 htail) h3)

/-- `evalShiftBranch` states `evalShift` for a branch list of a case term.
The selected branch takes the cutoff `c + 1` and the environment `payload :: E` of docs/metatheory.md lines 261 to 264, which matches the depth of lib/finite_term.ml line 125 and the environment of lib/finite_term.ml line 253.
-/
theorem evalShiftBranch : ∀ (bs : List (String × Term)) (f : Nat) (e dd rho : List Value)
    (label : String) (payload u : Value) (rest : Nat),
    evaluateBranch f (e ++ rho) label payload bs = .ok (u, rest) →
      evaluateBranch f ((e ++ dd) ++ rho) label payload
          (Weakening.shiftPureEntries (e.length + 1) dd.length bs) = .ok (u, rest)
  | [], _f, _e, _dd, _rho, _label, _payload, _u, _rest, h => (res_error_ne_ok h).elim
  | (_key, body) :: more, f, e, dd, rho, label, payload, u, rest, h =>
      ite_case (P := fun (x y : Res (Value × Nat)) => x = .ok (u, rest) → y = .ok (u, rest))
        (fun _hc hh => evalShift body f (payload :: e) dd rho u rest hh)
        (fun _hc hh => evalShiftBranch more f e dd rho label payload u rest hh) h

end

/-- `optSome` recovers the read entry from a successful variable step.
The read is lib/finite_term.ml line 239, and the value cases of docs/metatheory.md lines 278 to 282 start from it.
-/
theorem optSome : ∀ (o : Option Value) (i g : Nat) (v : Value) (rest : Nat),
    o.elim (Except.error (Err.invalidVariable i))
        (fun (w : Value) => (Except.ok (w, g) : Res (Value × Nat))) = .ok (v, rest) → o = some v
  | none, _i, _g, _v, _rest, h => (res_error_ne_ok h).elim
  | some _w, _i, _g, _v, _rest, h => congrArg some (congrArg Prod.fst (Except.ok.inj h))

/-- `optOk` builds a successful variable step from the read entry.
It is the converse direction of `optSome` for lib/finite_term.ml line 239, and it closes the substituted side of docs/metatheory.md lines 280 to 282.
-/
theorem optOk (o : Option Value) (i g : Nat) (v : Value) (h : o = some v) :
    o.elim (Except.error (Err.invalidVariable i))
      (fun (w : Value) => (Except.ok (w, g) : Res (Value × Nat))) = .ok (v, g) :=
  congrArg
    (fun (z : Option Value) =>
      z.elim (Except.error (Err.invalidVariable i))
        (fun (w : Value) => (Except.ok (w, g) : Res (Value × Nat))))
    h

/-- `indexBelow` states that an index under the depth reads the same entry on both sides.
This is the case `i < d` of docs/metatheory.md line 280 for the environment read of lib/finite_term.ml lines 43 to 46.
-/
theorem indexBelow (dd rho : List Value) (u v : Value) (index : Nat) (hlt : index < dd.length)
    (hs : (dd ++ u :: rho)[index]? = some v) : (dd ++ rho)[index]? = some v :=
  (getAppendLeft dd rho index hlt).trans
    ((getAppendLeft dd (u :: rho) index hlt).symm.trans hs)

/-- `indexAbove` states that an index over the depth reads the same entry after one decrement.
This is the case `i > d` of docs/metatheory.md lines 280 to 282 for the index decrement of
`substitute_core` at lib/finite_term.ml line 142. -/
theorem indexAbove (dd rho : List Value) (u v : Value) (index : Nat) (hgt : dd.length < index)
    (hs : (dd ++ u :: rho)[index]? = some v) : (dd ++ rho)[index - 1]? = some v :=
  ((getAppendRight dd rho (index - 1) (Nat.sub_le_sub_right hgt 1)).trans
      (congrArg (fun (z : Nat) => rho[z]?) (Nat.sub_right_comm index 1 dd.length))).trans
    ((congrArg (fun (z : Nat) => (u :: rho)[z]?)
          (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hgt)).symm).symm.trans
      ((getAppendRight dd (u :: rho) index (Nat.le_of_lt hgt)).symm.trans hs))

/-- `consZero` reads the head of an extended environment. The extension is lib/finite_term.ml line 253, and the read at the depth is docs/metatheory.md lines 279 to 280.
-/
theorem consZero (u : Value) (rho : List Value) : (u :: rho)[0]? = some u := rfl

/-- `indexAt` states that an index equal to the depth reads the replaced value.
This is the case `i = d` of docs/metatheory.md lines 278 to 280, where `D` holds exactly
`d` entries, for the environment read of lib/finite_term.ml lines 43 to 46.
-/
theorem indexAt (dd rho : List Value) (u v : Value) (index : Nat) (heq : index = dd.length)
    (hs : (dd ++ u :: rho)[index]? = some v) : u = v :=
  Option.some.inj
    ((((getAppendRight dd (u :: rho) dd.length (Nat.le_refl dd.length)).trans
              ((congrArg (fun (z : Nat) => (u :: rho)[z]?) (Nat.sub_self dd.length)).trans
                (consZero u rho))).symm).trans
      ((congrArg (fun (z : Nat) => (dd ++ u :: rho)[z]?) heq).symm.trans hs))

/-- `varSubEval` states Theorem 5 for a variable term. The three index cases are docs/metatheory.md lines 278 to 282, and the three arms of the replacement function are lib/finite_term.ml lines 140 to 149.
The case at the depth reuses `evalShift` at the cutoff zero, which is Lemma 3 of docs/metatheory.md lines 256 to 257.
-/
theorem varSubEval (index f : Nat) (dd rho : List Value) (r : Term) (u v : Value) (rest : Nat)
    (hr : ∃ (f0 rest0 : Nat), evaluate f0 rho r = .ok (u, rest0))
    (h : evaluate f (dd ++ u :: rho) (.var index) = .ok (v, rest)) :
    ∃ (f' rest' : Nat),
      evaluate f' (dd ++ rho)
          (if index < dd.length then Term.var index
            else if dd.length < index then Term.var (index - 1)
              else Weakening.shiftPure 0 dd.length r) = .ok (v, rest') :=
  match res_bind_ok h with
  | ⟨g, _ht, h2⟩ =>
      iteSplit
        (P := fun (z : Term) => ∃ (f' rest' : Nat), evaluate f' (dd ++ rho) z = .ok (v, rest'))
        (fun (hlt : index < dd.length) =>
          ⟨1, 0,
            res_bind_mk (a := 0) (tick_succ 0)
              (optOk ((dd ++ rho)[index]?) index 0 v
                (indexBelow dd rho u v index hlt
                  (optSome ((dd ++ u :: rho)[index]?) index g v rest h2)))⟩)
        (fun (hge : ¬ index < dd.length) =>
          iteSplit
            (P := fun (z : Term) => ∃ (f' rest' : Nat), evaluate f' (dd ++ rho) z = .ok (v, rest'))
            (fun (hgt : dd.length < index) =>
              ⟨1, 0,
                res_bind_mk (a := 0) (tick_succ 0)
                  (optOk ((dd ++ rho)[index - 1]?) (index - 1) 0 v
                    (indexAbove dd rho u v index hgt
                      (optSome ((dd ++ u :: rho)[index]?) index g v rest h2)))⟩)
            (fun (hng : ¬ dd.length < index) =>
              match hr with
              | ⟨f0, rest0, hev⟩ =>
                  ⟨f0, rest0,
                    Eq.mp
                      (congrArg
                        (fun (w : Value) =>
                          evaluate f0 (dd ++ rho) (Weakening.shiftPure 0 dd.length r)
                            = Except.ok (w, rest0))
                        (indexAt dd rho u v index (nat_eq_of_not_lt hge hng)
                          (optSome ((dd ++ u :: rho)[index]?) index g v rest h2)))
                      (evalShift r f0 [] dd rho u rest0 hev)⟩))

/-- `entriesAtSwap` raises the budget of a field list run and keeps the values.
The raise is the sufficiently large budget of docs/metatheory.md lines 268 to 269 for the charge point `tick` at lib/finite_term.ml line 47.
-/
theorem entriesAtSwap (es : List (String × Term)) (f2 r1 r2 : Nat) (rho : List Value)
    (vs : List (String × Value)) (h : evaluateEntries f2 rho es = .ok (vs, r2)) :
    evaluateEntries (r1 + f2) rho es = .ok (vs, r2 + r1) :=
  (congrArg (fun (z : Nat) => evaluateEntries z rho es) (Nat.add_comm r1 f2)).trans
    (evaluate_entries_mono_add es f2 r1 rho vs r2 h)

/-- `branchAtSwap` raises the budget of a branch run and keeps the value.
The raise is the sufficiently large budget of docs/metatheory.md lines 268 to 269 for the charge point `tick` at lib/finite_term.ml line 47.
-/
theorem branchAtSwap (bs : List (String × Term)) (f2 r1 r2 : Nat) (rho : List Value)
    (label : String) (payload w : Value)
    (h : evaluateBranch f2 rho label payload bs = .ok (w, r2)) :
    evaluateBranch (r1 + f2) rho label payload bs = .ok (w, r2 + r1) :=
  (congrArg (fun (z : Nat) => evaluateBranch z rho label payload bs) (Nat.add_comm r1 f2)).trans
    (evaluate_branch_mono_add bs f2 r1 rho label payload w r2 h)

/-- `caseSubTransfer` moves a branch selection to the substituted branch list.
The scrutinee agrees on both sides of docs/metatheory.md lines 284 to 287, and `sub` keeps every branch label and its source order, per
`map_entries` at lib/finite_term.ml lines 130 to 135. The fuel of the substituted side stays existential, per docs/metatheory.md lines 268 to 269.
-/
theorem caseSubTransfer : ∀ (w : Value) (fuelL : Nat) (rhoL rhoR : List Value)
    (bsL bsR : List (String × Term)) (v : Value) (restL : Nat),
    (∀ (l : String) (p : Value),
        evaluateBranch fuelL rhoL l p bsL = .ok (v, restL) →
          ∃ (f' rest' : Nat), evaluateBranch f' rhoR l p bsR = .ok (v, rest')) →
    (match w with
      | .tag l p => evaluateBranch fuelL rhoL l p bsL
      | .atom .. => (Except.error Err.expectedLan : Res (Value × Nat))
      | .«section» .. => (Except.error Err.expectedLan : Res (Value × Nat))) = .ok (v, restL) →
    ∃ (f' rest' : Nat),
      (match w with
        | .tag l p => evaluateBranch f' rhoR l p bsR
        | .atom .. => (Except.error Err.expectedLan : Res (Value × Nat))
        | .«section» .. => (Except.error Err.expectedLan : Res (Value × Nat))) = .ok (v, rest')
  | .atom _n, _fL, _rL, _rR, _bL, _bR, _v, _sL, _k, h => (res_error_ne_ok h).elim
  | .«section» _fs, _fL, _rL, _rR, _bL, _bR, _v, _sL, _k, h => (res_error_ne_ok h).elim
  | .tag l p, _fL, _rL, _rR, _bL, _bR, _v, _sL, k, h => k l p h

/-- `caseMono` raises the budget of a branch selection and keeps the value.
The raise serves the case arm of docs/metatheory.md lines 284 to 287, where the scrutinee run and the branch run need one common budget, and it charges through lib/finite_term.ml line 47.
-/
theorem caseMono : ∀ (w : Value) (f j : Nat) (rhoR : List Value) (bs : List (String × Term))
    (v : Value) (rest : Nat),
    (match w with
      | .tag l p => evaluateBranch f rhoR l p bs
      | .atom .. => (Except.error Err.expectedLan : Res (Value × Nat))
      | .«section» .. => (Except.error Err.expectedLan : Res (Value × Nat))) = .ok (v, rest) →
    (match w with
      | .tag l p => evaluateBranch (j + f) rhoR l p bs
      | .atom .. => (Except.error Err.expectedLan : Res (Value × Nat))
      | .«section» .. => (Except.error Err.expectedLan : Res (Value × Nat))) = .ok (v, rest + j)
  | .atom _n, _f, _j, _rR, _bs, _v, _rest, h => (res_error_ne_ok h).elim
  | .«section» _fs, _f, _j, _rR, _bs, _v, _rest, h => (res_error_ne_ok h).elim
  | .tag l p, f, j, rhoR, bs, v, rest, h => branchAtSwap bs f j rest rhoR l p v h

/-- `branchSplit` proves an existential goal under a label test from one proof per side.
The label test is the branch search of lib/finite_term.ml lines 251 to 253, and the two sides are the selected branch and the rest of docs/metatheory.md lines 284 to 287.
-/
theorem branchSplit {p : Prop} [inst : Decidable p] {A B : Res (Value × Nat)}
    {C D : Nat → Res (Value × Nat)} {v : Value} {rest : Nat}
    (ht : p → A = .ok (v, rest) → ∃ (f' rest' : Nat), C f' = .ok (v, rest'))
    (hf : ¬ p → B = .ok (v, rest) → ∃ (f' rest' : Nat), D f' = .ok (v, rest'))
    (h : (if p then A else B) = .ok (v, rest)) :
    ∃ (f' rest' : Nat), (if p then C f' else D f') = .ok (v, rest') :=
  match inst with
  | isTrue hp =>
      match ht hp h with
      | ⟨f', rest', hh⟩ => ⟨f', rest', hh⟩
  | isFalse hp =>
      match hf hp h with
      | ⟨f', rest', hh⟩ => ⟨f', rest', hh⟩

mutual

/-- `evalSub` states Theorem 5 of docs/metatheory.md lines 267 to 287 for the pure substitution form of
Substitution.lean. The recursion is structural on the body, generalized over the depth, the prefix `D` and the environment, per docs/metatheory.md lines 275 to 276.
It mirrors `substitute_core` at lib/finite_term.ml lines 139 to 151 against `evaluate` at lib/finite_term.ml lines 236 to 260.
The substituted side evaluates the replacement once for each occurrence, so the fuel and the remaining budget stay existential, per docs/metatheory.md lines 268 to 269.
-/
theorem evalSub : ∀ (b : Term) (f : Nat) (dd rho : List Value) (r : Term) (u v : Value)
    (rest : Nat),
    (∃ (f0 rest0 : Nat), evaluate f0 rho r = .ok (u, rest0)) →
    evaluate f (dd ++ u :: rho) b = .ok (v, rest) →
      ∃ (f' rest' : Nat),
        evaluate f' (dd ++ rho) (Substitution.subPure dd.length r b) = .ok (v, rest')
  | .var index, f, dd, rho, r, u, v, rest, hr, h =>
      varSubEval index f dd rho r u v rest hr h
  | .atom _name, _f, _dd, _rho, _r, _u, _v, _rest, _hr, h =>
      match res_bind_ok h with
      | ⟨_g, _ht, hv⟩ =>
          ⟨1, 0,
            congrArg (fun (z : Value) => (Except.ok (z, 0) : Res (Value × Nat)))
              (congrArg Prod.fst (Except.ok.inj hv))⟩
  | .tag _label payload, _f, dd, rho, r, u, _v, _rest, hr, h =>
      match res_bind_ok h with
      | ⟨g, _ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨p, hp, h3⟩ =>
              match evalSub payload g dd rho r u p.1 p.2 hr hp with
              | ⟨f1, r1, he1⟩ =>
                  ⟨f1 + 1, r1,
                    res_bind_mk (a := f1) (tick_succ f1)
                      (res_bind_mk (a := (p.1, r1)) he1
                        (congrArg (fun (z : Value) => (Except.ok (z, r1) : Res (Value × Nat)))
                          (congrArg Prod.fst (Except.ok.inj h3))))⟩
  | .«section» fields, _f, dd, rho, r, u, _v, _rest, hr, h =>
      match res_bind_ok h with
      | ⟨g, _ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨sorted, hcan, h3⟩ =>
              match res_bind_ok h3 with
              | ⟨res, hres, h4⟩ =>
                  match evalSubEntries fields g dd rho r u res.1 res.2 hr hres with
                  | ⟨f1, r1, he1⟩ =>
                      ⟨f1 + 1, r1,
                        res_bind_mk (a := f1) (tick_succ f1)
                          (res_bind_mk (a := Substitution.subPureEntries dd.length r sorted)
                            ((Substitution.canonicalSub dd.length r fields).trans
                              (congrArg
                                (fun (z : Res (List (String × Term))) =>
                                  z.map (Substitution.subPureEntries dd.length r))
                                hcan))
                            (res_bind_mk (a := (res.1, r1)) he1
                              (congrArg
                                (fun (z : Value) => (Except.ok (z, r1) : Res (Value × Nat)))
                                (congrArg Prod.fst (Except.ok.inj h4)))))⟩
  | .«case» scrutinee _scrutineeType branches, _f, dd, rho, r, u, v, rest, hr, h =>
      match res_bind_ok h with
      | ⟨g, _ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨res, hres, h3⟩ =>
              match evalSub scrutinee g dd rho r u res.1 res.2 hr hres with
              | ⟨f1, r1, he1⟩ =>
                  match caseSubTransfer res.1 res.2 (dd ++ u :: rho) (dd ++ rho) branches
                          (Substitution.subPureEntries (dd.length + 1) r branches) v rest
                          (fun (l : String) (p : Value) => fun hb =>
                            evalSubBranch branches res.2 dd rho r u l p v rest hr hb)
                          h3 with
                  | ⟨f2, r2, he2⟩ =>
                      ⟨f1 + f2 + 1, r2 + r1,
                        res_bind_mk (a := f1 + f2) (tick_succ (f1 + f2))
                          (res_bind_mk (a := (res.1, r1 + f2))
                            (evaluate_mono_add (Substitution.subPure dd.length r scrutinee) f1 f2
                              (dd ++ rho) res.1 r1 he1)
                            (caseMono res.1 f2 r1 (dd ++ rho)
                              (Substitution.subPureEntries (dd.length + 1) r branches) v r2 he2))⟩
  | .project field _sectionType label, _f, dd, rho, r, u, v, rest, hr, h =>
      match res_bind_ok h with
      | ⟨g, _ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨res, hres, h3⟩ =>
              match evalSub field g dd rho r u res.1 res.2 hr hres with
              | ⟨f1, r1, he1⟩ =>
                  ⟨f1 + 1, r1,
                    res_bind_mk (a := f1) (tick_succ f1)
                      (res_bind_mk (a := (res.1, r1)) he1
                        (projectTransfer res.1 label res.2 r1 v rest h3))⟩

/-- `evalSubEntries` states `evalSub` for a section field list.
It mirrors `map_entries` at lib/finite_term.ml lines 130 to 135 against `evaluate_entries` at lib/finite_term.ml lines 261 to 266, and it serves the section case of docs/metatheory.md line 276.
The two field runs take one common budget through `entriesAtSwap`.
-/
theorem evalSubEntries : ∀ (es : List (String × Term)) (f : Nat) (dd rho : List Value) (r : Term)
    (u : Value) (vs : List (String × Value)) (rest : Nat),
    (∃ (f0 rest0 : Nat), evaluate f0 rho r = .ok (u, rest0)) →
    evaluateEntries f (dd ++ u :: rho) es = .ok (vs, rest) →
      ∃ (f' rest' : Nat),
        evaluateEntries f' (dd ++ rho) (Substitution.subPureEntries dd.length r es)
          = .ok (vs, rest')
  | [], _f, _dd, _rho, _r, _u, _vs, _rest, _hr, h =>
      ⟨0, 0,
        congrArg
          (fun (z : List (String × Value)) =>
            (Except.ok (z, 0) : Res (List (String × Value) × Nat)))
          (congrArg Prod.fst (Except.ok.inj h))⟩
  | (_label, field) :: more, f, dd, rho, r, u, _vs, _rest, hr, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              match evalSub field f dd rho r u head.1 head.2 hr hhead with
              | ⟨f1, r1, he1⟩ =>
                  match evalSubEntries more head.2 dd rho r u tail.1 tail.2 hr htail with
                  | ⟨f2, r2, he2⟩ =>
                      ⟨f1 + f2, r2 + r1,
                        res_bind_mk (a := (head.1, r1 + f2))
                          (evaluate_mono_add (Substitution.subPure dd.length r field) f1 f2
                            (dd ++ rho) head.1 r1 he1)
                          (res_bind_mk (a := (tail.1, r2 + r1))
                            (entriesAtSwap (Substitution.subPureEntries dd.length r more) f2 r1 r2
                              (dd ++ rho) tail.1 he2)
                            (congrArg
                              (fun (z : List (String × Value)) =>
                                (Except.ok (z, r2 + r1) : Res (List (String × Value) × Nat)))
                              (congrArg Prod.fst (Except.ok.inj h3))))⟩

/-- `evalSubBranch` states `evalSub` for a branch list of a case term.
The selected branch takes the prefix `payload :: D` and the depth `d + 1` of docs/metatheory.md lines 284 to 287, which matches the depth of lib/finite_term.ml line 125 and the environment of lib/finite_term.ml line 253.
-/
theorem evalSubBranch : ∀ (bs : List (String × Term)) (f : Nat) (dd rho : List Value) (r : Term)
    (u : Value) (label : String) (payload v : Value) (rest : Nat),
    (∃ (f0 rest0 : Nat), evaluate f0 rho r = .ok (u, rest0)) →
    evaluateBranch f (dd ++ u :: rho) label payload bs = .ok (v, rest) →
      ∃ (f' rest' : Nat),
        evaluateBranch f' (dd ++ rho) label payload
          (Substitution.subPureEntries (dd.length + 1) r bs) = .ok (v, rest')
  | [], _f, _dd, _rho, _r, _u, _label, _payload, _v, _rest, _hr, h => (res_error_ne_ok h).elim
  | (_key, body) :: more, f, dd, rho, r, u, label, payload, v, rest, hr, h =>
      branchSplit
        (fun _hc hh => evalSub body f (payload :: dd) rho r u v rest hr hh)
        (fun _hc hh => evalSubBranch more f dd rho r u label payload v rest hr hh)
        h

end

end EvalSubst

/-- `shift_preserves_value` states Lemma 3 of docs/metatheory.md lines 252 to 265.
The prefix `e` has the length `c`, the inserted block `dd` has the length `d`, and one successful `shift` run of
Subst.lean supplies the shifted term, which mirrors `map_variables` at lib/finite_term.ml lines 112 to 129 through the index map of lib/finite_term.ml line 148.
The conclusion holds at a large enough budget, per docs/metatheory.md lines 254 to 255, so the fuel stays existential.
-/
theorem shift_preserves_value (c d : Nat) (e dd rho : List Value) (r r' : Term)
    (fs rsf f rest : Nat) (u : Value)
    (hc : e.length = c) (hd : dd.length = d)
    (hshift : shift c d fs r = .ok (r', rsf))
    (heval : evaluate f (e ++ rho) r = .ok (u, rest)) :
    ∃ (f' rest' : Nat), evaluate f' (e ++ dd ++ rho) r' = .ok (u, rest') :=
  ⟨f, rest,
    Eq.mp
      (congrArg (fun (z : Term) => evaluate f (e ++ dd ++ rho) z = Except.ok (u, rest))
        (((congrArg (fun (z : Nat) => Weakening.shiftPure z dd.length r) hc).trans
            (congrArg (fun (z : Nat) => Weakening.shiftPure c z r) hd)).trans
          (Weakening.shiftOkPure c d r fs (r', rsf) hshift).symm))
      (EvalSubst.evalShift r f e dd rho u rest heval)⟩

/-- `evaluate_sub_env` states Theorem 5 of docs/metatheory.md lines 267 to 287.
The prefix `dd` has the length `d`, and one successful `sub` run of Subst.lean supplies the substituted body, which mirrors
`substitute_core` at lib/finite_term.ml lines 139 to 151 against `evaluate` at lib/finite_term.ml lines 236 to 260.
The conclusion holds at a large enough budget, per docs/metatheory.md lines 268 to 269, so the fuel stays existential, and the claim covers a successful evaluation only, per docs/metatheory.md lines 271 to 274.
-/
theorem evaluate_sub_env (d : Nat) (dd rho : List Value) (r b b' : Term)
    (fs rsf f0 rest0 f rest : Nat) (u v : Value)
    (hd : dd.length = d)
    (hsub : sub d r fs b = .ok (b', rsf))
    (hr : evaluate f0 rho r = .ok (u, rest0))
    (hb : evaluate f (dd ++ u :: rho) b = .ok (v, rest)) :
    ∃ (f' rest' : Nat), evaluate f' (dd ++ rho) b' = .ok (v, rest') :=
  match EvalSubst.evalSub b f dd rho r u v rest ⟨f0, rest0, hr⟩ hb with
  | ⟨f', rest', hh⟩ =>
      ⟨f', rest',
        Eq.mp
          (congrArg (fun (z : Term) => evaluate f' (dd ++ rho) z = Except.ok (v, rest'))
            ((congrArg (fun (z : Nat) => Substitution.subPure z r b) hd).trans
              (Substitution.subOkPure d r b fs rsf b' hsub).symm))
          hh⟩

/-- `gapReplacement` is the replacement term of the claim C5 witness.
It mirrors a tagged atom of lib/finite_term.ml lines 241 to 243, and it costs two budget units, which docs/metatheory.md lines 288 to 290 needs.
-/
def gapReplacement : Term := .tag "a" (.atom "x")

/-- `gapBody` is the body term of the claim C5 witness. It holds one occurrence of the index zero, so
`substitute_core` of lib/finite_term.ml lines 139 to 151 plants one copy of the replacement, per docs/metatheory.md lines 288 to 290.
-/
def gapBody : Term := .tag "b" (.var 0)

/-- `gapSubstituted` is the substituted body of the claim C5 witness.
It is the result of `sub` on `gapBody`, and it costs one unit more than
`gapBody`, which is the budget gap of docs/metatheory.md lines 288 to 290.
-/
def gapSubstituted : Term := .tag "b" (.tag "a" (.atom "x"))

/-- `gapValue` is the value of `gapReplacement`. It is the environment entry of docs/metatheory.md line 268 for the run of lib/finite_term.ml lines 236 to 243.
-/
def gapValue : Value := .tag "a" (.atom "x")

/-- `gapResult` is the common value of both sides of the claim C5 witness.
Theorem 5 states the agreement of this value only, per docs/metatheory.md lines 288 to 290, for the run of lib/finite_term.ml lines 236 to 243.
-/
def gapResult : Value := .tag "b" gapValue

/-- `evaluate_sub_budget_gap` states claim C5 of docs/metatheory.md lines 288 to 290.
At the budget two the environment side succeeds while the substituted side exhausts, and the substituted side succeeds at the budget three, so the budget hypothesis of
Theorem 5 is real. The gap holds because the environment side reads the value of the replacement from the environment while the substituted side evaluates one copy of the replacement, which lib/finite_term.ml line 47 charges.
-/
theorem evaluate_sub_budget_gap :
    ∃ (dd rho : List Value) (r b b' : Term) (u v : Value) (f0 rest0 f rest fs rsf : Nat),
      evaluate f0 rho r = .ok (u, rest0) ∧
      evaluate f (dd ++ u :: rho) b = .ok (v, rest) ∧
      sub dd.length r fs b = .ok (b', rsf) ∧
      evaluate f (dd ++ rho) b' = .error .resourceExhausted ∧
      ∃ (fbig restbig : Nat), evaluate fbig (dd ++ rho) b' = .ok (v, restbig) :=
  ⟨[], [], gapReplacement, gapBody, gapSubstituted, gapValue, gapResult, 2, 0, 2, 0, 8, 4, rfl, rfl, rfl, rfl, ⟨3, 0, rfl⟩⟩
