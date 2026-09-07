import KanEvmProofs.Check
import KanEvmProofs.Subst
import KanEvmProofs.Eval
import KanEvmProofs.Reduce

/-! # Budget lemmas of the finite fragment

This module states the budget propositions of docs/metatheory.md lines 87 to 109.
Row Lemma1 becomes five propositions, one per fueled function of decision S2-D4.
Row Check-gas pays for the structural gas parameter of decision S2-D5.
Row Lemma2 states the exact cost of a check, and row Lemma2b states the charges of one reduction step of lib/finite_term.ml lines 162 to 225.
Every proof runs in term mode through the equation compiler, so no tactic block appears here.
-/

universe u

/-- `res_error_ne_ok` states that an error is no success in the monad of decision S2-D3.
It refutes an impossible branch of a chain of lib/finite_term.ml lines 62 to 105.
-/
theorem res_error_ne_ok {α : Type} {x : Err} {v : α} (h : (Except.error x : Res α) = .ok v) :
    False :=
  cast (congrArg (fun z : Res α => match z with | .error .. => False | .ok .. => True) h).symm
    True.intro

/-- `res_bind_ok` inverts one successful bind of the error monad of decision S2-D3.
It reads a chain of lib/finite_term.ml lines 62 to 105 one step at a time.
The Lean form of an OCaml `let*` chain is a bind, so this lemma opens every proof step below.
-/
theorem res_bind_ok {α β : Type} {e : Res α} {cont : α → Res β} {v : β}
    (h : e >>= cont = .ok v) : ∃ a : α, e = .ok a ∧ cont a = .ok v :=
  match e, h with
  | .ok a, hh => ⟨a, rfl, hh⟩
  | .error _x, hh => (res_error_ne_ok hh).elim

/-- `res_bind_mk` builds one successful bind of the error monad of decision S2-D3.
It is the partner of `res_bind_ok` and it rebuilds a chain at a second budget.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem res_bind_mk {α β : Type} {e : Res α} {a : α} {cont : α → Res β} {v : β}
    (he : e = .ok a) (hk : cont a = .ok v) : (e >>= cont) = .ok v :=
  (congrArg (fun z => z >>= cont) he).trans hk

/-- `ok_pair_add` raises the budget component of one successful pair result.
Every fueled function of decision S2-D4 returns a value and the remaining budget.
This statement closes the leaf of each monotonicity proof of docs/metatheory.md lines 87 to 91.
-/
theorem ok_pair_add {A : Type} {u x : A} {g rest : Nat} (j : Nat)
    (h : (Except.ok (u, g) : Res (A × Nat)) = .ok (x, rest)) :
    (Except.ok (u, g + j) : Res (A × Nat)) = .ok (x, rest + j) :=
  congrArg (fun p : A × Nat => (Except.ok (p.1, p.2 + j) : Res (A × Nat))) (Except.ok.inj h)

/-- `ite_case` reads one conditional of lib/finite_term.ml at two budgets at once.
The condition of each conditional of the fragment never reads the budget, so both runs take the same branch, which is the argument of docs/metatheory.md lines 89 to 91.
-/
theorem ite_case {c : Prop} [inst : Decidable c] {α β : Sort u} {a b : α} {x y : β}
    {P : α → β → Prop} (ha : c → P a x) (hb : ¬ c → P b y) :
    P (if c then a else b) (if c then x else y) :=
  match inst with
  | isTrue hc => ha hc
  | isFalse hc => hb hc

/-- `option_case` reads one `Option.elim` of lib/finite_term.ml lines 40 to 45 at two budgets.
The option value never reads the budget, so both runs take the same branch.
-/
theorem option_case {α : Type} {o : Option α} {β γ : Type} {n1 : β} {n2 : γ}
    {s1 : α → β} {s2 : α → γ} {P : β → γ → Prop} (hn : P n1 n2) (hs : ∀ a : α, P (s1 a) (s2 a)) :
    P (o.elim n1 s1) (o.elim n2 s2) :=
  match o with
  | none => hn
  | some a => hs a

/-- `tick_add_succ` runs `tick` of lib/finite_term.ml line 47 at a raised budget.
A budget above zero spends one unit and it keeps the raise.
-/
theorem tick_add_succ (f j : Nat) : tick (f + 1 + j) = .ok (f + j) :=
  congrArg tick (Nat.succ_add f j)

/-- `tick_mono` states docs/metatheory.md lines 87 to 91 for `tick` alone.
`tick` of lib/finite_term.ml line 47 is the only charge point, so this is the leaf of Lemma 1.
-/
theorem tick_mono : ∀ (f j rest : Nat), tick f = .ok rest → tick (f + j) = .ok (rest + j)
  | 0, _j, _rest, hh => (res_error_ne_ok hh).elim
  | f + 1, j, _rest, hh =>
      (tick_add_succ f j).trans
        (congrArg (fun z : Nat => (Except.ok (z + j) : Res Nat)) (Except.ok.inj hh))

/-- `tick_cost` states that one tick of lib/finite_term.ml line 47 spends exactly one unit.
It is the leaf of the cost lemma of docs/metatheory.md lines 92 to 96.
-/
theorem tick_cost : ∀ (f rest : Nat), tick f = .ok rest → rest + 1 = f
  | 0, _rest, hh => (res_error_ne_ok hh).elim
  | _f + 1, _rest, hh => congrArg (fun z : Nat => z + 1) (Except.ok.inj hh).symm

/-- `nat_recover` rebuilds the larger budget of docs/metatheory.md lines 87 to 91.
The raise `f' - f` returns `f'` once `f` is below `f'`.
-/
theorem nat_recover {f f' : Nat} (h : f ≤ f') : f + (f' - f) = f' := Nat.add_sub_cancel' h

/-- `rest_recover` moves the raise of docs/metatheory.md lines 87 to 91 out of the sum.
The statement of Lemma 1 reads `rest + f' - f`, and each proof below builds `rest + (f' - f)`.
-/
theorem rest_recover (rest : Nat) {f f' : Nat} (h : f ≤ f') :
    rest + (f' - f) = rest + f' - f := (Nat.add_sub_assoc h rest).symm

mutual
/-- `shift_mono_add` states docs/metatheory.md lines 87 to 91 for `shift` at a raise `j`.
`shift` mirrors lib/finite_term.ml lines 112 to 135, and it ticks once for one term node.
The raised run takes the same branch at every node and it returns the same term.
-/
theorem shift_mono_add : ∀ (t : Term) (c d f j : Nat) (x : Term) (rest : Nat),
    shift c d f t = .ok (x, rest) → shift c d (f + j) t = .ok (x, rest + j)
  | .var _i, _c, _d, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, hv⟩ => res_bind_mk (a := g + j) (tick_mono f j g ht) (ok_pair_add j hv)
  | .atom _l, _c, _d, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, hv⟩ => res_bind_mk (a := g + j) (tick_mono f j g ht) (ok_pair_add j hv)
  | .tag _l p, c, d, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (r.1, r.2 + j))
                  (shift_mono_add p c d g j r.1 r.2 hr) (ok_pair_add j h3))
  | .«section» fields, c, d, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (r.1, r.2 + j))
                  (shift_entries_mono_add fields c d g j r.1 r.2 hr) (ok_pair_add j h3))
  | .«case» s _st br, c, d, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨head, hh1, h3⟩ =>
              match res_bind_ok h3 with
              | ⟨tail, ht2, h4⟩ =>
                  res_bind_mk (a := g + j) (tick_mono f j g ht)
                    (res_bind_mk (a := (head.1, head.2 + j))
                      (shift_mono_add s c d g j head.1 head.2 hh1)
                      (res_bind_mk (a := (tail.1, tail.2 + j))
                        (shift_entries_mono_add br (c + 1) d head.2 j tail.1 tail.2 ht2)
                        (ok_pair_add j h4)))
  | .project fl _st _l, c, d, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (r.1, r.2 + j))
                  (shift_mono_add fl c d g j r.1 r.2 hr) (ok_pair_add j h3))

/-- `shift_entries_mono_add` is the entry list partner of `shift_mono_add`.
`shiftEntries` mirrors lib/finite_term.ml lines 130 to 135 and it holds no charge point.
-/
theorem shift_entries_mono_add : ∀ (es : List (String × Term)) (c d f j : Nat)
    (ys : List (String × Term)) (rest : Nat),
    shiftEntries c d f es = .ok (ys, rest) → shiftEntries c d (f + j) es = .ok (ys, rest + j)
  | [], _c, _d, _f, j, _ys, _rest, h => ok_pair_add j h
  | (_label, field) :: more, c, d, f, j, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hh1, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, ht2, h3⟩ =>
              res_bind_mk (a := (head.1, head.2 + j))
                (shift_mono_add field c d f j head.1 head.2 hh1)
                (res_bind_mk (a := (tail.1, tail.2 + j))
                  (shift_entries_mono_add more c d head.2 j tail.1 tail.2 ht2)
                  (ok_pair_add j h3))
end

/-- `budget_monotone_shift` states row Lemma1 of the theorem inventory for `shift`.
It states docs/metatheory.md lines 87 to 91 for lib/finite_term.ml lines 112 to 135.
A result at budget `f` returns the same term and the raised budget at every `f'` above `f`.
-/
theorem budget_monotone_shift (c d f f' : Nat) (t x : Term) (rest : Nat)
    (hle : f ≤ f') (h : shift c d f t = .ok (x, rest)) :
    shift c d f' t = .ok (x, rest + f' - f) :=
  (congrArg (fun z => shift c d z t) (nat_recover hle)).symm.trans
    ((shift_mono_add t c d f (f' - f) x rest h).trans
      (congrArg (fun z : Nat => (Except.ok (x, z) : Res (Term × Nat))) (rest_recover rest hle)))

mutual
/-- `sub_mono_add` states docs/metatheory.md lines 87 to 91 for `sub` at a raise `j`.
`sub` mirrors lib/finite_term.ml lines 112 to 151, and it ticks once for one term node.
The hit arm calls `shift` on the replacement, which raises its budget through
`shift_mono_add`, as lines 146 to 149 of the OCaml file ask.
-/
theorem sub_mono_add : ∀ (t : Term) (d : Nat) (r : Term) (f j : Nat) (x : Term) (rest : Nat),
    sub d r f t = .ok (x, rest) → sub d r (f + j) t = .ok (x, rest + j)
  | .var _index, d, r, f, j, x, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          res_bind_mk (a := g + j) (tick_mono f j g ht)
            (ite_case (P := fun (u v : Res (Term × Nat)) => u = .ok (x, rest) → v = .ok (x, rest + j))
              (fun _hc hh => ok_pair_add j hh)
              (fun _hc =>
                ite_case
                  (P := fun (u v : Res (Term × Nat)) => u = .ok (x, rest) → v = .ok (x, rest + j))
                  (fun _hd hh => ok_pair_add j hh)
                  (fun _hd hh => shift_mono_add r 0 d g j x rest hh))
              h2)
  | .atom _l, _d, _r, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, hv⟩ => res_bind_mk (a := g + j) (tick_mono f j g ht) (ok_pair_add j hv)
  | .tag _l p, d, r, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (q.1, q.2 + j))
                  (sub_mono_add p d r g j q.1 q.2 hq) (ok_pair_add j h3))
  | .«section» fields, d, r, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (q.1, q.2 + j))
                  (sub_entries_mono_add fields d r g j q.1 q.2 hq) (ok_pair_add j h3))
  | .«case» s _st br, d, r, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨head, hh1, h3⟩ =>
              match res_bind_ok h3 with
              | ⟨tail, ht2, h4⟩ =>
                  res_bind_mk (a := g + j) (tick_mono f j g ht)
                    (res_bind_mk (a := (head.1, head.2 + j))
                      (sub_mono_add s d r g j head.1 head.2 hh1)
                      (res_bind_mk (a := (tail.1, tail.2 + j))
                        (sub_entries_mono_add br (d + 1) r head.2 j tail.1 tail.2 ht2)
                        (ok_pair_add j h4)))
  | .project fl _st _l, d, r, f, j, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (q.1, q.2 + j))
                  (sub_mono_add fl d r g j q.1 q.2 hq) (ok_pair_add j h3))

/-- `sub_entries_mono_add` is the entry list partner of `sub_mono_add`.
`subEntries` mirrors lib/finite_term.ml lines 130 to 135 and it holds no charge point.
-/
theorem sub_entries_mono_add : ∀ (es : List (String × Term)) (d : Nat) (r : Term) (f j : Nat)
    (ys : List (String × Term)) (rest : Nat),
    subEntries d r f es = .ok (ys, rest) → subEntries d r (f + j) es = .ok (ys, rest + j)
  | [], _d, _r, _f, j, _ys, _rest, h => ok_pair_add j h
  | (_label, field) :: more, d, r, f, j, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hh1, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, ht2, h3⟩ =>
              res_bind_mk (a := (head.1, head.2 + j))
                (sub_mono_add field d r f j head.1 head.2 hh1)
                (res_bind_mk (a := (tail.1, tail.2 + j))
                  (sub_entries_mono_add more d r head.2 j tail.1 tail.2 ht2)
                  (ok_pair_add j h3))
end

/-- `budget_monotone_sub` states row Lemma1 of the theorem inventory for `sub`.
It states docs/metatheory.md lines 87 to 91 for lib/finite_term.ml lines 112 to 151.
-/
theorem budget_monotone_sub (d : Nat) (r : Term) (f f' : Nat) (t x : Term) (rest : Nat)
    (hle : f ≤ f') (h : sub d r f t = .ok (x, rest)) :
    sub d r f' t = .ok (x, rest + f' - f) :=
  (congrArg (fun z => sub d r z t) (nat_recover hle)).symm.trans
    ((sub_mono_add t d r f (f' - f) x rest h).trans
      (congrArg (fun z : Nat => (Except.ok (x, z) : Res (Term × Nat))) (rest_recover rest hle)))

mutual
/-- `evaluate_mono_add` states docs/metatheory.md lines 87 to 91 for `evaluate` at a raise `j`.
`evaluate` mirrors lib/finite_term.ml lines 231 to 266, and it ticks once for one entered node.
The environment and the branch choice never read the budget, so the raised run returns the same value, as lines 89 to 91 of the metatheory state.
-/
theorem evaluate_mono_add : ∀ (t : Term) (f j : Nat) (rho : List Value) (v : Value) (rest : Nat),
    evaluate f rho t = .ok (v, rest) → evaluate (f + j) rho t = .ok (v, rest + j)
  | .var index, f, j, rho, v, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          res_bind_mk (a := g + j) (tick_mono f j g ht)
            (option_case (o := rho[index]?)
              (P := fun (u w : Res (Value × Nat)) => u = .ok (v, rest) → w = .ok (v, rest + j))
              (fun hh => (res_error_ne_ok hh).elim) (fun _value hh => ok_pair_add j hh) h2)
  | .atom _name, f, j, _rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, hv⟩ => res_bind_mk (a := g + j) (tick_mono f j g ht) (ok_pair_add j hv)
  | .tag _label payload, f, j, rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (r.1, r.2 + j))
                  (evaluate_mono_add payload g j rho r.1 r.2 hr) (ok_pair_add j h3))
  | .«section» entries, f, j, rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨sorted, hsorted, h3⟩ =>
              match res_bind_ok h3 with
              | ⟨r, hr, h4⟩ =>
                  res_bind_mk (a := g + j) (tick_mono f j g ht)
                    (res_bind_mk (a := sorted) hsorted
                      (res_bind_mk (a := (r.1, r.2 + j))
                        (evaluate_entries_mono_add entries g j rho r.1 r.2 hr)
                        (ok_pair_add j h4)))
  | .«case» scrutinee _st branches, f, j, rho, v, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (r.1, r.2 + j))
                  (evaluate_mono_add scrutinee g j rho r.1 r.2 hr)
                  (match r.1, h3 with
                    | .tag label payload, hh =>
                        evaluate_branch_mono_add branches r.2 j rho label payload v rest hh
                    | .atom .., hh => (res_error_ne_ok hh).elim
                    | .«section» .., hh => (res_error_ne_ok hh).elim))
  | .project field _st _label, f, j, rho, _v, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨r, hr, h3⟩ =>
              res_bind_mk (a := g + j) (tick_mono f j g ht)
                (res_bind_mk (a := (r.1, r.2 + j))
                  (evaluate_mono_add field g j rho r.1 r.2 hr)
                  (match r.1, h3 with
                    | .«section» .., hh =>
                        match res_bind_ok hh with
                        | ⟨value, hlookup, h4⟩ =>
                            res_bind_mk (a := value) hlookup (ok_pair_add j h4)
                    | .atom .., hh => (res_error_ne_ok hh).elim
                    | .tag .., hh => (res_error_ne_ok hh).elim))

/-- `evaluate_entries_mono_add` is the entry list partner of `evaluate_mono_add`.
`evaluateEntries` mirrors lib/finite_term.ml lines 261 to 266 and it holds no charge point.
-/
theorem evaluate_entries_mono_add : ∀ (es : List (String × Term)) (f j : Nat) (rho : List Value)
    (vs : List (String × Value)) (rest : Nat),
    evaluateEntries f rho es = .ok (vs, rest) → evaluateEntries (f + j) rho es = .ok (vs, rest + j)
  | [], _f, j, _rho, _vs, _rest, h => ok_pair_add j h
  | (_label, field) :: more, f, j, rho, _vs, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              res_bind_mk (a := (head.1, head.2 + j))
                (evaluate_mono_add field f j rho head.1 head.2 hhead)
                (res_bind_mk (a := (tail.1, tail.2 + j))
                  (evaluate_entries_mono_add more head.2 j rho tail.1 tail.2 htail)
                  (ok_pair_add j h3))

/-- `evaluate_branch_mono_add` is the branch list partner of `evaluate_mono_add`.
`evaluateBranch` replaces the branch lookup of lib/finite_term.ml lines 252 and 253, per decision
S2-D5, and it holds no charge point, so it hands the raised budget on unchanged.
-/
theorem evaluate_branch_mono_add : ∀ (bs : List (String × Term)) (f j : Nat) (rho : List Value)
    (label : String) (payload : Value) (v : Value) (rest : Nat),
    evaluateBranch f rho label payload bs = .ok (v, rest) →
      evaluateBranch (f + j) rho label payload bs = .ok (v, rest + j)
  | [], _f, _j, _rho, _label, _payload, _v, _rest, h => (res_error_ne_ok h).elim
  | (_key, body) :: more, f, j, rho, label, payload, v, rest, h =>
      ite_case (P := fun (u w : Res (Value × Nat)) => u = .ok (v, rest) → w = .ok (v, rest + j))
        (fun _hc hh => evaluate_mono_add body f j (payload :: rho) v rest hh)
        (fun _hc hh => evaluate_branch_mono_add more f j rho label payload v rest hh) h
end

/-- `budget_monotone_evaluate` states row Lemma1 of the theorem inventory for `evaluate`.
It states docs/metatheory.md lines 87 to 91 for lib/finite_term.ml lines 231 to 266.
-/
theorem budget_monotone_evaluate (f f' : Nat) (rho : List Value) (t : Term) (v : Value)
    (rest : Nat) (hle : f ≤ f') (h : evaluate f rho t = .ok (v, rest)) :
    evaluate f' rho t = .ok (v, rest + f' - f) :=
  (congrArg (fun z => evaluate z rho t) (nat_recover hle)).symm.trans
    ((evaluate_mono_add t f (f' - f) rho v rest h).trans
      (congrArg (fun z : Nat => (Except.ok (v, z) : Res (Value × Nat))) (rest_recover rest hle)))

/-- `ok_nat_add` raises the budget of one successful check result.
`checkCore` of lib/finite_term.ml lines 62 to 105 returns the remaining budget alone, so the leaf of its monotonicity proof reads a bare
`Nat` and not a pair.
-/
theorem ok_nat_add {g rest : Nat} (j : Nat) (h : (Except.ok g : Res Nat) = .ok rest) :
    (Except.ok (g + j) : Res Nat) = .ok (rest + j) :=
  congrArg (fun z : Nat => (Except.ok (z + j) : Res Nat)) (Except.ok.inj h)

mutual
/-- `check_core_mono_add` states docs/metatheory.md lines 87 to 91 for `checkCore` at a raise `j`.
`checkCore` mirrors lib/finite_term.ml lines 62 to 105, and it ticks once for one entered node.
The gas parameter of decision S2-D5 stays fixed, since gas is no budget, as section 3 of the stage brief states of row
Lemma1.
-/
theorem check_core_mono_add : ∀ (gas : Nat) (t : Term) (f j : Nat) (ctx : List Ty) (a : Ty)
    (rest : Nat),
    checkCore gas f ctx t a = .ok rest → checkCore gas (f + j) ctx t a = .ok (rest + j)
  | 0, _t, _f, _j, _ctx, _a, _rest, h => (res_error_ne_ok h).elim
  | gasPred + 1, t, f, j, ctx, a, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          res_bind_mk (a := g + j) (tick_mono f j g ht)
            (match t, h2 with
              | .var _index, hh =>
                  match res_bind_ok hh with
                  | ⟨actual, hv, h3⟩ =>
                      res_bind_mk (a := actual) hv
                        (ite_case
                          (P := fun (u w : Res Nat) => u = .ok rest → w = .ok (rest + j))
                          (fun _hc h4 => ok_nat_add j h4)
                          (fun _hc h4 => (res_error_ne_ok h4).elim) h3)
              | .atom _name, hh =>
                  match a, hh with
                  | .atoms .., h3 =>
                      ite_case (P := fun (u w : Res Nat) => u = .ok rest → w = .ok (rest + j))
                        (fun _hc h4 => ok_nat_add j h4)
                        (fun _hc h4 => (res_error_ne_ok h4).elim) h3
                  | .lan .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim
              | .tag _label payload, hh =>
                  match a, hh with
                  | .lan .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨fiber, hf, h4⟩ =>
                          res_bind_mk (a := fiber) hf
                            (check_core_mono_add gasPred payload g j ctx fiber rest h4)
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim
              | .«section» _entries, hh =>
                  match a, hh with
                  | .ran .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨sorted, hs, h4⟩ =>
                          res_bind_mk (a := sorted) hs
                            (match res_bind_ok h4 with
                              | ⟨pairs, hp, h5⟩ =>
                                  res_bind_mk (a := pairs) hp
                                    (check_fields_mono_add gasPred pairs g j ctx rest h5))
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .lan .., h3 => (res_error_ne_ok h3).elim
              | .«case» scrutinee st _branches, hh =>
                  match st, hh with
                  | .lan fibers, h3 =>
                      match res_bind_ok h3 with
                      | ⟨sorted, hs, h4⟩ =>
                          res_bind_mk (a := sorted) hs
                            (match res_bind_ok h4 with
                              | ⟨pairs, hp, h5⟩ =>
                                  res_bind_mk (a := pairs) hp
                                    (match res_bind_ok h5 with
                                      | ⟨f2, hf2, h6⟩ =>
                                          res_bind_mk (a := f2 + j)
                                            (check_core_mono_add gasPred scrutinee g j ctx
                                              (Ty.lan fibers) f2 hf2)
                                            (check_branches_mono_add gasPred pairs f2 j ctx a rest
                                              h6)))
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim
              | .project field st _label, hh =>
                  match st, hh with
                  | .ran fibers, h3 =>
                      match res_bind_ok h3 with
                      | ⟨actual, hl, h4⟩ =>
                          res_bind_mk (a := actual) hl
                            (ite_case
                              (P := fun (u w : Res Nat) => u = .ok rest → w = .ok (rest + j))
                              (fun _hc h5 =>
                                check_core_mono_add gasPred field g j ctx (Ty.ran fibers) rest h5)
                              (fun _hc h5 => (res_error_ne_ok h5).elim) h4)
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .lan .., h3 => (res_error_ne_ok h3).elim)

/-- `check_fields_mono_add` is the field list partner of `check_core_mono_add`.
`checkFields` replaces `check_many` of lib/finite_term.ml lines 103 to 105 and it holds no charge point of its own.
-/
theorem check_fields_mono_add : ∀ (gas : Nat) (pairs : List (String × Ty × Term)) (f j : Nat)
    (ctx : List Ty) (rest : Nat),
    checkFields gas f ctx pairs = .ok rest → checkFields gas (f + j) ctx pairs = .ok (rest + j)
  | 0, _pairs, _f, _j, _ctx, _rest, h => (res_error_ne_ok h).elim
  | gasPred + 1, pairs, f, j, ctx, rest, h =>
      match pairs, h with
      | [], hh => ok_nat_add j hh
      | (_label, fiber, field) :: more, hh =>
          match res_bind_ok hh with
          | ⟨f2, hf2, h2⟩ =>
              res_bind_mk (a := f2 + j)
                (check_core_mono_add gasPred field f j ctx fiber f2 hf2)
                (check_fields_mono_add gasPred more f2 j ctx rest h2)

/-- `check_branches_mono_add` is the branch list partner of `check_core_mono_add`.
`checkBranches` replaces `check_many` of lib/finite_term.ml lines 103 to 105 for the case rule of lines 86 to 95, and each body runs at the context that the payload type extends.
-/
theorem check_branches_mono_add : ∀ (gas : Nat) (pairs : List (String × Ty × Term)) (f j : Nat)
    (ctx : List Ty) (a : Ty) (rest : Nat),
    checkBranches gas f ctx pairs a = .ok rest →
      checkBranches gas (f + j) ctx pairs a = .ok (rest + j)
  | 0, _pairs, _f, _j, _ctx, _a, _rest, h => (res_error_ne_ok h).elim
  | gasPred + 1, pairs, f, j, ctx, a, rest, h =>
      match pairs, h with
      | [], hh => ok_nat_add j hh
      | (_label, payloadType, body) :: more, hh =>
          match res_bind_ok hh with
          | ⟨f2, hf2, h2⟩ =>
              res_bind_mk (a := f2 + j)
                (check_core_mono_add gasPred body f j (payloadType :: ctx) a f2 hf2)
                (check_branches_mono_add gasPred more f2 j ctx a rest h2)
end

/-- `budget_monotone_check` states row Lemma1 of the theorem inventory for `checkCore`.
It states docs/metatheory.md lines 87 to 91 for lib/finite_term.ml lines 62 to 105.
The gas argument stays fixed, since the gas of decision S2-D5 is no budget.
-/
theorem budget_monotone_check (gas f f' : Nat) (ctx : List Ty) (t : Term) (a : Ty) (rest : Nat)
    (hle : f ≤ f') (h : checkCore gas f ctx t a = .ok rest) :
    checkCore gas f' ctx t a = .ok (rest + f' - f) :=
  (congrArg (fun z => checkCore gas z ctx t a) (nat_recover hle)).symm.trans
    ((check_core_mono_add gas t f (f' - f) ctx a rest h).trans
      (congrArg (fun z : Nat => (Except.ok z : Res Nat)) (rest_recover rest hle)))

/-- `reduce_fields_mono_add` raises the budget of one field walk of the reducer.
`reduceFields` mirrors lib/finite_term.ml lines 210 to 216, it holds no charge point and it runs one step per field, so a raised step raises the whole walk.
-/
theorem reduce_fields_mono_add (step : Nat → Term → Ty → Res (Term × Nat)) (j : Nat)
    (hstep : ∀ (f : Nat) (x : Term) (a : Ty) (y : Term) (rest : Nat),
      step f x a = .ok (y, rest) → step (f + j) x a = .ok (y, rest + j)) :
    ∀ (fields : List (String × Ty × Term)) (f : Nat) (ys : List (String × Term)) (rest : Nat),
      reduceFields step f fields = .ok (ys, rest) →
        reduceFields step (f + j) fields = .ok (ys, rest + j)
  | [], _f, _ys, _rest, h => ok_pair_add j h
  | (_label, fiber, field) :: more, f, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              res_bind_mk (a := (head.1, head.2 + j)) (hstep f field fiber head.1 head.2 hhead)
                (res_bind_mk (a := (tail.1, tail.2 + j))
                  (reduce_fields_mono_add step j hstep more head.2 tail.1 tail.2 htail)
                  (ok_pair_add j h3))

/-- `reduce_branches_mono_add` raises the budget of one branch walk of the reducer.
`reduceBranches` mirrors lib/finite_term.ml lines 219 to 225, it holds no charge point and each body reduces at the expected type of the whole node.
-/
theorem reduce_branches_mono_add (step : Nat → Term → Ty → Res (Term × Nat)) (j : Nat)
    (hstep : ∀ (f : Nat) (x : Term) (a : Ty) (y : Term) (rest : Nat),
      step f x a = .ok (y, rest) → step (f + j) x a = .ok (y, rest + j)) :
    ∀ (fields : List (String × Ty × Term)) (f : Nat) (expected : Ty)
      (ys : List (String × Term)) (rest : Nat),
      reduceBranches step f fields expected = .ok (ys, rest) →
        reduceBranches step (f + j) fields expected = .ok (ys, rest + j)
  | [], _f, _expected, _ys, _rest, h => ok_pair_add j h
  | (_label, _fiber, body) :: more, f, expected, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              res_bind_mk (a := (head.1, head.2 + j)) (hstep f body expected head.1 head.2 hhead)
                (res_bind_mk (a := (tail.1, tail.2 + j))
                  (reduce_branches_mono_add step j hstep more head.2 expected tail.1 tail.2 htail)
                  (ok_pair_add j h3))

/-- `reduce_mono_add` states docs/metatheory.md lines 87 to 91 for `reduce` at a raise `j`.
`reduce` mirrors lib/finite_term.ml lines 162 to 225, and it ticks once for one entered node.
The gas parameter of decision S2-D6 stays fixed, since gas is no budget.
The case of a tag raises the budget of `substituteCore` through `sub_mono_add`, which mirrors lines 187 to 190 of the
OCaml file.
-/
theorem reduce_mono_add : ∀ (gas : Nat) (t : Term) (f j : Nat) (a : Ty) (x : Term) (rest : Nat),
    reduce gas f t a = .ok (x, rest) → reduce gas (f + j) t a = .ok (x, rest + j)
  | 0, _t, _f, _j, _a, _x, _rest, h => (res_error_ne_ok h).elim
  | gasPred + 1, t, f, j, a, x, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          res_bind_mk (a := g + j) (tick_mono f j g ht)
            (match t, h2 with
              | .var .., hh => ok_pair_add j hh
              | .atom .., hh => ok_pair_add j hh
              | .tag _label payload, hh =>
                  match a, hh with
                  | .lan .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨fiber, hfiber, h4⟩ =>
                          res_bind_mk (a := fiber) hfiber
                            (match res_bind_ok h4 with
                              | ⟨r, hr, h5⟩ =>
                                  res_bind_mk (a := (r.1, r.2 + j))
                                    (reduce_mono_add gasPred payload g j fiber r.1 r.2 hr)
                                    (ok_pair_add j h5))
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim
              | .«section» _entries, hh =>
                  match a, hh with
                  | .ran .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨sorted, hsorted, h4⟩ =>
                          res_bind_mk (a := sorted) hsorted
                            (match res_bind_ok h4 with
                              | ⟨fields, hfields, h5⟩ =>
                                  res_bind_mk (a := fields) hfields
                                    (match res_bind_ok h5 with
                                      | ⟨r, hr, h6⟩ =>
                                          res_bind_mk (a := (r.1, r.2 + j))
                                            (reduce_fields_mono_add
                                              (fun f2 x2 a2 => reduce gasPred f2 x2 a2) j
                                              (fun f2 x2 a2 y2 r2 h7 =>
                                                reduce_mono_add gasPred x2 f2 j a2 y2 r2 h7)
                                              fields g r.1 r.2 hr)
                                            (ok_pair_add j h6)))
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .lan .., h3 => (res_error_ne_ok h3).elim
              | .«case» scrutinee st _branches, hh =>
                  match st, hh with
                  | .lan fibers, h3 =>
                      match res_bind_ok h3 with
                      | ⟨sorted, hsorted, h4⟩ =>
                          res_bind_mk (a := sorted) hsorted
                            (match res_bind_ok h4 with
                              | ⟨head, hhead, h5⟩ =>
                                  res_bind_mk (a := (head.1, head.2 + j))
                                    (reduce_mono_add gasPred scrutinee g j (Ty.lan fibers)
                                      head.1 head.2 hhead)
                                    (match head.1, h5 with
                                      | .tag _label payload, h6 =>
                                          match res_bind_ok h6 with
                                          | ⟨body, hbody, h7⟩ =>
                                              res_bind_mk (a := body) hbody
                                                (match res_bind_ok h7 with
                                                  | ⟨opened, hopened, h8⟩ =>
                                                      res_bind_mk
                                                        (a := (opened.1, opened.2 + j))
                                                        (sub_mono_add body 0 payload head.2 j
                                                          opened.1 opened.2 hopened)
                                                        (reduce_mono_add gasPred opened.1
                                                          opened.2 j a x rest h8))
                                      | .var .., h6 =>
                                          match res_bind_ok h6 with
                                          | ⟨fields, hfields, h7⟩ =>
                                              res_bind_mk (a := fields) hfields
                                                (match res_bind_ok h7 with
                                                  | ⟨r, hr, h8⟩ =>
                                                      res_bind_mk (a := (r.1, r.2 + j))
                                                        (reduce_branches_mono_add
                                                          (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                                          j
                                                          (fun f2 x2 a2 y2 r2 h9 =>
                                                            reduce_mono_add gasPred x2 f2 j a2 y2
                                                              r2 h9)
                                                          fields head.2 a r.1 r.2 hr)
                                                        (ok_pair_add j h8))
                                      | .«case» .., h6 =>
                                          match res_bind_ok h6 with
                                          | ⟨fields, hfields, h7⟩ =>
                                              res_bind_mk (a := fields) hfields
                                                (match res_bind_ok h7 with
                                                  | ⟨r, hr, h8⟩ =>
                                                      res_bind_mk (a := (r.1, r.2 + j))
                                                        (reduce_branches_mono_add
                                                          (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                                          j
                                                          (fun f2 x2 a2 y2 r2 h9 =>
                                                            reduce_mono_add gasPred x2 f2 j a2 y2
                                                              r2 h9)
                                                          fields head.2 a r.1 r.2 hr)
                                                        (ok_pair_add j h8))
                                      | .project .., h6 =>
                                          match res_bind_ok h6 with
                                          | ⟨fields, hfields, h7⟩ =>
                                              res_bind_mk (a := fields) hfields
                                                (match res_bind_ok h7 with
                                                  | ⟨r, hr, h8⟩ =>
                                                      res_bind_mk (a := (r.1, r.2 + j))
                                                        (reduce_branches_mono_add
                                                          (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                                          j
                                                          (fun f2 x2 a2 y2 r2 h9 =>
                                                            reduce_mono_add gasPred x2 f2 j a2 y2
                                                              r2 h9)
                                                          fields head.2 a r.1 r.2 hr)
                                                        (ok_pair_add j h8))
                                      | .atom .., h6 => (res_error_ne_ok h6).elim
                                      | .«section» .., h6 => (res_error_ne_ok h6).elim))
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim
              | .project field st _label, hh =>
                  match st, hh with
                  | .ran fibers, h3 =>
                      match res_bind_ok h3 with
                      | ⟨actual, hactual, h4⟩ =>
                          res_bind_mk (a := actual) hactual
                            (ite_case
                              (P := fun (u w : Res (Term × Nat)) =>
                                u = .ok (x, rest) → w = .ok (x, rest + j))
                              (fun _hc h5 =>
                                match res_bind_ok h5 with
                                | ⟨head, hhead, h6⟩ =>
                                    res_bind_mk (a := (head.1, head.2 + j))
                                      (reduce_mono_add gasPred field g j (Ty.ran fibers)
                                        head.1 head.2 hhead)
                                      (match head.1, h6 with
                                        | .«section» .., h7 =>
                                            match res_bind_ok h7 with
                                            | ⟨found, hfound, h8⟩ =>
                                                res_bind_mk (a := found) hfound
                                                  (ok_pair_add j h8)
                                        | .var .., h7 => ok_pair_add j h7
                                        | .«case» .., h7 => ok_pair_add j h7
                                        | .project .., h7 => ok_pair_add j h7
                                        | .atom .., h7 => (res_error_ne_ok h7).elim
                                        | .tag .., h7 => (res_error_ne_ok h7).elim))
                              (fun _hc h5 => (res_error_ne_ok h5).elim) h4)
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .lan .., h3 => (res_error_ne_ok h3).elim)

/-- `budget_monotone_reduce` states row Lemma1 of the theorem inventory for `reduce`.
It states docs/metatheory.md lines 87 to 91 for lib/finite_term.ml lines 162 to 225.
The gas argument stays fixed, since the gas of decision S2-D6 is no budget.
-/
theorem budget_monotone_reduce (gas f f' : Nat) (t : Term) (a : Ty) (x : Term) (rest : Nat)
    (hle : f ≤ f') (h : reduce gas f t a = .ok (x, rest)) :
    reduce gas f' t a = .ok (x, rest + f' - f) :=
  (congrArg (fun z => reduce gas z t a) (nat_recover hle)).symm.trans
    ((reduce_mono_add gas t f (f' - f) a x rest h).trans
      (congrArg (fun z : Nat => (Except.ok (x, z) : Res (Term × Nat))) (rest_recover rest hle)))

/-- `ite_elim` reads one two way branch of a definition at one single motive.
`checkCore` at lib/finite_term.ml lines 62 to 105 tests one type equality at three arms, and each test reaches the same conclusion of docs/metatheory.md lines 92 to 96.
-/
theorem ite_elim {c : Prop} [inst : Decidable c] {α : Sort u} {a b : α} {P : α → Prop}
    (ha : c → P a) (hb : ¬ c → P b) : P (if c then a else b) :=
  match inst with
  | isTrue hc => ha hc
  | isFalse hc => hb hc

/-- `nat_shift1` moves the node unit of `size` to the right end of one sum.
Each arm of docs/metatheory.md lines 92 to 96 pays one unit for the entered node.
-/
theorem nat_shift1 (a b : Nat) : a + (1 + b) = a + b + 1 :=
  (congrArg (fun z : Nat => a + z) (Nat.add_comm 1 b)).trans (Nat.add_assoc a b 1).symm

/-- `nat_one_shift` moves one unit across one addition on the right.
It serves the case arm of docs/metatheory.md lines 92 to 96, which pays a scrutinee and a list.
-/
theorem nat_one_shift (x b : Nat) : x + 1 + b = x + b + 1 :=
  (Nat.add_assoc x 1 b).trans
    ((congrArg (fun z : Nat => x + z) (Nat.add_comm 1 b)).trans (Nat.add_assoc x b 1).symm)

/-- `nat_right_swap` exchanges the two right summands of one sum of three.
It serves the case arm of docs/metatheory.md lines 92 to 96.
-/
theorem nat_right_swap (r s b : Nat) : r + s + b = r + b + s :=
  (Nat.add_assoc r s b).trans
    ((congrArg (fun z : Nat => r + z) (Nat.add_comm s b)).trans (Nat.add_assoc r b s).symm)

/-- `nat_case_shift` is the arithmetic of the case arm of docs/metatheory.md lines 92 to 96.
`checkCore` charges one unit, then the scrutinee, then the branch list, as lib/finite_term.ml lines 96 to 102 shows.
-/
theorem nat_case_shift (r s b : Nat) : r + (1 + s + b) = r + b + s + 1 :=
  (Nat.add_assoc r (1 + s) b).symm.trans
    ((congrArg (fun z : Nat => z + b) (nat_shift1 r s)).trans
      ((nat_one_shift (r + s) b).trans (congrArg (fun z : Nat => z + 1) (nat_right_swap r s b))))

/-- `nat_pair_swap` exchanges the two summands under one addition on the right.
It serves the cons arm of the field walk of lib/finite_term.ml lines 103 to 105.
-/
theorem nat_pair_swap (r s m : Nat) : r + (s + m) = r + m + s :=
  (congrArg (fun z : Nat => r + z) (Nat.add_comm s m)).trans (Nat.add_assoc r m s).symm

/-- `nat_cancel` removes one summand of the left side through one subtraction. docs/metatheory.md lines 92 to 96 report the remaining budget as
`f - size t`.
-/
theorem nat_cancel (a b : Nat) : a + b - b = a :=
  (Nat.add_sub_assoc (Nat.le_refl b) a).trans
    ((congrArg (fun z : Nat => a + z) (Nat.sub_self b)).trans (Nat.add_zero a))

/-- `tick_close` closes one leaf arm of the cost lemma of docs/metatheory.md lines 92 to 96.
A leaf of lib/finite_term.ml lines 62 to 105 returns the budget that the tick of line 63 leaves.
-/
theorem tick_close {fuel g rest : Nat} (ht : tick fuel = .ok g)
    (hq : (Except.ok g : Res Nat) = .ok rest) : rest + 1 = fuel :=
  (congrArg (fun z : Nat => z + 1) (Except.ok.inj hq).symm).trans (tick_cost fuel g ht)

/-- `sizePairs` sums the sizes of the terms of one aligned list of `align`.
`align` at lib/finite_term.ml lines 51 to 60 pairs one fiber list with one term list.
This count is the list side of `size` of docs/metatheory.md lines 92 to 96.
-/
def sizePairs : List (String × Ty × Term) → Nat
  | [] => 0
  | (_label, _fiber, field) :: rest => size field + sizePairs rest

/-- `nat_swap` exchanges the head summand with the head of the summand on the right.
The sort of `canonical` at lib/finite_term.ml lines 20 to 23 moves one field across another one.
-/
theorem nat_swap (a b c : Nat) : a + (b + c) = b + (a + c) :=
  (Nat.add_assoc a b c).symm.trans
    ((congrArg (fun z : Nat => z + c) (Nat.add_comm a b)).trans (Nat.add_assoc b a c))

/-- `insert_size` states that one insertion of the sort keeps the total size of one entry list.
`canonical` at lib/finite_term.ml lines 20 to 23 sorts the fields of a section and of a case.
-/
theorem insert_size : ∀ (entry : String × Term) (es : List (String × Term)),
    sizeEntries (insertEntry entry es) = size entry.2 + sizeEntries es
  | (_l, _t), [] => rfl
  | (l, t), (_hl, ht) :: rest =>
      ite_elim (P := fun u : List (String × Term) =>
        sizeEntries u = size t + sizeEntries ((_hl, ht) :: rest))
        (fun _hc => rfl)
        (fun _hc =>
          (congrArg (fun z : Nat => size ht + z) (insert_size (l, t) rest)).trans
            (nat_swap (size ht) (size t) (sizeEntries rest)))

/-- `sort_size` states that the sort of `canonical` keeps the total size of one entry list.
It serves the section arm and the case arm of docs/metatheory.md lines 92 to 96, since
`checkCore` at lib/finite_term.ml lines 88 to 102 checks the sorted list.
-/
theorem sort_size : ∀ (es : List (String × Term)), sizeEntries (sortEntries es) = sizeEntries es
  | [] => rfl
  | (l, t) :: rest =>
      (insert_size (l, t) (sortEntries rest)).trans
        (congrArg (fun z : Nat => size t + z) (sort_size rest))

/-- `canonical_sorted` reads the success of `canonicalEntries` as the sort of the input.
`canonical` at lib/finite_term.ml lines 20 to 23 returns the sorted list once the labels differ.
-/
theorem canonical_sorted {α : Type} (entries sorted : List (String × α))
    (h : canonicalEntries entries = .ok sorted) : sorted = sortEntries entries :=
  match res_bind_ok h with
  | ⟨_u, _hu, hk⟩ => (Except.ok.inj hk).symm

/-- `align_cons` states the cons arm of `align` at lib/finite_term.ml lines 51 to 60.
It exposes the label comparison of line 55, so one proof can read the three orders apart.
-/
theorem align_cons (key : String) (fiber : Ty) (types : List (String × Ty)) (label : String)
    (field : Term) (terms : List (String × Term)) :
    align ((key, fiber) :: types) ((label, field) :: terms) =
      (match compare key label with
        | .lt => .error (.missingLabel key)
        | .gt => .error (.unexpectedLabel label)
        | .eq => align types terms >>= fun rest => .ok ((key, fiber, field) :: rest)) := rfl

/-- `align_size` states that `align` keeps the total size of the term list.
`align` at lib/finite_term.ml lines 51 to 60 pairs each fiber with the term of the same label.
It serves the section arm and the case arm of docs/metatheory.md lines 92 to 96.
-/
theorem align_size : ∀ (fibers : List (String × Ty)) (terms : List (String × Term))
    (pairs : List (String × Ty × Term)),
    align fibers terms = .ok pairs → sizePairs pairs = sizeEntries terms
  | [], [], _pairs, h => congrArg sizePairs (Except.ok.inj h).symm
  | (_key, _fiber) :: _types, [], _pairs, h => (res_error_ne_ok h).elim
  | [], (_label, _field) :: _terms, _pairs, h => (res_error_ne_ok h).elim
  | (key, fiber) :: types, (label, field) :: terms, _pairs, h =>
      match compare key label, (align_cons key fiber types label field terms).symm.trans h with
      | .lt, hh => (res_error_ne_ok hh).elim
      | .gt, hh => (res_error_ne_ok hh).elim
      | .eq, hh =>
          match res_bind_ok hh with
          | ⟨rest, hrest, hk⟩ =>
              (congrArg sizePairs (Except.ok.inj hk).symm).trans
                (congrArg (fun z : Nat => size field + z) (align_size types terms rest hrest))

mutual
/-- `check_core_cost` is the strong form of docs/metatheory.md lines 92 to 96 for `checkCore`.
A success at budget `fuel` leaves `rest`, and the spent amount is the size of the term.
`checkCore` mirrors lib/finite_term.ml lines 62 to 105, and the tick of line 63 pays one node.
The recursion runs on the structural gas of decision S2-D6, together with the two list partners.
-/
theorem check_core_cost : ∀ (gas : Nat) (t : Term) (fuel : Nat) (ctx : List Ty) (a : Ty)
    (rest : Nat), checkCore gas fuel ctx t a = .ok rest → rest + size t = fuel
  | 0, _t, _fuel, _ctx, _a, _rest, h => (res_error_ne_ok h).elim
  | gasPred + 1, t, fuel, ctx, a, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match t, h2 with
          | .var _index, hh =>
              match res_bind_ok hh with
              | ⟨_actual, _hact, h3⟩ =>
                  ite_elim (P := fun u : Res Nat => u = .ok rest → rest + 1 = fuel)
                    (fun _hc hq => tick_close ht hq) (fun _hc hq => (res_error_ne_ok hq).elim) h3
          | .atom _name, hh =>
              match a, hh with
              | .atoms _labels, h3 =>
                  ite_elim (P := fun u : Res Nat => u = .ok rest → rest + 1 = fuel)
                    (fun _hc hq => tick_close ht hq) (fun _hc hq => (res_error_ne_ok hq).elim) h3
              | .lan .., h3 => (res_error_ne_ok h3).elim
              | .ran .., h3 => (res_error_ne_ok h3).elim
          | .tag _label payload, hh =>
              match a, hh with
              | .lan _fibers, h3 =>
                  match res_bind_ok h3 with
                  | ⟨fiber, _hfiber, h4⟩ =>
                      (nat_shift1 rest (size payload)).trans
                        ((congrArg (fun z : Nat => z + 1)
                          (check_core_cost gasPred payload g ctx fiber rest h4)).trans
                          (tick_cost fuel g ht))
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .ran .., h3 => (res_error_ne_ok h3).elim
          | .«section» entries, hh =>
              match a, hh with
              | .ran fibers, h3 =>
                  match res_bind_ok h3 with
                  | ⟨sorted, hsorted, h4⟩ =>
                      match res_bind_ok h4 with
                      | ⟨pairs, hpairs, h5⟩ =>
                          (nat_shift1 rest (sizeEntries entries)).trans
                            ((congrArg (fun z : Nat => z + 1)
                              ((congrArg (fun z : Nat => rest + z)
                                ((align_size fibers sorted pairs hpairs).trans
                                  ((congrArg sizeEntries
                                    (canonical_sorted entries sorted hsorted)).trans
                                    (sort_size entries))).symm).trans
                                (check_fields_cost gasPred pairs g ctx rest h5))).trans
                              (tick_cost fuel g ht))
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
                          | ⟨g2, hscrut, h6⟩ =>
                              (nat_case_shift rest (size scrutinee) (sizeEntries branches)).trans
                                ((congrArg (fun z : Nat => z + 1)
                                  ((congrArg (fun z : Nat => z + size scrutinee)
                                    ((congrArg (fun z : Nat => rest + z)
                                      ((align_size fibers sorted pairs hpairs).trans
                                        ((congrArg sizeEntries
                                          (canonical_sorted branches sorted hsorted)).trans
                                          (sort_size branches))).symm).trans
                                      (check_branches_cost gasPred pairs g2 ctx a rest h6))).trans
                                    (check_core_cost gasPred scrutinee g ctx (Ty.lan fibers) g2
                                      hscrut))).trans
                                  (tick_cost fuel g ht))
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .ran .., h3 => (res_error_ne_ok h3).elim
          | .project field st _label, hh =>
              match st, hh with
              | .ran fibers, h3 =>
                  match res_bind_ok h3 with
                  | ⟨_actual, _hact, h4⟩ =>
                      ite_elim
                        (P := fun u : Res Nat => u = .ok rest → rest + (1 + size field) = fuel)
                        (fun _hc hq =>
                          (nat_shift1 rest (size field)).trans
                            ((congrArg (fun z : Nat => z + 1)
                              (check_core_cost gasPred field g ctx (Ty.ran fibers) rest hq)).trans
                              (tick_cost fuel g ht)))
                        (fun _hc hq => (res_error_ne_ok hq).elim) h4
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .lan .., h3 => (res_error_ne_ok h3).elim

/-- `check_fields_cost` is the field list statement of docs/metatheory.md lines 92 to 96.
`checkFields` replaces the higher order walk of lib/finite_term.ml lines 103 to 105.
The walk holds no charge point, so the spent amount is the sum of the sizes of the fields.
-/
theorem check_fields_cost : ∀ (gas : Nat) (pairs : List (String × Ty × Term)) (fuel : Nat)
    (ctx : List Ty) (rest : Nat),
    checkFields gas fuel ctx pairs = .ok rest → rest + sizePairs pairs = fuel
  | 0, _pairs, _fuel, _ctx, _rest, h => (res_error_ne_ok h).elim
  | _gasPred + 1, [], _fuel, _ctx, _rest, h => (Except.ok.inj h).symm
  | gasPred + 1, (_label, fiber, field) :: more, fuel, ctx, rest, h =>
      match res_bind_ok h with
      | ⟨g2, hhead, h2⟩ =>
          (nat_pair_swap rest (size field) (sizePairs more)).trans
            ((congrArg (fun z : Nat => z + size field)
              (check_fields_cost gasPred more g2 ctx rest h2)).trans
              (check_core_cost gasPred field fuel ctx fiber g2 hhead))

/-- `check_branches_cost` is the branch list statement of docs/metatheory.md lines 92 to 96.
`checkBranches` replaces the higher order walk of lib/finite_term.ml lines 103 to 105.
Each body runs at the context that the payload type extends, and that extension costs nothing.
-/
theorem check_branches_cost : ∀ (gas : Nat) (pairs : List (String × Ty × Term)) (fuel : Nat)
    (ctx : List Ty) (expected : Ty) (rest : Nat),
    checkBranches gas fuel ctx pairs expected = .ok rest → rest + sizePairs pairs = fuel
  | 0, _pairs, _fuel, _ctx, _expected, _rest, h => (res_error_ne_ok h).elim
  | _gasPred + 1, [], _fuel, _ctx, _expected, _rest, h => (Except.ok.inj h).symm
  | gasPred + 1, (_label, payloadType, body) :: more, fuel, ctx, expected, rest, h =>
      match res_bind_ok h with
      | ⟨g2, hhead, h2⟩ =>
          (nat_pair_swap rest (size body) (sizePairs more)).trans
            ((congrArg (fun z : Nat => z + size body)
              (check_branches_cost gasPred more g2 ctx expected rest h2)).trans
              (check_core_cost gasPred body fuel (payloadType :: ctx) expected g2 hhead))
end

/-- `check_cost_exact` states row Lemma2 of the theorem inventory.
It states docs/metatheory.md lines 92 to 96 for `check_term` of lib/finite_term.ml lines 62 to 105.
The gas is the one of `check` at line 108, which decision S2-D6 keeps at `2 * fuel + 2`.
The two simultaneous statements are `check_fields_cost` and `check_branches_cost` above.
-/
theorem check_cost_exact (f : Nat) (g : List Ty) (t : Term) (a : Ty) (rest : Nat)
    (h : checkCore (2 * f + 2) f g t a = .ok rest) : rest = f - size t :=
  (nat_cancel rest (size t)).symm.trans
    (congrArg (fun z : Nat => z - size t) (check_core_cost (2 * f + 2) t f g a rest h))

/-- `bind_congr_any` compares two continuations of one bind of decision S2-D3.
The two runs of one chain of lib/finite_term.ml lines 62 to 105 share the head, and the gas proof needs no fact about the value that the head returns at these steps.
-/
theorem bind_congr_any {α β : Type} {e : Res α} {k1 k2 : α → Res β} (hk : ∀ x : α, k1 x = k2 x) :
    e >>= k1 = e >>= k2 :=
  congrArg (fun k => e >>= k) (funext hk)

/-- `bind_congr_ok` compares two continuations of one bind at the value of the head.
The gas bound of decision S2-D6 reads the budget that the earlier check leaves, so the comparison of lib/finite_term.ml lines 96 to 102 needs that value.
-/
theorem bind_congr_ok {α β : Type} {e : Res α} {k1 k2 : α → Res β}
    (hk : ∀ x : α, e = .ok x → k1 x = k2 x) : e >>= k1 = e >>= k2 :=
  match e with
  | .ok x => hk x rfl
  | .error .. => rfl

/-- `bind_congr_dep` compares two binds of decision S2-D3 with an equal head.
It joins one head equality with one continuation comparison at the value of the head.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem bind_congr_dep {α β : Type} {e1 e2 : Res α} {k1 k2 : α → Res β} (he : e1 = e2)
    (hk : ∀ x : α, e2 = .ok x → k1 x = k2 x) : e1 >>= k1 = e2 >>= k2 :=
  (congrArg (fun z => z >>= k1) he).trans (bind_congr_ok hk)

/-- `ite_eq` compares two conditionals of lib/finite_term.ml at one condition.
The condition of `check_term` at lines 66 and 99 never reads the gas of decision S2-D6.
-/
theorem ite_eq {c : Prop} [inst : Decidable c] {α : Sort u} {a b x y : α} (ha : a = x)
    (hb : b = y) : (if c then a else b) = (if c then x else y) :=
  match inst with
  | isTrue .. => ha
  | isFalse .. => hb

/-- `size_pos` states that each term of lib/finite_term.ml lines 31 to 38 holds one node at least. docs/metatheory.md lines 92 to 96 charge one unit for that node.
-/
theorem size_pos : ∀ (t : Term), 1 ≤ size t
  | .var .. => Nat.le_refl 1
  | .atom .. => Nat.le_refl 1
  | .tag _l payload => Nat.le_add_right 1 (size payload)
  | .«section» fields => Nat.le_add_right 1 (sizeEntries fields)
  | .«case» s _st br =>
      Nat.le_trans (Nat.le_add_right 1 (size s)) (Nat.le_add_right (1 + size s) (sizeEntries br))
  | .project fl .. => Nat.le_add_right 1 (size fl)

/-- `cost_step` reads one successful check as a drop of the budget of one unit at least.
It joins docs/metatheory.md lines 92 to 96 with the gas bound of decision S2-D6.
-/
theorem cost_step {f2 fuel : Nat} {t : Term} (hcost : f2 + size t = fuel) : f2 + 1 ≤ fuel :=
  cast (congrArg (fun z : Nat => f2 + 1 ≤ z) hcost)
    (Nat.add_le_add (Nat.le_refl f2) (size_pos t))

/-- `gas_list` carries the gas bound of decision S2-D6 from one node to its entry list.
The list walk of lib/finite_term.ml lines 103 to 105 runs at the budget that the tick leaves.
-/
theorem gas_list {fuel fuel2 gp : Nat} (hc : fuel2 + 1 = fuel) (h : 2 * fuel + 2 ≤ gp + 1) :
    2 * fuel2 + 3 ≤ gp :=
  Nat.le_of_succ_le_succ (cast (congrArg (fun z : Nat => 2 * z + 2 ≤ gp + 1) hc.symm) h)

/-- `gas_inner` carries the gas bound of decision S2-D6 from one node to a nested node.
The nested call of lib/finite_term.ml lines 62 to 105 runs at the budget that the tick leaves.
-/
theorem gas_inner {fuel fuel2 gp : Nat} (hc : fuel2 + 1 = fuel) (h : 2 * fuel + 2 ≤ gp + 1) :
    2 * fuel2 + 2 ≤ gp :=
  Nat.le_of_succ_le (gas_list hc h)

/-- `gas_after` carries the gas bound of decision S2-D6 across one earlier check.
The earlier check spends one unit at least, as docs/metatheory.md lines 92 to 96 states.
-/
theorem gas_after {f2 fuel gp : Nat} (hstep : f2 + 1 ≤ fuel) (h : 2 * fuel + 2 ≤ gp) :
    2 * f2 + 3 ≤ gp :=
  Nat.le_trans
    (Nat.le_trans (Nat.succ_le_succ (Nat.mul_le_mul (Nat.le_refl 2) hstep))
      (Nat.le_succ (2 * fuel + 1)))
    h

mutual
/-- `check_core_gas` states row Check-gas of the theorem inventory for `checkCore`.
The structural gas of decision S2-D6 is no part of the OCaml
`check_term` of lib/finite_term.ml lines 62 to 105, so two runs above the bound of line 108 agree.
The recursion runs on the first gas, and the second gas stays free at every step.
The two bounds ride one conjunction, since each arm reads one of them alone.
-/
theorem check_core_gas : ∀ (gas : Nat) (t : Term) (gas' fuel : Nat) (ctx : List Ty) (a : Ty),
    2 * fuel + 2 ≤ gas ∧ 2 * fuel + 2 ≤ gas' →
      checkCore gas fuel ctx t a = checkCore gas' fuel ctx t a
  | 0, _t, _gas', fuel, _ctx, _a, hh => (Nat.not_succ_le_zero (2 * fuel + 1) hh.1).elim
  | _gp + 1, _t, 0, fuel, _ctx, _a, hh => (Nat.not_succ_le_zero (2 * fuel + 1) hh.2).elim
  | gp + 1, t, gp' + 1, fuel, ctx, a, hh =>
      bind_congr_ok (fun fuel2 htick =>
        match t with
        | .var .. => rfl
        | .atom .. => rfl
        | .tag _label payload =>
            match a with
            | .lan .. =>
                bind_congr_any (fun fiber =>
                  check_core_gas gp payload gp' fuel2 ctx fiber
                    ⟨gas_inner (tick_cost fuel fuel2 htick) hh.1,
                      gas_inner (tick_cost fuel fuel2 htick) hh.2⟩)
            | .atoms .. => rfl
            | .ran .. => rfl
        | .«section» .. =>
            match a with
            | .ran .. =>
                bind_congr_any (fun (_sorted : List (String × Term)) =>
                  bind_congr_any (fun pairs =>
                    check_fields_gas gp pairs gp' fuel2 ctx
                      ⟨gas_list (tick_cost fuel fuel2 htick) hh.1,
                        gas_list (tick_cost fuel fuel2 htick) hh.2⟩))
            | .atoms .. => rfl
            | .lan .. => rfl
        | .«case» scrutinee st .. =>
            match st with
            | .lan fibers =>
                bind_congr_any (fun (_sorted : List (String × Term)) =>
                  bind_congr_any (fun pairs =>
                    bind_congr_dep
                      (check_core_gas gp scrutinee gp' fuel2 ctx (Ty.lan fibers)
                        ⟨gas_inner (tick_cost fuel fuel2 htick) hh.1,
                          gas_inner (tick_cost fuel fuel2 htick) hh.2⟩)
                      (fun fuel3 hok =>
                        check_branches_gas gp pairs gp' fuel3 ctx a
                          ⟨gas_after
                            (cost_step
                              (check_core_cost gp' scrutinee fuel2 ctx (Ty.lan fibers) fuel3 hok))
                            (gas_inner (tick_cost fuel fuel2 htick) hh.1),
                            gas_after
                              (cost_step
                                (check_core_cost gp' scrutinee fuel2 ctx (Ty.lan fibers) fuel3 hok))
                              (gas_inner (tick_cost fuel fuel2 htick) hh.2)⟩)))
            | .atoms .. => rfl
            | .ran .. => rfl
        | .project field st .. =>
            match st with
            | .ran fibers =>
                bind_congr_any (fun (_actual : Ty) =>
                  ite_eq
                    (check_core_gas gp field gp' fuel2 ctx (Ty.ran fibers)
                      ⟨gas_inner (tick_cost fuel fuel2 htick) hh.1,
                        gas_inner (tick_cost fuel fuel2 htick) hh.2⟩) rfl)
            | .atoms .. => rfl
            | .lan .. => rfl)

/-- `check_fields_gas` is the field list statement of row Check-gas.
`checkFields` replaces the higher order walk of lib/finite_term.ml lines 103 to 105.
The bound holds one unit above the node bound, since the walk runs after one tick.
-/
theorem check_fields_gas : ∀ (gas : Nat) (pairs : List (String × Ty × Term)) (gas' fuel : Nat)
    (ctx : List Ty), 2 * fuel + 3 ≤ gas ∧ 2 * fuel + 3 ≤ gas' →
      checkFields gas fuel ctx pairs = checkFields gas' fuel ctx pairs
  | 0, _pairs, _gas', fuel, _ctx, hh => (Nat.not_succ_le_zero (2 * fuel + 2) hh.1).elim
  | _gp + 1, _pairs, 0, fuel, _ctx, hh => (Nat.not_succ_le_zero (2 * fuel + 2) hh.2).elim
  | gp + 1, pairs, gp' + 1, fuel, ctx, hh =>
      match pairs with
      | [] => rfl
      | (_label, fiber, field) :: more =>
          bind_congr_dep
            (check_core_gas gp field gp' fuel ctx fiber
              ⟨Nat.le_of_succ_le_succ hh.1, Nat.le_of_succ_le_succ hh.2⟩)
            (fun fuel2 hok =>
              check_fields_gas gp more gp' fuel2 ctx
                ⟨gas_after (cost_step (check_core_cost gp' field fuel ctx fiber fuel2 hok))
                  (Nat.le_of_succ_le_succ hh.1),
                  gas_after (cost_step (check_core_cost gp' field fuel ctx fiber fuel2 hok))
                    (Nat.le_of_succ_le_succ hh.2)⟩)

/-- `check_branches_gas` is the branch list statement of row Check-gas.
`checkBranches` replaces the higher order walk of lib/finite_term.ml lines 103 to 105.
Each body runs at the context that the payload type extends, and the bound reads the budget.
-/
theorem check_branches_gas : ∀ (gas : Nat) (pairs : List (String × Ty × Term)) (gas' fuel : Nat)
    (ctx : List Ty) (expected : Ty), 2 * fuel + 3 ≤ gas ∧ 2 * fuel + 3 ≤ gas' →
      checkBranches gas fuel ctx pairs expected = checkBranches gas' fuel ctx pairs expected
  | 0, _pairs, _gas', fuel, _ctx, _expected, hh => (Nat.not_succ_le_zero (2 * fuel + 2) hh.1).elim
  | _gp + 1, _pairs, 0, fuel, _ctx, _expected, hh =>
      (Nat.not_succ_le_zero (2 * fuel + 2) hh.2).elim
  | gp + 1, pairs, gp' + 1, fuel, ctx, expected, hh =>
      match pairs with
      | [] => rfl
      | (_label, payloadType, body) :: more =>
          bind_congr_dep
            (check_core_gas gp body gp' fuel (payloadType :: ctx) expected
              ⟨Nat.le_of_succ_le_succ hh.1, Nat.le_of_succ_le_succ hh.2⟩)
            (fun fuel2 hok =>
              check_branches_gas gp more gp' fuel2 ctx expected
                ⟨gas_after
                  (cost_step
                    (check_core_cost gp' body fuel (payloadType :: ctx) expected fuel2 hok))
                  (Nat.le_of_succ_le_succ hh.1),
                  gas_after
                    (cost_step
                      (check_core_cost gp' body fuel (payloadType :: ctx) expected fuel2 hok))
                    (Nat.le_of_succ_le_succ hh.2)⟩)
end

/-- `check_gas_irrelevant` states row Check-gas of the theorem inventory.
The gas of decision S2-D6 is no part of the OCaml `check_term` of lib/finite_term.ml lines 62 to 105, so two runs above the bound of line 108 return the same result.
-/
theorem check_gas_irrelevant (gas gas' fuel : Nat) (ctx : List Ty) (t : Term) (a : Ty)
    (h : 2 * fuel + 2 ≤ gas) (h' : 2 * fuel + 2 ≤ gas') :
    checkCore gas fuel ctx t a = checkCore gas' fuel ctx t a :=
  check_core_gas gas t gas' fuel ctx a ⟨h, h'⟩

/-- `ok_pair_rest` reads the budget component of one successful pair result.
Every fueled function of decision S2-D4 returns a value and the remaining budget, so the cost statements of docs/metatheory.md lines 97 to 109 read the second component of that pair.
-/
theorem ok_pair_rest {A : Type} {u x : A} {g rest : Nat}
    (h : (Except.ok (u, g) : Res (A × Nat)) = .ok (x, rest)) : g = rest :=
  congrArg (fun p : A × Nat => p.2) (Except.ok.inj h)

/-- `tick_close_pair` closes one leaf arm of the cost statements of docs/metatheory.md lines 97 to 109.
A leaf of lib/finite_term.ml lines 112 to 135 returns the budget that line 113 leaves.
-/
theorem tick_close_pair {A : Type} {u x : A} {fuel g rest : Nat} (ht : tick fuel = .ok g)
    (hq : (Except.ok (u, g) : Res (A × Nat)) = .ok (x, rest)) : rest + 1 = fuel :=
  (congrArg (fun z : Nat => z + 1) (ok_pair_rest hq)).symm.trans (tick_cost fuel g ht)

/-- `cost_node1` states the cost of one node of lib/finite_term.ml lines 112 to 135 with one child.
The node pays one unit at the tick of line 113, then it pays the cost of that child.
-/
theorem cost_node1 {A : Type} {u x : A} {f g inner rest child : Nat} (ht : tick f = .ok g)
    (hchild : inner + child = g)
    (hq : (Except.ok (u, inner) : Res (A × Nat)) = .ok (x, rest)) : rest + (1 + child) = f :=
  (nat_shift1 rest child).trans
    ((congrArg (fun z : Nat => z + 1)
      ((congrArg (fun z : Nat => z + child) (ok_pair_rest hq).symm).trans hchild)).trans
      (tick_cost f g ht))

/-- `cost_node2` states the cost of one node of lib/finite_term.ml lines 112 to 135 with two children.
The `case` node of line 125 pays one unit, then the scrutinee, then the branch list.
-/
theorem cost_node2 {A : Type} {u x : A} {f g mid inner rest c1 c2 : Nat} (ht : tick f = .ok g)
    (hfirst : mid + c1 = g) (hsecond : inner + c2 = mid)
    (hq : (Except.ok (u, inner) : Res (A × Nat)) = .ok (x, rest)) : rest + (1 + c1 + c2) = f :=
  (nat_case_shift rest c1 c2).trans
    ((congrArg (fun z : Nat => z + 1)
      ((congrArg (fun z : Nat => z + c1)
        ((congrArg (fun z : Nat => z + c2) (ok_pair_rest hq).symm).trans hsecond)).trans
        hfirst)).trans
      (tick_cost f g ht))

/-- `cost_list` states the cost of one cons arm of lib/finite_term.ml lines 130 to 135.
The walk holds no charge point, so the head and the tail pay the whole amount.
-/
theorem cost_list {A : Type} {u x : A} {f mid inner rest c1 c2 : Nat} (hfirst : mid + c1 = f)
    (hsecond : inner + c2 = mid)
    (hq : (Except.ok (u, inner) : Res (A × Nat)) = .ok (x, rest)) : rest + (c1 + c2) = f :=
  (nat_pair_swap rest c1 c2).trans
    ((congrArg (fun z : Nat => z + c1)
      ((congrArg (fun z : Nat => z + c2) (ok_pair_rest hq).symm).trans hsecond)).trans hfirst)

mutual
/-- `shift_cost` states the exact cost of `shift` of lib/finite_term.ml lines 112 to 135.
The walk pays one unit for one term node, so the whole cost is the size of the term.
Row Lemma2b of the theorem inventory reads this cost at the occurrence arm of `sub`.
-/
theorem shift_cost : ∀ (t : Term) (c d f : Nat) (x : Term) (rest : Nat),
    shift c d f t = .ok (x, rest) → rest + size t = f
  | .var _i, _c, _d, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨_g, ht, hv⟩ => tick_close_pair ht hv
  | .atom _l, _c, _d, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨_g, ht, hv⟩ => tick_close_pair ht hv
  | .tag _l p, c, d, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ => cost_node1 ht (shift_cost p c d g q.1 q.2 hq) h3
  | .«section» fields, c, d, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ => cost_node1 ht (shift_entries_cost fields c d g q.1 q.2 hq) h3
  | .«case» s _st br, c, d, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨head, hhead, h3⟩ =>
              match res_bind_ok h3 with
              | ⟨tail, htail, h4⟩ =>
                  cost_node2 ht (shift_cost s c d g head.1 head.2 hhead)
                    (shift_entries_cost br (c + 1) d head.2 tail.1 tail.2 htail) h4
  | .project fl _st _l, c, d, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ => cost_node1 ht (shift_cost fl c d g q.1 q.2 hq) h3

/-- `shift_entries_cost` is the entry list partner of `shift_cost`.
`shiftEntries` mirrors lib/finite_term.ml lines 130 to 135 and it holds no charge point.
-/
theorem shift_entries_cost : ∀ (es : List (String × Term)) (c d f : Nat)
    (ys : List (String × Term)) (rest : Nat),
    shiftEntries c d f es = .ok (ys, rest) → rest + sizeEntries es = f
  | [], _c, _d, _f, _ys, _rest, h => (ok_pair_rest h).symm
  | (_label, field) :: more, c, d, f, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              cost_list (shift_cost field c d f head.1 head.2 hhead)
                (shift_entries_cost more c d head.2 tail.1 tail.2 htail) h3
end

/-- `nat_ne_of_lt` states that a smaller index differs from the binder depth.
The variable arm of lib/finite_term.ml lines 140 to 142 splits on that order.
-/
theorem nat_ne_of_lt {a b : Nat} (h : a < b) : a ≠ b :=
  fun he => Nat.lt_irrefl a (cast (congrArg (fun z : Nat => a < z) he.symm) h)

/-- `nat_ne_of_gt` states that a larger index differs from the binder depth.
The variable arm of lib/finite_term.ml lines 140 to 142 splits on that order.
-/
theorem nat_ne_of_gt {a b : Nat} (h : b < a) : a ≠ b := fun he => nat_ne_of_lt h he.symm

/-- `nat_eq_of_not_lt` states that two indices agree once neither order holds.
The third arm of lib/finite_term.ml lines 143 to 149 replaces the variable at that index.
-/
theorem nat_eq_of_not_lt {a b : Nat} (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
  match Nat.lt_or_ge a b with
  | Or.inl hlt => (h1 hlt).elim
  | Or.inr hge =>
      match Nat.lt_or_ge b a with
      | Or.inl hlt => (h2 hlt).elim
      | Or.inr hge2 => Nat.le_antisymm hge2 hge

/-- `occ_var_ne` reads the occurrence count of one variable at another depth.
`occurrences` of decision S2-D5 counts the node `var d` at binder depth `d` alone.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem occ_var_ne {index d : Nat} (h : index ≠ d) : occurrences d (Term.var index) = 0 :=
  (if_neg h : (if index = d then (1 : Nat) else 0) = 0)

/-- `occ_var_eq` reads the occurrence count of one variable at its own depth.
`occurrences` of decision S2-D5 counts one unit at that node.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem occ_var_eq {index d : Nat} (h : index = d) : occurrences d (Term.var index) = 1 :=
  (if_pos h : (if index = d then (1 : Nat) else 0) = 1)

/-- `nat_add_mul` distributes one product over one sum of counts.
The `case` arm of `occurrences` adds two counts, and each one pays the replacement once, as lib/finite_term.ml lines 146 to 149 shows.
-/
theorem nat_add_mul (a b m : Nat) : (a + b) * m = a * m + b * m := Nat.add_mul a b m

/-- `nat_shuffle4` exchanges the two middle summands of one sum of four.
The charge of lib/finite_term.ml lines 139 to 151 joins one size with one product on each side.
-/
theorem nat_shuffle4 (p q u v : Nat) : p + q + (u + v) = p + u + (q + v) :=
  (Nat.add_assoc (p + q) u v).symm.trans
    ((congrArg (fun z : Nat => z + v) (nat_right_swap p q u)).trans (Nat.add_assoc (p + u) q v))

/-- `nat_case_charge` is the arithmetic of the `case` arm of the substitution cost.
The node pays one unit, the scrutinee and the branch list, and each side pays its occurrences.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem nat_case_charge (a1 a2 o1 o2 m : Nat) :
    1 + a1 + a2 + (o1 + o2) * m = 1 + (a1 + o1 * m) + (a2 + o2 * m) :=
  (congrArg (fun z : Nat => 1 + a1 + a2 + z) (nat_add_mul o1 o2 m)).trans
    ((nat_shuffle4 (1 + a1) a2 (o1 * m) (o2 * m)).trans
      (congrArg (fun z : Nat => z + (a2 + o2 * m)) (Nat.add_assoc 1 a1 (o1 * m))))

/-- `nat_list_charge` is the arithmetic of the cons arm of the substitution cost.
The head and the tail each pay one size and the occurrences of the replacement.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem nat_list_charge (a1 a2 o1 o2 m : Nat) :
    a1 + a2 + (o1 + o2) * m = a1 + o1 * m + (a2 + o2 * m) :=
  (congrArg (fun z : Nat => a1 + a2 + z) (nat_add_mul o1 o2 m)).trans
    (nat_shuffle4 a1 a2 (o1 * m) (o2 * m))

/-- `nat_occ_zero` drops one product at an empty occurrence count.
A node that holds no free use of the replaced index pays the replacement no unit.
This helper mirrors no line of lib/finite_term.ml and states no proposition of docs/metatheory.md.
-/
theorem nat_occ_zero (a s m : Nat) : a + (s + 0 * m) = a + s :=
  congrArg (fun z : Nat => a + (s + z)) (Nat.zero_mul m)

/-- `nat_occ_one` reads one product at a single occurrence count.
The hit arm of lib/finite_term.ml lines 146 to 149 pays the replacement once.
-/
theorem nat_occ_one (a s m : Nat) : a + (s + 1 * m) = a + (s + m) :=
  congrArg (fun z : Nat => a + (s + z)) (Nat.one_mul m)

/-- `nat_nil_charge` reads the cost of the empty entry list of lib/finite_term.ml line 131.
The empty list pays no size and no occurrence.
-/
theorem nat_nil_charge (a m : Nat) : a + (0 + 0 * m) = a :=
  congrArg (fun z : Nat => a + (0 + z)) (Nat.zero_mul m)

/-- `cost_sub_node1` states the cost of one node of lib/finite_term.ml lines 139 to 151 with one child.
The node pays one unit, then the child pays its size and its occurrences.
-/
theorem cost_sub_node1 {A : Type} {u x : A} {f g inner rest s occ m : Nat} (ht : tick f = .ok g)
    (hchild : inner + (s + occ * m) = g)
    (hq : (Except.ok (u, inner) : Res (A × Nat)) = .ok (x, rest)) :
    rest + (1 + s + occ * m) = f :=
  (congrArg (fun z : Nat => rest + z) (Nat.add_assoc 1 s (occ * m))).trans
    (cost_node1 ht hchild hq)

/-- `cost_sub_node2` states the cost of the `case` arm of lib/finite_term.ml lines 139 to 151.
The node pays one unit, the scrutinee and the branch list, and each side pays its occurrences.
-/
theorem cost_sub_node2 {A : Type} {u x : A} {f g mid inner rest a1 a2 o1 o2 m : Nat}
    (ht : tick f = .ok g) (hfirst : mid + (a1 + o1 * m) = g)
    (hsecond : inner + (a2 + o2 * m) = mid)
    (hq : (Except.ok (u, inner) : Res (A × Nat)) = .ok (x, rest)) :
    rest + (1 + a1 + a2 + (o1 + o2) * m) = f :=
  (congrArg (fun z : Nat => rest + z) (nat_case_charge a1 a2 o1 o2 m)).trans
    (cost_node2 ht hfirst hsecond hq)

/-- `cost_sub_list` states the cost of one cons arm of lib/finite_term.ml lines 130 to 135 under the replacing callback of lines 140 to 149.
-/
theorem cost_sub_list {A : Type} {u x : A} {f mid inner rest a1 a2 o1 o2 m : Nat}
    (hfirst : mid + (a1 + o1 * m) = f) (hsecond : inner + (a2 + o2 * m) = mid)
    (hq : (Except.ok (u, inner) : Res (A × Nat)) = .ok (x, rest)) :
    rest + (a1 + a2 + (o1 + o2) * m) = f :=
  (congrArg (fun z : Nat => rest + z) (nat_list_charge a1 a2 o1 o2 m)).trans
    (cost_list hfirst hsecond hq)

mutual
/-- `sub_cost` states the exact cost of `sub` of lib/finite_term.ml lines 112 to 151.
The walk pays one unit for one term node, and each free use of the replaced index pays the size of the replacement through
`shift`, as lines 146 to 149 show. docs/metatheory.md lines 97 to 101 state that amount for row
Lemma2b.
-/
theorem sub_cost : ∀ (t : Term) (d : Nat) (r : Term) (f : Nat) (x : Term) (rest : Nat),
    sub d r f t = .ok (x, rest) → rest + (size t + occurrences d t * size r) = f
  | .var index, d, r, f, x, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          ite_elim
            (P := fun w : Res (Term × Nat) =>
              w = .ok (x, rest) →
                rest + (size (Term.var index) + occurrences d (Term.var index) * size r) = f)
            (fun hlt hq =>
              ((congrArg (fun z : Nat => rest + (1 + z * size r))
                (occ_var_ne (nat_ne_of_lt hlt))).trans
                (nat_occ_zero rest 1 (size r))).trans (tick_close_pair ht hq))
            (fun hnlt =>
              ite_elim
                (P := fun w : Res (Term × Nat) =>
                  w = .ok (x, rest) →
                    rest + (size (Term.var index) + occurrences d (Term.var index) * size r) = f)
                (fun hgt hq =>
                  ((congrArg (fun z : Nat => rest + (1 + z * size r))
                    (occ_var_ne (nat_ne_of_gt hgt))).trans
                    (nat_occ_zero rest 1 (size r))).trans (tick_close_pair ht hq))
                (fun hngt hq =>
                  ((((congrArg (fun z : Nat => rest + (1 + z * size r))
                    (occ_var_eq (nat_eq_of_not_lt hnlt hngt))).trans
                    (nat_occ_one rest 1 (size r))).trans (nat_shift1 rest (size r))).trans
                    (congrArg (fun z : Nat => z + 1) (shift_cost r 0 d g x rest hq))).trans
                    (tick_cost f g ht)))
            h2
  | .atom _l, _d, r, _f, _x, rest, h =>
      match res_bind_ok h with
      | ⟨_g, ht, hv⟩ => (nat_occ_zero rest 1 (size r)).trans (tick_close_pair ht hv)
  | .tag _l p, d, r, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ => cost_sub_node1 ht (sub_cost p d r g q.1 q.2 hq) h3
  | .«section» fields, d, r, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ => cost_sub_node1 ht (sub_entries_cost fields d r g q.1 q.2 hq) h3
  | .«case» s _st br, d, r, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨head, hhead, h3⟩ =>
              match res_bind_ok h3 with
              | ⟨tail, htail, h4⟩ =>
                  cost_sub_node2 ht (sub_cost s d r g head.1 head.2 hhead)
                    (sub_entries_cost br (d + 1) r head.2 tail.1 tail.2 htail) h4
  | .project fl _st _l, d, r, _f, _x, _rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨q, hq, h3⟩ => cost_sub_node1 ht (sub_cost fl d r g q.1 q.2 hq) h3

/-- `sub_entries_cost` is the entry list partner of `sub_cost`.
`subEntries` mirrors lib/finite_term.ml lines 130 to 135 and it holds no charge point.
The depth reaches each entry unchanged, as `occurrencesEntries` of decision S2-D5 does.
-/
theorem sub_entries_cost : ∀ (es : List (String × Term)) (d : Nat) (r : Term) (f : Nat)
    (ys : List (String × Term)) (rest : Nat),
    subEntries d r f es = .ok (ys, rest) →
      rest + (sizeEntries es + occurrencesEntries d es * size r) = f
  | [], _d, r, _f, _ys, rest, h => (nat_nil_charge rest (size r)).trans (ok_pair_rest h).symm
  | (_label, field) :: more, d, r, f, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              cost_sub_list (sub_cost field d r f head.1 head.2 hhead)
                (sub_entries_cost more d r head.2 tail.1 tail.2 htail) h3
end

/-- `tick_succ` runs `tick` of lib/finite_term.ml line 47 at a budget above zero.
The entered node of docs/metatheory.md lines 97 and 98 pays that one unit.
-/
theorem tick_succ (f : Nat) : tick (f + 1) = .ok f := rfl

/-- `reduce_step_charge` states row Lemma2b of the theorem inventory.
It states docs/metatheory.md lines 97 to 109 for the case of a tag at lib/finite_term.ml lines 187 to 190.
The first part is the step equation, which exhibits the one unit that the entered node pays at the tick of line 163 and the gas unit that decision
S2-D6 spends. The second part is the charge equation, and it reads the exact cost of `substitute_core` of lines 139 to 151, which is the size of the body plus one size of the payload for each free use of index zero in that body.
The reduction of the substituted body follows the two parts, so `reduce` may charge one input node more than once, and the bound of row
Lemma2 stops here.
-/
theorem reduce_step_charge (gas fuel : Nat) (scrutinee : Term) (fibers : List (String × Ty))
    (branches sorted : List (String × Term)) (expected : Ty) (label : String)
    (payload body opened final : Term) (afterHead afterSub rest : Nat)
    (hscrut : reduce gas fuel scrutinee (Ty.lan fibers) = .ok (Term.tag label payload, afterHead))
    (hsorted : canonicalEntries branches = .ok sorted)
    (hbody : lookup label sorted = .ok body)
    (hsub : substituteCore afterHead payload body = .ok (opened, afterSub))
    (hrun : reduce gas afterSub opened expected = .ok (final, rest)) :
    reduce (gas + 1) (fuel + 1) (Term.«case» scrutinee (Ty.lan fibers) branches) expected
        = .ok (final, rest)
      ∧ afterSub + (size body + occurrences 0 body * size payload) = afterHead :=
  ⟨res_bind_mk (a := fuel) (tick_succ fuel)
      (res_bind_mk (a := sorted) hsorted
        (res_bind_mk (a := (Term.tag label payload, afterHead)) hscrut
          (res_bind_mk (a := body) hbody
            (res_bind_mk (a := (opened, afterSub)) hsub hrun)))),
    sub_cost body 0 payload afterHead opened afterSub hsub⟩
