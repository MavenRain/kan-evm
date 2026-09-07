import KanEvmProofs.Reduce
import KanEvmProofs.Budget
import KanEvmProofs.Canonical

/-! # Normalizer core of the finite fragment

This module states rows Theorem6-gas, Theorem6-11.1, Theorem6-11.2, Theorem6-11.4 and Theorem6-C6 of the theorem inventory.
It reads `reduce` at lib/finite_term.ml lines 162 to 225 and `normalize` at lines 227 to 229.
It states docs/metatheory.md lines 292 to 320 and lines 358 to 367.
Only `tick` ends a run of `reduce`, since the gas guard of decision S2-D6 cannot fire below `f + 1` gas.
Every proof of this module runs in term mode, so the module holds no tactic block.
-/

universe u

/-- `pair_rest_le` bounds the budget component of one successful pair result.
Every fueled function of decision S2-D4 returns a value and the remaining budget, so each budget bound of docs/metatheory.md lines 87 to 91 reads that second component.
-/
theorem pair_rest_le {A : Type} {u x : A} {g rest bound : Nat} (hb : g ≤ bound)
    (h : (Except.ok (u, g) : Res (A × Nat)) = .ok (x, rest)) : rest ≤ bound :=
  Nat.le_trans (Nat.le_of_eq (ok_pair_rest h).symm) hb

/-- `pair_value_eq` reads the value component of one successful pair result.
The normal form statement of docs/metatheory.md lines 358 to 367 reads that first component.
-/
theorem pair_value_eq {A : Type} {u x : A} {g rest : Nat}
    (h : (Except.ok (u, g) : Res (A × Nat)) = .ok (x, rest)) : u = x :=
  congrArg (fun p : A × Nat => p.1) (Except.ok.inj h)

/-- `cond_elim` reads one two way choice over a Bool at one motive.
`List.lookup` under `lookup` of lib/finite_term.ml lines 40 and 41 chooses on one label test, and both choices reach the same conclusion of docs/metatheory.md lines 358 to 367.
-/
theorem cond_elim {c : Bool} {α : Sort u} {x y : α} {P : α → Prop} (ht : P x) (hf : P y) :
    P (cond c x y) :=
  Bool.casesOn (motive := fun z => P (cond z x y)) c hf ht

/-- `sub_rest_le` states that one substitution never raises the budget it entered with.
`sub` mirrors lib/finite_term.ml lines 112 to 151, and row
Lemma2b of the inventory states its exact cost at docs/metatheory.md lines 97 to 101.
-/
theorem sub_rest_le (d : Nat) (r : Term) (f : Nat) (t x : Term) (rest : Nat)
    (h : sub d r f t = .ok (x, rest)) : rest ≤ f :=
  Nat.le.intro (sub_cost t d r f x rest h)

/-- `reduce_fields_rest_le` bounds the budget of one field walk of the reducer.
`reduceFields` mirrors lib/finite_term.ml lines 211 to 216 and it holds no charge point, so a step that never raises the budget leaves the whole walk under the budget it entered with. docs/metatheory.md lines 92 to 96 state that the walk pays for its parts alone.
-/
theorem reduce_fields_rest_le (step : Nat → Term → Ty → Res (Term × Nat))
    (hstep : ∀ (u : Nat) (x : Term) (b : Ty) (y : Term) (r : Nat),
      step u x b = .ok (y, r) → r ≤ u) :
    ∀ (fields : List (String × Ty × Term)) (f : Nat) (ys : List (String × Term)) (rest : Nat),
      reduceFields step f fields = .ok (ys, rest) → rest ≤ f
  | [], _f, _ys, _rest, h => Nat.le_of_eq (ok_pair_rest h).symm
  | (_label, fiber, field) :: more, f, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              Nat.le_trans (pair_rest_le (Nat.le_refl tail.2) h3)
                (Nat.le_trans
                  (reduce_fields_rest_le step hstep more head.2 tail.1 tail.2 htail)
                  (hstep f field fiber head.1 head.2 hhead))

/-- `reduce_branches_rest_le` bounds the budget of one branch walk of the reducer.
`reduceBranches` mirrors lib/finite_term.ml lines 219 to 225 and it holds no charge point, so a step that never raises the budget leaves the whole walk under the budget it entered with. docs/metatheory.md lines 92 to 96 state that the walk pays for its parts alone.
-/
theorem reduce_branches_rest_le (step : Nat → Term → Ty → Res (Term × Nat))
    (hstep : ∀ (u : Nat) (x : Term) (b : Ty) (y : Term) (r : Nat),
      step u x b = .ok (y, r) → r ≤ u) :
    ∀ (fields : List (String × Ty × Term)) (f : Nat) (expected : Ty)
      (ys : List (String × Term)) (rest : Nat),
      reduceBranches step f fields expected = .ok (ys, rest) → rest ≤ f
  | [], _f, _expected, _ys, _rest, h => Nat.le_of_eq (ok_pair_rest h).symm
  | (_label, _fiber, body) :: more, f, expected, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              Nat.le_trans (pair_rest_le (Nat.le_refl tail.2) h3)
                (Nat.le_trans
                  (reduce_branches_rest_le step hstep more head.2 expected tail.1 tail.2 htail)
                  (hstep f body expected head.1 head.2 hhead))
/-- `reduce_rest_lt` states that one reduction spends the budget of the node it enters.
`reduce` mirrors lib/finite_term.ml lines 162 to 225 and it ticks at line 163 ahead of every nested call, so the budget it returns sits under the budget it entered with. docs/metatheory.md lines 92 to 96 state that bound for the checker, and lines 97 to 109 state the charges of one reduction step.
-/
theorem reduce_rest_lt : ∀ (gas : Nat) (t : Term) (f : Nat) (a : Ty) (x : Term) (rest : Nat),
    reduce gas f t a = .ok (x, rest) → rest < f
  | 0, _t, _f, _a, _x, _rest, h => (res_error_ne_ok h).elim
  | gasPred + 1, t, f, a, x, rest, h =>
      match res_bind_ok h with
      | ⟨g, ht, h2⟩ =>
          Nat.lt_of_le_of_lt
            (match t, h2 with
              | .var .., hh => pair_rest_le (Nat.le_refl g) hh
              | .atom .., hh => pair_rest_le (Nat.le_refl g) hh
              | .tag (payload := payload) .., hh =>
                  match a, hh with
                  | .lan .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨fiber, _hfiber, h4⟩ =>
                          match res_bind_ok h4 with
                          | ⟨r, hr, h5⟩ =>
                              pair_rest_le
                                (Nat.le_of_lt (reduce_rest_lt gasPred payload g fiber r.1 r.2 hr))
                                h5
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim
              | .«section» .., hh =>
                  match a, hh with
                  | .ran .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨_sorted, _hsorted, h4⟩ =>
                          match res_bind_ok h4 with
                          | ⟨fields, _hfields, h5⟩ =>
                              match res_bind_ok h5 with
                              | ⟨r, hr, h6⟩ =>
                                  pair_rest_le
                                    (reduce_fields_rest_le
                                      (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                      (fun u2 x2 b2 y2 r2 h7 =>
                                        Nat.le_of_lt (reduce_rest_lt gasPred x2 u2 b2 y2 r2 h7))
                                      fields g r.1 r.2 hr)
                                    h6
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .lan .., h3 => (res_error_ne_ok h3).elim
              | .«case» (scrutinee := scrutinee) (scrutineeType := st) .., hh =>
                  match st, hh with
                  | .lan .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨_sorted, _hsorted, h4⟩ =>
                          match res_bind_ok h4 with
                          | ⟨head, hhead, h5⟩ =>
                              match head.1, h5 with
                              | .tag (payload := payload) .., h6 =>
                                  match res_bind_ok h6 with
                                  | ⟨body, _hbody, h7⟩ =>
                                      match res_bind_ok h7 with
                                      | ⟨opened, hopened, h8⟩ =>
                                          Nat.le_trans
                                            (Nat.le_of_lt
                                              (reduce_rest_lt gasPred opened.1 opened.2 a x rest
                                                h8))
                                            (Nat.le_trans
                                              (sub_rest_le 0 payload head.2 body opened.1 opened.2
                                                hopened)
                                              (Nat.le_of_lt
                                                (reduce_rest_lt gasPred scrutinee g _ head.1 head.2
                                                  hhead)))
                              | .var .., h6 =>
                                  match res_bind_ok h6 with
                                  | ⟨fields, _hfields, h7⟩ =>
                                      match res_bind_ok h7 with
                                      | ⟨r, hr, h8⟩ =>
                                          pair_rest_le
                                            (Nat.le_trans
                                              (reduce_branches_rest_le
                                                (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                                (fun u2 x2 b2 y2 r2 h9 =>
                                                  Nat.le_of_lt
                                                    (reduce_rest_lt gasPred x2 u2 b2 y2 r2 h9))
                                                fields head.2 a r.1 r.2 hr)
                                              (Nat.le_of_lt
                                                (reduce_rest_lt gasPred scrutinee g _ head.1 head.2
                                                  hhead)))
                                            h8
                              | .«case» .., h6 =>
                                  match res_bind_ok h6 with
                                  | ⟨fields, _hfields, h7⟩ =>
                                      match res_bind_ok h7 with
                                      | ⟨r, hr, h8⟩ =>
                                          pair_rest_le
                                            (Nat.le_trans
                                              (reduce_branches_rest_le
                                                (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                                (fun u2 x2 b2 y2 r2 h9 =>
                                                  Nat.le_of_lt
                                                    (reduce_rest_lt gasPred x2 u2 b2 y2 r2 h9))
                                                fields head.2 a r.1 r.2 hr)
                                              (Nat.le_of_lt
                                                (reduce_rest_lt gasPred scrutinee g _ head.1 head.2
                                                  hhead)))
                                            h8
                              | .project .., h6 =>
                                  match res_bind_ok h6 with
                                  | ⟨fields, _hfields, h7⟩ =>
                                      match res_bind_ok h7 with
                                      | ⟨r, hr, h8⟩ =>
                                          pair_rest_le
                                            (Nat.le_trans
                                              (reduce_branches_rest_le
                                                (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                                (fun u2 x2 b2 y2 r2 h9 =>
                                                  Nat.le_of_lt
                                                    (reduce_rest_lt gasPred x2 u2 b2 y2 r2 h9))
                                                fields head.2 a r.1 r.2 hr)
                                              (Nat.le_of_lt
                                                (reduce_rest_lt gasPred scrutinee g _ head.1 head.2
                                                  hhead)))
                                            h8
                              | .atom .., h6 => (res_error_ne_ok h6).elim
                              | .«section» .., h6 => (res_error_ne_ok h6).elim
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .ran .., h3 => (res_error_ne_ok h3).elim
              | .project («section» := field) (sectionType := sty) .., hh =>
                  match sty, hh with
                  | .ran .., h3 =>
                      match res_bind_ok h3 with
                      | ⟨_actual, _hactual, h4⟩ =>
                          ite_elim
                            (P := fun w : Res (Term × Nat) => w = .ok (x, rest) → rest ≤ g)
                            (fun _hc h5 =>
                              match res_bind_ok h5 with
                              | ⟨head, hhead, h6⟩ =>
                                  match head.1, h6 with
                                  | .«section» .., h7 =>
                                      match res_bind_ok h7 with
                                      | ⟨_found, _hfound, h8⟩ =>
                                          pair_rest_le
                                            (Nat.le_of_lt
                                              (reduce_rest_lt gasPred field g _ head.1 head.2
                                                hhead))
                                            h8
                                  | .var .., h7 =>
                                      pair_rest_le
                                        (Nat.le_of_lt
                                          (reduce_rest_lt gasPred field g _ head.1 head.2 hhead))
                                        h7
                                  | .«case» .., h7 =>
                                      pair_rest_le
                                        (Nat.le_of_lt
                                          (reduce_rest_lt gasPred field g _ head.1 head.2 hhead))
                                        h7
                                  | .project .., h7 =>
                                      pair_rest_le
                                        (Nat.le_of_lt
                                          (reduce_rest_lt gasPred field g _ head.1 head.2 hhead))
                                        h7
                                  | .atom .., h7 => (res_error_ne_ok h7).elim
                                  | .tag .., h7 => (res_error_ne_ok h7).elim)
                            (fun _hc h5 => (res_error_ne_ok h5).elim) h4
                  | .atoms .., h3 => (res_error_ne_ok h3).elim
                  | .lan .., h3 => (res_error_ne_ok h3).elim)
            (Nat.lt_of_lt_of_eq (Nat.lt_succ_self g) (tick_cost f g ht))
/-- `drop_arg` keeps a bound name in sight when the proof of one arm needs no part of it.
The walks of lib/finite_term.ml lines 211 to 225 bind a head value at each element, and a proof of one equality of two walks needs the name and not the value. docs/metatheory.md lines 97 to 109 record those walks.
-/
theorem drop_arg {α : Sort u} {Q : Prop} (_x : α) (q : Q) : Q := q

/-- `bind_congr_head` compares two binds that share one continuation.
The nodes of lib/finite_term.ml lines 162 to 225 end in a common return, so a proof of one equality of two runs closes at the head of the bind. docs/metatheory.md lines 97 to 109 record that shape.
-/
theorem bind_congr_head {α β : Type} {e1 e2 : Res α} {k : α → Res β} (he : e1 = e2) :
    e1 >>= k = e2 >>= k :=
  congrArg (fun z => z >>= k) he

/-- `reduce_fields_congr` states that two steps that agree under one bound drive the same walk.
`reduceFields` of lib/finite_term.ml lines 211 to 216 threads one budget, and each element enters at the budget the element ahead of it returned, so one bound covers the whole list. docs/metatheory.md lines 97 to 109 record that threading.
-/
theorem reduce_fields_congr (s1 s2 : Nat → Term → Ty → Res (Term × Nat)) (bound : Nat)
    (hagree : ∀ (u : Nat) (x : Term) (b : Ty), u ≤ bound → s1 u x b = s2 u x b)
    (hle : ∀ (u : Nat) (x : Term) (b : Ty) (y : Term) (r : Nat), s1 u x b = .ok (y, r) → r ≤ u) :
    ∀ (fields : List (String × Ty × Term)) (f : Nat), f ≤ bound →
      reduceFields s1 f fields = reduceFields s2 f fields
  | [], _f, hf => drop_arg hf rfl
  | (_label, fiber, field) :: more, f, hf =>
      bind_congr_dep (hagree f field fiber hf) (fun head hhead =>
        bind_congr_head
          (reduce_fields_congr s1 s2 bound hagree hle more head.2
            (Nat.le_trans
              (hle f field fiber head.1 head.2 ((hagree f field fiber hf).trans hhead)) hf)))

/-- `reduce_branches_congr` states the same agreement for the branch walk.
`reduceBranches` of lib/finite_term.ml lines 219 to 225 threads one budget through the bodies and each body reduces at the expected type of the whole node, as line 223 shows. docs/metatheory.md lines 97 to 109 record that threading.
-/
theorem reduce_branches_congr (s1 s2 : Nat → Term → Ty → Res (Term × Nat)) (bound : Nat)
    (hagree : ∀ (u : Nat) (x : Term) (b : Ty), u ≤ bound → s1 u x b = s2 u x b)
    (hle : ∀ (u : Nat) (x : Term) (b : Ty) (y : Term) (r : Nat), s1 u x b = .ok (y, r) → r ≤ u) :
    ∀ (fields : List (String × Ty × Term)) (f : Nat) (expected : Ty), f ≤ bound →
      reduceBranches s1 f fields expected = reduceBranches s2 f fields expected
  | [], _f, _expected, hf => drop_arg hf rfl
  | (_label, _fiber, body) :: more, f, expected, hf =>
      bind_congr_dep (hagree f body expected hf) (fun head hhead =>
        bind_congr_head
          (reduce_branches_congr s1 s2 bound hagree hle more head.2 expected
            (Nat.le_trans
              (hle f body expected head.1 head.2 ((hagree f body expected hf).trans hhead)) hf)))

/-- `nat_pos_cases` names the predecessor of a gas that stands above one fuel.
Decision S2-D6 puts a gas parameter ahead of the fuel of lib/finite_term.ml line 162, and every statement of this module holds the gas above the fuel, so the gas is never zero.
The gas parameter states no proposition of docs/metatheory.md, and it pays for decision S2-D6.
-/
theorem nat_pos_cases {f : Nat} {P : Nat → Prop}
    (k : ∀ gp : Nat, f < gp + 1 → P (gp + 1)) : ∀ (gas : Nat), f < gas → P gas
  | 0, h => (Nat.not_lt_zero f h).elim
  | gp + 1, h => k gp h

/-- `reduce_gas_step` is one step of the strong induction on the fuel of decision S2-D6.
It compares one entered node of lib/finite_term.ml lines 162 to 225 at two gas values.
The tick of line 163 leaves a smaller fuel for every nested call, so the hypothesis `ih` covers each of them, and docs/metatheory.md lines 97 to 109 state the charges that make it smaller.
-/
theorem reduce_gas_step (f : Nat)
    (ih : ∀ (m : Nat), m < f → ∀ (gas gas' : Nat) (t : Term) (a : Ty), m < gas → m < gas' →
      reduce gas m t a = reduce gas' m t a)
    (gas gas' : Nat) (t : Term) (a : Ty) (h1 : f < gas) (h2 : f < gas') :
    reduce gas f t a = reduce gas' f t a :=
  nat_pos_cases (P := fun z => reduce z f t a = reduce gas' f t a)
    (fun gp hgp =>
      nat_pos_cases (P := fun z => reduce (gp + 1) f t a = reduce z f t a)
        (fun gp' hgp' =>
          match f, ih, hgp, hgp' with
          | 0, _ih, _ha, hb => drop_arg hb rfl
          | fp + 1, ih2, ha, hb =>
              let hg1 : fp < gp := Nat.lt_of_succ_lt_succ ha
              let hg2 : fp < gp' := Nat.lt_of_succ_lt_succ hb
              let hagree : ∀ (u : Nat) (x : Term) (b : Ty), u ≤ fp →
                  reduce gp u x b = reduce gp' u x b :=
                fun u x b hu =>
                  ih2 u (Nat.lt_succ_of_le hu) gp gp' x b (Nat.lt_of_le_of_lt hu hg1)
                    (Nat.lt_of_le_of_lt hu hg2)
              let hle : ∀ (u : Nat) (x : Term) (b : Ty) (y : Term) (r : Nat),
                  reduce gp u x b = .ok (y, r) → r ≤ u :=
                fun u x b y r hr => Nat.le_of_lt (reduce_rest_lt gp x u b y r hr)
              match t with
              | .var .. => rfl
              | .atom .. => rfl
              | .tag label payload =>
                  match a with
                  | .lan fibers =>
                      bind_congr_any (e := lookup label fibers) (fun fiber =>
                        bind_congr_head (hagree fp payload fiber (Nat.le_refl fp)))
                  | .atoms .. => rfl
                  | .ran .. => rfl
              | .«section» entries =>
                  match a with
                  | .ran fibers =>
                      bind_congr_any (e := canonicalEntries entries) (fun sorted =>
                        bind_congr_any (e := align fibers sorted) (fun fields =>
                          bind_congr_head
                            (reduce_fields_congr (fun u x b => reduce gp u x b)
                              (fun u x b => reduce gp' u x b) fp hagree hle fields fp
                              (Nat.le_refl fp))))
                  | .atoms .. => rfl
                  | .lan .. => rfl
              | .«case» scrutinee scrutineeType branches =>
                  match scrutineeType with
                  | .lan .. =>
                      bind_congr_any (e := canonicalEntries branches) (fun sorted =>
                        drop_arg sorted
                          (bind_congr_dep (hagree fp scrutinee _ (Nat.le_refl fp))
                            (fun head hhead =>
                              let hb2 : head.2 ≤ fp :=
                                Nat.le_of_lt
                                  (reduce_rest_lt gp' scrutinee fp _ head.1 head.2 hhead)
                              match head.1 with
                              | .tag (payload := payload) .. =>
                                  bind_congr_any (fun body =>
                                    bind_congr_ok (fun opened hopened =>
                                      hagree opened.2 opened.1 a
                                        (Nat.le_trans
                                          (sub_rest_le 0 payload head.2 body opened.1 opened.2
                                            hopened)
                                          hb2)))
                              | .var .. =>
                                  bind_congr_any (fun fields =>
                                    bind_congr_head
                                      (reduce_branches_congr (fun u x b => reduce gp u x b)
                                        (fun u x b => reduce gp' u x b) fp hagree hle fields
                                        head.2 a hb2))
                              | .«case» .. =>
                                  bind_congr_any (fun fields =>
                                    bind_congr_head
                                      (reduce_branches_congr (fun u x b => reduce gp u x b)
                                        (fun u x b => reduce gp' u x b) fp hagree hle fields
                                        head.2 a hb2))
                              | .project .. =>
                                  bind_congr_any (fun fields =>
                                    bind_congr_head
                                      (reduce_branches_congr (fun u x b => reduce gp u x b)
                                        (fun u x b => reduce gp' u x b) fp hagree hle fields
                                        head.2 a hb2))
                              | .atom .. => rfl
                              | .«section» .. => rfl)))
                  | .atoms .. => rfl
                  | .ran .. => rfl
              | .project field sectionType label =>
                  match sectionType with
                  | .ran fibers =>
                      bind_congr_any (e := lookup label fibers) (fun actual =>
                        drop_arg actual
                          (ite_eq
                            (bind_congr_dep (hagree fp field _ (Nat.le_refl fp))
                              (fun head hhead =>
                                drop_arg hhead
                                  (match head.1 with
                                    | .«section» .. => rfl
                                    | .var .. => rfl
                                    | .«case» .. => rfl
                                    | .project .. => rfl
                                    | .atom .. => rfl
                                    | .tag .. => rfl))) rfl))
                  | .atoms .. => rfl
                  | .lan .. => rfl)
        gas' h2)
    gas h1
/-- `reduce_gas_irrelevant` states that the gas parameter of decision S2-D6 is never observable.
The OCaml `reduce` at lib/finite_term.ml lines 162 to 225 carries no gas, and this statement is the reason the mechanization may carry one.
Two gas values above the fuel give one result. `reduceFields` and `reduceBranches` at lines 211 to 225 pass the gas unchanged, so
`f < gas` is the whole hypothesis. The gas parameter states no proposition of docs/metatheory.md, and it pays for decision
S2-D6.
-/
theorem reduce_gas_irrelevant (gas gas' f : Nat) (t : Term) (a : Ty) (h1 : f < gas)
    (h2 : f < gas') : reduce gas f t a = reduce gas' f t a :=
  Nat.strongRecOn
    (motive := fun m => ∀ (gas1 gas2 : Nat) (x : Term) (b : Ty), m < gas1 → m < gas2 →
      reduce gas1 m x b = reduce gas2 m x b)
    f (fun m ih => reduce_gas_step m ih) gas gas' t a h1 h2

/-- `reduce_gas_unused` states the normal form of that reading, at the gas `normalize` picks.
Line 229 of lib/finite_term.ml runs one reduction at the budget the check leaves, and the mechanization runs it at one unit above that budget, per decision
S2-D6. The gas parameter states no proposition of docs/metatheory.md, and it pays for decision S2-D6.
-/
theorem reduce_gas_unused (gas f : Nat) (t : Term) (a : Ty) (h : f < gas) :
    reduce gas f t a = reduce (f + 1) f t a :=
  reduce_gas_irrelevant gas (f + 1) f t a h (Nat.lt_succ_self f)

/-- `reduce_fuel_irrelevant` states that a larger fuel changes no result and only the rest.
The OCaml `reduce` at lib/finite_term.ml lines 162 to 225 charges one unit per entered node and line 163 is the one charge point, so a run at a larger fuel returns the same term and the extra budget on top of the rest. docs/metatheory.md lines 97 to 109 state those charges.
-/
theorem reduce_fuel_irrelevant (gas gas' f f' : Nat) (t : Term) (a : Ty) (t' : Term) (r : Nat)
    (_hcanon : Ty.Canonical a) (h1 : f < gas) (h2 : f' < gas') (hle : f ≤ f')
    (h : reduce gas f t a = .ok (t', r)) : reduce gas' f' t a = .ok (t', r + f' - f) :=
  (reduce_gas_irrelevant gas' (f' + 1) f' t a h2 (Nat.lt_succ_self f')).trans
    (budget_monotone_reduce (f' + 1) f f' t a t' r hle
      ((reduce_gas_irrelevant (f' + 1) gas f t a (Nat.lt_succ_of_le hle) h1).trans h))

/-- `normalize_is_check_then_reduce` states that `normalize` is one check ahead of one reduction.
It mirrors the OCaml `normalize` at lib/finite_term.ml lines 227 to 229, where line 228 checks and line 229 reduces, and it holds through
`rfl` on the assignment line. The reduction never rechecks its own output, so the preservation statement of the check is the one well typedness argument. docs/metatheory.md lines 354 to 356 hold claim
C6.
-/
theorem normalize_is_check_then_reduce (f : Nat) (dd : List Ty) (t : Term) (a : Ty) :
    normalize f dd t a =
      checkCore (2 * f + 2) f dd t a >>= fun rest =>
        reduce (rest + 1) rest t a >>= fun result => .ok result.1 := rfl
/-- `NoTag` holds of a term that is no `tag` node.
The comment at lib/finite_term.ml lines 158 to 161 states that a `case` of a
`tag` is the one redex of the `lan` side, so a scrutinee that is no
`tag` is a normal scrutinee. docs/metatheory.md lines 358 to 370 record that reading.
-/
def NoTag : Term → Prop
  | .var .. => True
  | .atom .. => True
  | .tag .. => False
  | .«section» .. => True
  | .«case» .. => True
  | .project .. => True

/-- `NoSection` holds of a term that is no `section` node.
Lines 198 to 210 of lib/finite_term.ml project out of a `section`, so a projected term that is no
`section` is a normal projection. docs/metatheory.md lines 358 to 370 record that reading.
-/
def NoSection : Term → Prop
  | .var .. => True
  | .atom .. => True
  | .tag .. => True
  | .«section» .. => False
  | .«case» .. => True
  | .project .. => True

mutual

/-- `NormalForm` holds of a term that carries no redex of lib/finite_term.ml lines 162 to 225.
A `case` of a `tag` scrutinee reduces at lines 187 to 190 and a `project` of a
`section` reduces at lines 198 to 210, so a normal term holds neither.
Every subterm of a normal term is normal. docs/metatheory.md lines 358 to 370 record that reading.
-/
inductive NormalForm : Term → Prop where
  | var (index : Nat) : NormalForm (.var index)
  | atom (label : String) : NormalForm (.atom label)
  | tag (label : String) (payload : Term) : NormalForm payload → NormalForm (.tag label payload)
  | «section» (entries : List (String × Term)) :
      NormalFormEntries entries → NormalForm (.«section» entries)
  | «case» (scrutinee : Term) (scrutineeType : Ty) (branches : List (String × Term)) :
      NoTag scrutinee → NormalForm scrutinee → NormalFormEntries branches →
        NormalForm (.«case» scrutinee scrutineeType branches)
  | project (field : Term) (sectionType : Ty) (label : String) :
      NoSection field → NormalForm field → NormalForm (.project field sectionType label)

/-- `NormalFormEntries` holds of an entry list whose values are all normal.
The walks of lib/finite_term.ml lines 211 to 225 return one entry list, and every value of that list is the result of one reduction. docs/metatheory.md lines 358 to 370 record that reading.
-/
inductive NormalFormEntries : List (String × Term) → Prop where
  | nil : NormalFormEntries []
  | cons (label : String) (value : Term) (more : List (String × Term)) :
      NormalForm value → NormalFormEntries more → NormalFormEntries ((label, value) :: more)

end

/-- `normal_transport` moves a normal form across the equation of one returned pair.
The nodes of lib/finite_term.ml lines 162 to 225 return a term and a budget in one pair, and the statement of the caller names the parts of that pair. docs/metatheory.md lines 358 to 370 record that shape.
-/
theorem normal_transport {u x : Term} {g rest : Nat}
    (h : (Except.ok (u, g) : Res (Term × Nat)) = .ok (x, rest)) (p : NormalForm u) :
    NormalForm x :=
  pair_value_eq h ▸ p

/-- `normal_entries_transport` moves a normal entry list across the equation of one returned pair.
The walks of lib/finite_term.ml lines 211 to 225 return an entry list and a budget in one pair. docs/metatheory.md lines 358 to 370 record that shape.
-/
theorem normal_entries_transport {u x : List (String × Term)} {g rest : Nat}
    (h : (Except.ok (u, g) : Res (List (String × Term) × Nat)) = .ok (x, rest))
    (p : NormalFormEntries u) : NormalFormEntries x :=
  pair_value_eq h ▸ p

/-- `reduce_fields_normal` states that the field walk returns normal values.
`reduceFields` of lib/finite_term.ml lines 211 to 216 keeps the label of each element and it replaces the value with the result of one step. docs/metatheory.md lines 358 to 370 record that.
-/
theorem reduce_fields_normal (step : Nat → Term → Ty → Res (Term × Nat))
    (hstep : ∀ (u : Nat) (x : Term) (b : Ty) (y : Term) (r : Nat),
      step u x b = .ok (y, r) → NormalForm y) :
    ∀ (fields : List (String × Ty × Term)) (f : Nat) (ys : List (String × Term)) (rest : Nat),
      reduceFields step f fields = .ok (ys, rest) → NormalFormEntries ys
  | [], _f, _ys, _rest, h => normal_entries_transport h NormalFormEntries.nil
  | (_label, fiber, field) :: more, f, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              normal_entries_transport h3
                (NormalFormEntries.cons _ head.1 tail.1
                  (hstep f field fiber head.1 head.2 hhead)
                  (reduce_fields_normal step hstep more head.2 tail.1 tail.2 htail))

/-- `reduce_branches_normal` states that the branch walk returns normal bodies.
`reduceBranches` of lib/finite_term.ml lines 219 to 225 keeps the label of each branch and it replaces the body with the result of one step. docs/metatheory.md lines 358 to 370 record that.
-/
theorem reduce_branches_normal (step : Nat → Term → Ty → Res (Term × Nat))
    (hstep : ∀ (u : Nat) (x : Term) (b : Ty) (y : Term) (r : Nat),
      step u x b = .ok (y, r) → NormalForm y) :
    ∀ (fields : List (String × Ty × Term)) (f : Nat) (expected : Ty)
      (ys : List (String × Term)) (rest : Nat),
      reduceBranches step f fields expected = .ok (ys, rest) → NormalFormEntries ys
  | [], _f, _expected, _ys, _rest, h => normal_entries_transport h NormalFormEntries.nil
  | (_label, _fiber, body) :: more, f, expected, _ys, _rest, h =>
      match res_bind_ok h with
      | ⟨head, hhead, h2⟩ =>
          match res_bind_ok h2 with
          | ⟨tail, htail, h3⟩ =>
              normal_entries_transport h3
                (NormalFormEntries.cons _ head.1 tail.1
                  (hstep f body expected head.1 head.2 hhead)
                  (reduce_branches_normal step hstep more head.2 expected tail.1 tail.2 htail))

/-- `normal_lookup` states that a lookup into a normal entry list returns a normal value.
`lookup` mirrors the OCaml `lookup` at lib/finite_term.ml lines 40 and 41, and line 206 read one value out of a reduced
`section`. docs/metatheory.md lines 358 to 370 record that.
-/
theorem normal_lookup : ∀ {entries : List (String × Term)}, NormalFormEntries entries →
    ∀ (label : String) (found : Term), lookup label entries = .ok found → NormalForm found
  | _, .nil, _label, _found, h => (res_error_ne_ok h).elim
  | _, .cons key value more hv hm, label, found, h =>
      cond_elim (c := label == key) (x := some value) (y := List.lookup label more)
        (P := fun o : Option Term =>
          (Option.elim o (.error (.unexpectedLabel label)) .ok : Res Term) = .ok found →
            NormalForm found)
        (fun h2 => (Except.ok.inj h2 : value = found) ▸ hv)
        (fun h2 => normal_lookup hm label found h2) h
/-- `normal_section_entries` reads the entry list out of a normal `section`.
Line 206 of lib/finite_term.ml reads one value out of a reduced `section`, so the caller needs the entries of that node. docs/metatheory.md lines 358 to 370 record that reading.
-/
theorem normal_section_entries {entries : List (String × Term)}
    (h : NormalForm (.«section» entries)) : NormalFormEntries entries :=
  match h with
  | .«section» _ he => he

/-- `reduce_normal_form` states that one reduction returns a normal term.
It mirrors the OCaml `reduce` at lib/finite_term.ml lines 162 to 225, where lines 187 to 190 remove a `case` of a
`tag` scrutinee and lines 198 to 210 remove a `project` of a `section`.
The result holds no such node, and the comment at lines 158 to 161 states that rule. docs/metatheory.md lines 358 to 370 record the statement.
-/
theorem reduce_normal_form : ∀ (gas : Nat) (t : Term) (f : Nat) (a : Ty) (x : Term) (rest : Nat),
    reduce gas f t a = .ok (x, rest) → NormalForm x
  | 0, _t, _f, _a, _x, _rest, h => (res_error_ne_ok h).elim
  | gasPred + 1, t, _f, a, x, rest, h =>
      match res_bind_ok h with
      | ⟨g, _ht, h2⟩ =>
          match t, h2 with
          | .var .., hh => normal_transport hh (NormalForm.var _)
          | .atom .., hh => normal_transport hh (NormalForm.atom _)
          | .tag (payload := payload) .., hh =>
              match a, hh with
              | .lan .., h3 =>
                  match res_bind_ok h3 with
                  | ⟨fiber, _hfiber, h4⟩ =>
                      match res_bind_ok h4 with
                      | ⟨r, hr, h5⟩ =>
                          normal_transport h5
                            (NormalForm.tag _ r.1
                              (reduce_normal_form gasPred payload g fiber r.1 r.2 hr))
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .ran .., h3 => (res_error_ne_ok h3).elim
          | .«section» .., hh =>
              match a, hh with
              | .ran .., h3 =>
                  match res_bind_ok h3 with
                  | ⟨_sorted, _hsorted, h4⟩ =>
                      match res_bind_ok h4 with
                      | ⟨fields, _hfields, h5⟩ =>
                          match res_bind_ok h5 with
                          | ⟨r, hr, h6⟩ =>
                              normal_transport h6
                                (NormalForm.«section» r.1
                                  (reduce_fields_normal
                                    (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                    (fun u2 x2 b2 y2 r2 h7 =>
                                      reduce_normal_form gasPred x2 u2 b2 y2 r2 h7)
                                    fields g r.1 r.2 hr))
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .lan .., h3 => (res_error_ne_ok h3).elim
          | .«case» (scrutinee := scrutinee) (scrutineeType := st) .., hh =>
              match st, hh with
              | .lan .., h3 =>
                  match res_bind_ok h3 with
                  | ⟨_sorted, _hsorted, h4⟩ =>
                      match res_bind_ok h4 with
                      | ⟨head, hhead, h5⟩ =>
                          match head.1,
                              reduce_normal_form gasPred scrutinee g _ head.1 head.2 hhead, h5 with
                          | .tag .., _hn, h6 =>
                              match res_bind_ok h6 with
                              | ⟨_body, _hbody, h7⟩ =>
                                  match res_bind_ok h7 with
                                  | ⟨opened, _hopened, h8⟩ =>
                                      reduce_normal_form gasPred opened.1 opened.2 a x rest h8
                          | .var .., hn, h6 =>
                              match res_bind_ok h6 with
                              | ⟨fields, _hfields, h7⟩ =>
                                  match res_bind_ok h7 with
                                  | ⟨r, hr, h8⟩ =>
                                      normal_transport h8
                                        (NormalForm.«case» _ _ r.1 True.intro hn
                                          (reduce_branches_normal
                                            (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                            (fun u2 x2 b2 y2 r2 h9 =>
                                              reduce_normal_form gasPred x2 u2 b2 y2 r2 h9)
                                            fields head.2 a r.1 r.2 hr))
                          | .«case» .., hn, h6 =>
                              match res_bind_ok h6 with
                              | ⟨fields, _hfields, h7⟩ =>
                                  match res_bind_ok h7 with
                                  | ⟨r, hr, h8⟩ =>
                                      normal_transport h8
                                        (NormalForm.«case» _ _ r.1 True.intro hn
                                          (reduce_branches_normal
                                            (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                            (fun u2 x2 b2 y2 r2 h9 =>
                                              reduce_normal_form gasPred x2 u2 b2 y2 r2 h9)
                                            fields head.2 a r.1 r.2 hr))
                          | .project .., hn, h6 =>
                              match res_bind_ok h6 with
                              | ⟨fields, _hfields, h7⟩ =>
                                  match res_bind_ok h7 with
                                  | ⟨r, hr, h8⟩ =>
                                      normal_transport h8
                                        (NormalForm.«case» _ _ r.1 True.intro hn
                                          (reduce_branches_normal
                                            (fun f2 x2 a2 => reduce gasPred f2 x2 a2)
                                            (fun u2 x2 b2 y2 r2 h9 =>
                                              reduce_normal_form gasPred x2 u2 b2 y2 r2 h9)
                                            fields head.2 a r.1 r.2 hr))
                          | .atom .., _hn, h6 => (res_error_ne_ok h6).elim
                          | .«section» .., _hn, h6 => (res_error_ne_ok h6).elim
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .ran .., h3 => (res_error_ne_ok h3).elim
          | .project («section» := field) (sectionType := sty) .., hh =>
              match sty, hh with
              | .ran .., h3 =>
                  match res_bind_ok h3 with
                  | ⟨_actual, _hactual, h4⟩ =>
                      ite_elim
                        (P := fun w : Res (Term × Nat) => w = .ok (x, rest) → NormalForm x)
                        (fun _hc h5 =>
                          match res_bind_ok h5 with
                          | ⟨head, hhead, h6⟩ =>
                              match head.1,
                                  reduce_normal_form gasPred field g _ head.1 head.2 hhead,
                                  h6 with
                              | .«section» .., hn, h7 =>
                                  match res_bind_ok h7 with
                                  | ⟨found, hfound, h8⟩ =>
                                      normal_transport h8
                                        (normal_lookup (normal_section_entries hn) _ found hfound)
                              | .var .., hn, h7 =>
                                  normal_transport h7 (NormalForm.project _ _ _ True.intro hn)
                              | .«case» .., hn, h7 =>
                                  normal_transport h7 (NormalForm.project _ _ _ True.intro hn)
                              | .project .., hn, h7 =>
                                  normal_transport h7 (NormalForm.project _ _ _ True.intro hn)
                              | .atom .., _hn, h7 => (res_error_ne_ok h7).elim
                              | .tag .., _hn, h7 => (res_error_ne_ok h7).elim)
                        (fun _hc h5 => (res_error_ne_ok h5).elim) h4
              | .atoms .., h3 => (res_error_ne_ok h3).elim
              | .lan .., h3 => (res_error_ne_ok h3).elim





/-- The public normalizer returns a term with no Case-of-Tag or Project-of-Section redex.
This lifts the reduction guarantee through the check and budget erasure of lib/finite_term.ml lines 227 to 229.
It asserts no successful fuel bound.
-/
theorem normalize_normal_form (fuel : Nat) (g : List Ty) (t t' : Term) (a : Ty)
    (h : normalize fuel g t a = Except.ok t') : NormalForm t' :=
  match res_bind_ok h with
  | ⟨remaining, _checked, reduced⟩ =>
      match res_bind_ok reduced with
      | ⟨result, core, returned⟩ =>
          (Except.ok.inj returned) ▸
            reduce_normal_form (remaining + 1) t remaining a result.1 result.2 core
