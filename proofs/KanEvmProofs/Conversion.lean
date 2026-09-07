import KanEvmProofs.NormalizeTyping
import KanEvmProofs.NormalizeAgree

/-! # Fueled conversion of the finite fragment

Conversion checks and normalizes both inputs under one shared budget, then compares
the resulting syntax. Annotations participate in equality, and neutral terms receive
no eta expansion. Success asserts neither confluence nor a sufficient fuel bound.
-/

mutual
/-- Structural equality includes every annotation and the order of every entry list. -/
def Term.beq : Term → Term → Bool
  | .var i, .var j => i == j
  | .atom a, .atom b => a == b
  | .tag a t, .tag b u => a == b && Term.beq t u
  | .«section» fs, .«section» gs => Term.beqEntries fs gs
  | .«case» t a fs, .«case» u b gs =>
      Term.beq t u && Ty.beq a b && Term.beqEntries fs gs
  | .project t a l, .project u b k => Term.beq t u && Ty.beq a b && l == k
  | .var .., .atom .. | .var .., .tag .. | .var .., .«section» ..
  | .var .., .«case» .. | .var .., .project ..
  | .atom .., .var .. | .atom .., .tag .. | .atom .., .«section» ..
  | .atom .., .«case» .. | .atom .., .project ..
  | .tag .., .var .. | .tag .., .atom .. | .tag .., .«section» ..
  | .tag .., .«case» .. | .tag .., .project ..
  | .«section» .., .var .. | .«section» .., .atom .. | .«section» .., .tag ..
  | .«section» .., .«case» .. | .«section» .., .project ..
  | .«case» .., .var .. | .«case» .., .atom .. | .«case» .., .tag ..
  | .«case» .., .«section» .. | .«case» .., .project ..
  | .project .., .var .. | .project .., .atom .. | .project .., .tag ..
  | .project .., .«section» .. | .project .., .«case» .. => false

/-- Structural equality for the nested term lists of sections and cases. -/
def Term.beqEntries : List (String × Term) → List (String × Term) → Bool
  | [], [] => true
  | (a, t) :: fs, (b, u) :: gs => a == b && Term.beq t u && Term.beqEntries fs gs
  | [], .cons .. | .cons .., [] => false
end

instance : BEq Term := ⟨Term.beq⟩

namespace Conversion

private theorem and_true {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := Eq.mp (Bool.and_eq_true a b) h

private theorem and_mk {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := Eq.mpr (Bool.and_eq_true a b) ⟨ha, hb⟩

end Conversion

mutual
/-- Term comparison decides literal syntax equality, including type annotations. -/
theorem term_beq_iff : (t u : Term) → (Term.beq t u = true ↔ t = u)
  | .var .., .var .. =>
      ⟨fun h => congrArg Term.var (eq_of_beq h),
        fun h => beq_iff_eq.mpr (Term.var.inj h)⟩
  | .atom .., .atom .. =>
      ⟨fun h => congrArg Term.atom (eq_of_beq h),
        fun h => beq_iff_eq.mpr (Term.atom.inj h)⟩
  | .tag _a t, .tag _b u =>
      ⟨fun h => congr (congrArg Term.tag (eq_of_beq (Conversion.and_true h).1))
          ((term_beq_iff t u).mp (Conversion.and_true h).2),
        fun h => Conversion.and_mk (beq_iff_eq.mpr (Term.tag.inj h).1)
          ((term_beq_iff t u).mpr (Term.tag.inj h).2)⟩
  | .«section» fs, .«section» gs =>
      ⟨fun h => congrArg Term.«section» ((term_beqEntries_iff fs gs).mp h),
        fun h => (term_beqEntries_iff fs gs).mpr (Term.«section».inj h)⟩
  | .«case» t a fs, .«case» u b gs =>
      ⟨fun h => congr
          (congr (congrArg Term.«case»
            ((term_beq_iff t u).mp (Conversion.and_true (Conversion.and_true h).1).1))
            ((ty_beq_iff a b).mp (Conversion.and_true (Conversion.and_true h).1).2))
          ((term_beqEntries_iff fs gs).mp (Conversion.and_true h).2),
        fun h => Conversion.and_mk
          (Conversion.and_mk ((term_beq_iff t u).mpr (Term.«case».inj h).1)
            ((ty_beq_iff a b).mpr (Term.«case».inj h).2.1))
          ((term_beqEntries_iff fs gs).mpr (Term.«case».inj h).2.2)⟩
  | .project t a .., .project u b .. =>
      ⟨fun h => congr
          (congr (congrArg Term.project
            ((term_beq_iff t u).mp (Conversion.and_true (Conversion.and_true h).1).1))
            ((ty_beq_iff a b).mp (Conversion.and_true (Conversion.and_true h).1).2))
          (eq_of_beq (Conversion.and_true h).2),
        fun h => Conversion.and_mk
          (Conversion.and_mk ((term_beq_iff t u).mpr (Term.project.inj h).1)
            ((ty_beq_iff a b).mpr (Term.project.inj h).2.1))
          (beq_iff_eq.mpr (Term.project.inj h).2.2)⟩
  | .var .., .atom .. | .var .., .tag .. | .var .., .«section» ..
  | .var .., .«case» .. | .var .., .project ..
  | .atom .., .var .. | .atom .., .tag .. | .atom .., .«section» ..
  | .atom .., .«case» .. | .atom .., .project ..
  | .tag .., .var .. | .tag .., .atom .. | .tag .., .«section» ..
  | .tag .., .«case» .. | .tag .., .project ..
  | .«section» .., .var .. | .«section» .., .atom .. | .«section» .., .tag ..
  | .«section» .., .«case» .. | .«section» .., .project ..
  | .«case» .., .var .. | .«case» .., .atom .. | .«case» .., .tag ..
  | .«case» .., .«section» .. | .«case» .., .project ..
  | .project .., .var .. | .project .., .atom .. | .project .., .tag ..
  | .project .., .«section» .. | .project .., .«case» .. =>
      ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩

/-- Entry comparison decides equality of labels, bodies, and list order. -/
theorem term_beqEntries_iff : (fs gs : List (String × Term)) →
    (Term.beqEntries fs gs = true ↔ fs = gs)
  | [], [] => ⟨fun h => Canon.hold_first rfl h, fun h => Canon.hold_first rfl h⟩
  | [], .cons .. | .cons .., [] =>
      ⟨fun h => False.elim (Canon.false_ne_true h), fun h => nomatch h⟩
  | (_a, t) :: fs, (_b, u) :: gs =>
      ⟨fun h => congr
          (congrArg List.cons
            (congr (congrArg Prod.mk
              (eq_of_beq (Conversion.and_true (Conversion.and_true h).1).1))
              ((term_beq_iff t u).mp (Conversion.and_true (Conversion.and_true h).1).2)))
          ((term_beqEntries_iff fs gs).mp (Conversion.and_true h).2),
        fun h => Conversion.and_mk
          (Conversion.and_mk (beq_iff_eq.mpr (Prod.mk.inj (List.cons.inj h).1).1)
            ((term_beq_iff t u).mpr (Prod.mk.inj (List.cons.inj h).1).2))
          ((term_beqEntries_iff fs gs).mpr (List.cons.inj h).2)⟩
end

/-- Checking and reduction return the unused budget for the next operand. -/
def normalizeWithRest (fuel : Nat) (ctx : List Ty) (t : Term) (expected : Ty) :
    Res (Term × Nat) :=
  checkCore (2 * fuel + 2) fuel ctx t expected >>= fun remaining =>
    reduce (remaining + 1) remaining t expected

/-- Conversion spends one budget in left-to-right order and propagates either error. -/
def convert (fuel : Nat) (ctx : List Ty) (left right : Term) (expected : Ty) : Res Bool :=
  normalizeWithRest fuel ctx left expected >>= fun l =>
    normalizeWithRest l.2 ctx right expected >>= fun r =>
      .ok (Term.beq l.1 r.1)

/-- Retaining the remaining budget leaves the existing normalization result unchanged. -/
theorem normalizeWithRest_normalize (fuel : Nat) (ctx : List Ty) (t x : Term) (a : Ty)
    (rest : Nat) (h : normalizeWithRest fuel ctx t a = .ok (x, rest)) :
    normalize fuel ctx t a = .ok x :=
  match res_bind_ok h with
  | ⟨_checkedRest, hc, hr⟩ => res_bind_mk hc (res_bind_mk hr rfl)

/-- A retained-budget normalization establishes input typing and normal output typing. -/
theorem normalizeWithRest_spec (fuel : Nat) (ctx : List Ty) (t x : Term) (a : Ty)
    (rest : Nat) (h : normalizeWithRest fuel ctx t a = .ok (x, rest)) :
    HasType ctx t a ∧ HasType ctx x a ∧ NormalForm x :=
  match res_bind_ok h with
  | ⟨checkedRest, hc, _hr⟩ =>
      let hn := normalizeWithRest_normalize fuel ctx t x a rest h
      ⟨Checker.check_core_sound (2 * fuel + 2) fuel ctx t a checkedRest hc,
        normalize_preserves_type fuel ctx t x a hn,
        normalize_normal_form fuel ctx t x a hn⟩

/-- Successful conversion exposes both normalizations and their shared budget boundary. -/
theorem convert_success_iff (fuel : Nat) (ctx : List Ty) (left right : Term) (a : Ty)
    (result : Bool) : convert fuel ctx left right a = .ok result ↔
      ∃ (x : Term) (leftRest : Nat) (y : Term) (rightRest : Nat),
        normalizeWithRest fuel ctx left a = .ok (x, leftRest) ∧
        normalizeWithRest leftRest ctx right a = .ok (y, rightRest) ∧
        Term.beq x y = result :=
  ⟨fun h =>
    match res_bind_ok h with
    | ⟨l, hl, h2⟩ =>
        match res_bind_ok h2 with
        | ⟨r, hr, h3⟩ => ⟨l.1, l.2, r.1, r.2, hl, hr, Except.ok.inj h3⟩,
    fun ⟨_x, _lr, _y, _rr, hl, hr, hb⟩ =>
      res_bind_mk hl (res_bind_mk hr (congrArg Except.ok hb))⟩

/-- A true result is exactly equal successful normal forms at the shared budgets. -/
theorem convert_true_iff (fuel : Nat) (ctx : List Ty) (left right : Term) (a : Ty) :
    convert fuel ctx left right a = .ok true ↔
      ∃ (x : Term) (leftRest : Nat) (y : Term) (rightRest : Nat),
        normalizeWithRest fuel ctx left a = .ok (x, leftRest) ∧
        normalizeWithRest leftRest ctx right a = .ok (y, rightRest) ∧ x = y :=
  ⟨fun h =>
    match (convert_success_iff fuel ctx left right a true).mp h with
    | ⟨x, lr, y, rr, hl, hr, hb⟩ =>
        ⟨x, lr, y, rr, hl, hr, (term_beq_iff x y).mp hb⟩,
    fun ⟨x, lr, y, rr, hl, hr, he⟩ =>
      (convert_success_iff fuel ctx left right a true).mpr
        ⟨x, lr, y, rr, hl, hr, (term_beq_iff x y).mpr he⟩⟩

/-- Either Boolean result guarantees that both input terms have the expected type. -/
theorem convert_inputs_typed (fuel : Nat) (ctx : List Ty) (left right : Term) (a : Ty)
    (result : Bool) (h : convert fuel ctx left right a = .ok result) :
    HasType ctx left a ∧ HasType ctx right a :=
  match (convert_success_iff fuel ctx left right a result).mp h with
  | ⟨x, lr, y, rr, hl, hr, _hb⟩ =>
      ⟨(normalizeWithRest_spec fuel ctx left x a lr hl).1,
        (normalizeWithRest_spec lr ctx right y a rr hr).1⟩

/-- Equal closed conversion results agree with the quotations of successful executions.
The execution budgets are independent, and execution success remains an explicit premise.
-/
theorem convert_agrees_with_run (fuel leftRunFuel rightRunFuel : Nat)
    (left right : Term) (a : Ty) (leftValue rightValue : Value)
    (hc : convert fuel [] left right a = .ok true)
    (hl : run leftRunFuel left a = .ok leftValue)
    (hr : run rightRunFuel right a = .ok rightValue) : quote leftValue = quote rightValue :=
  match (convert_true_iff fuel [] left right a).mp hc with
  | ⟨x, lr, y, rr, hnl, hnr, he⟩ =>
      (normalize_agrees_with_run fuel leftRunFuel left x a leftValue
        (normalizeWithRest_normalize fuel [] left x a lr hnl) hl).symm.trans
        (he.trans (normalize_agrees_with_run lr rightRunFuel right y a rightValue
          (normalizeWithRest_normalize lr [] right y a rr hnr) hr))
