import KanEvmProofs.Syntax
import KanEvmProofs.Check
import KanEvmProofs.Subst
import KanEvmProofs.Typing

/-! # Weakening of the finite fragment

This module states and proves Theorem 2 of docs/metatheory.md lines 147 to 170.
The mirrored OCaml text is `map_variables` at lib/finite_term.ml lines 112 to 135.
Decision S2-D5 splits that text into `shift` and `shiftEntries` of Subst.lean.
Decision S2-D8 fixes the cutoff rule of that pair, and the cutoff rises one unit inside each `case` branch and nowhere else.
The whole proof runs in term mode. No tactic block appears in this module.
-/

namespace Weakening

/-- `errNotOk` states that one error result never equals one success result.
It carries the constructor test that every inversion step of this module needs.
It mirrors the error path of `map_variables` at lib/finite_term.ml lines 112 to 135.
It states no proposition of docs/metatheory.md and it serves the proof of lines 147 to 170.
-/
theorem errNotOk {α : Type} {e : Err} {v : α}
    (h : (Except.error e : Res α) = Except.ok v) : False :=
  nomatch h

/-- `bindOkElim` inverts one successful bind of the error monad.
A success of `m >>= k` gives one value `x` with `m = .ok x` and with `k x = .ok v`.
It mirrors the sequencing of `map_variables` at lib/finite_term.ml lines 112 to 135.
It states no proposition of docs/metatheory.md and it serves the proof of lines 147 to 170.
-/
theorem bindOkElim {α β : Type} {P : Prop} (m : Res α) (k : α → Res β) (v : β)
    (step : ∀ (x : α), m = Except.ok x → k x = Except.ok v → P)
    (h : (m >>= k) = Except.ok v) : P :=
  Except.rec
    (motive := fun (z : Res α) =>
      (∀ (x : α), z = Except.ok x → k x = Except.ok v → P) → (z >>= k) = Except.ok v → P)
    (fun _e _g hz => False.elim (errNotOk hz))
    (fun x g hz => g x rfl hz)
    m step h

/-- `iteCongr` rewrites the two branches of one conditional term.
It supports the sort step of lib/finite_term.ml line 21, which `insertEntry` of Check.lean holds.
It states no proposition of docs/metatheory.md and it serves the proof of lines 147 to 170.
-/
theorem iteCongr {α : Type} {p : Prop} [inst : Decidable p] {x y u v : α}
    (ht : x = u) (hf : y = v) : (if p then x else y) = (if p then u else v) :=
  (congrArg (fun (z : α) => if p then z else y) ht).trans
    (congrArg (fun (z : α) => if p then u else z) hf)

/-- `iteMap` moves one function inside one conditional term.
It supports the sort step of lib/finite_term.ml line 21, which `insertEntry` of Check.lean holds.
It states no proposition of docs/metatheory.md and it serves the proof of lines 147 to 170.
-/
theorem iteMap {α β : Type} {p : Prop} [inst : Decidable p] (f : α → β) (x y : α) :
    f (if p then x else y) = (if p then f x else f y) :=
  Decidable.rec (motive := fun (z : Decidable p) => f (@ite α p z x y) = @ite β p z (f x) (f y))
    (fun _hn => rfl) (fun _hp => rfl) inst

/-- `natShiftComm` moves one unit across one sum of natural numbers.
It states the index arithmetic of the raising callback at lib/finite_term.ml lines 146 to 149.
It states the step `i + d` of docs/metatheory.md lines 149 and 165.
-/
theorem natShiftComm : ∀ (k d : Nat), k + 1 + d = k + d + 1
  | _k, 0 => rfl
  | k, e + 1 => congrArg (fun (n : Nat) => n + 1) (natShiftComm k e)

/-- `cutoffStep` relates the cutoff test at one deeper index to the cutoff test at the index.
It states the guard `index < c` of the raising callback at lib/finite_term.ml lines 147 and 148.
It states the two cases of docs/metatheory.md lines 149 and 165.
-/
theorem cutoffStep (k n d : Nat) :
    (if k + 1 < n + 1 then k + 1 else k + 1 + d) = (if k < n then k else k + d) + 1 :=
  match Nat.decLt k n with
  | .isTrue hp =>
      (if_pos (Nat.succ_lt_succ hp)).trans (congrArg (fun (z : Nat) => z + 1) (if_pos hp)).symm
  | .isFalse hn =>
      (if_neg (fun (hlt : k + 1 < n + 1) => hn (Nat.lt_of_succ_lt_succ hlt))).trans
        ((natShiftComm k d).trans (congrArg (fun (z : Nat) => z + 1) (if_neg hn)).symm)

/-- `variableZero` reads the head of one context.
It mirrors the successful read of `variable` at lib/finite_term.ml lines 43 to 45.
It states the rule VAR of docs/metatheory.md line 40 at index zero.
-/
theorem variableZero (x : Ty) (l : List Ty) : «variable» 0 (x :: l) = Except.ok x := rfl

/-- `getElemStep` drops the head of one list and one unit of the index together.
It mirrors the list walk of `variable` at lib/finite_term.ml lines 43 to 45.
It states the index step of docs/metatheory.md lines 163 to 166.
-/
theorem getElemStep (x : Ty) (l : List Ty) (i : Nat) : (x :: l)[i + 1]? = l[i]? := rfl

/-- `optionElimOk` keeps one successful read under one other error value.
Two calls of `variable` at two indexes name two error values, and a success hides both.
It mirrors the total read of `variable` at lib/finite_term.ml lines 43 to 45.
It states the index step of docs/metatheory.md lines 163 to 166.
-/
theorem optionElimOk (o : Option Ty) (e1 e2 : Err) (a : Ty)
    (h : o.elim (Except.error e1) Except.ok = Except.ok a) :
    o.elim (Except.error e2) Except.ok = Except.ok a :=
  Option.rec
    (motive := fun (z : Option Ty) =>
      z.elim (Except.error e1) Except.ok = Except.ok a →
      z.elim (Except.error e2) Except.ok = Except.ok a)
    (fun hn => False.elim (errNotOk hn))
    (fun _y hs => hs)
    o h

/-- `variableStep` reads one context under one longer context and one deeper index.
It mirrors the list walk of `variable` at lib/finite_term.ml lines 43 to 45.
It states the index step of docs/metatheory.md lines 163 to 166.
-/
theorem variableStep (x : Ty) (l : List Ty) (i : Nat) (a : Ty)
    (h : «variable» i l = Except.ok a) : «variable» (i + 1) (x :: l) = Except.ok a :=
  (congrArg
      (fun (o : Option Ty) => o.elim (Except.error (Err.invalidVariable (i + 1))) Except.ok)
      (getElemStep x l i)).trans
    (optionElimOk l[i]? (Err.invalidVariable i) (Err.invalidVariable (i + 1)) a h)

/-- `variableStepBack` reads one longer context down to one shorter context.
It mirrors the list walk of `variable` at lib/finite_term.ml lines 43 to 45.
It states the index step of docs/metatheory.md lines 163 to 166.
-/
theorem variableStepBack (x : Ty) (l : List Ty) (i : Nat) (a : Ty)
    (h : «variable» (i + 1) (x :: l) = Except.ok a) : «variable» i l = Except.ok a :=
  optionElimOk l[i]? (Err.invalidVariable (i + 1)) (Err.invalidVariable i) a
    ((congrArg
        (fun (o : Option Ty) => o.elim (Except.error (Err.invalidVariable (i + 1))) Except.ok)
        (getElemStep x l i)).symm.trans h)

/-- `indexEq` moves one context read along one equality of indices.
It carries the index arithmetic of docs/metatheory.md lines 163 to 166 into `variable`.
-/
theorem indexEq (i j : Nat) (l : List Ty) (a : Ty) (h : j = i)
    (v : «variable» i l = Except.ok a) : «variable» j l = Except.ok a :=
  Eq.mp (congrArg (fun (n : Nat) => «variable» n l = Except.ok a) h.symm) v

/-- `headEq` reads the head of one context at index zero.
It mirrors the variable arm of `check_term` at lib/finite_term.ml lines 65 to 67.
-/
theorem headEq (x a : Ty) (l : List Ty) (h : «variable» 0 (x :: l) = Except.ok a) : x = a :=
  Except.ok.inj h

/-- `variableAppend` inserts one context at the front and adds its length to every index.
It states the index step of docs/metatheory.md lines 163 to 166 at the cutoff zero.
-/
theorem variableAppend : ∀ (dd g2 : List Ty) (i : Nat) (a : Ty),
    «variable» i g2 = Except.ok a →
      «variable» (i + dd.length) (dd ++ g2) = Except.ok a
  | [], _g2, _i, _a, h => h
  | x :: dd, g2, i, a, h =>
      variableStep x (dd ++ g2) (i + dd.length) a (variableAppend dd g2 i a h)

/-- `variableWeakenCore` weakens one context read at the cutoff of docs/metatheory.md line 159.
An index below the cutoff reads the same type, and an index at the cutoff or above it rises.
It states the index step of docs/metatheory.md lines 163 to 166.
-/
theorem variableWeakenCore (dd : List Ty) : ∀ (g1 g2 : List Ty) (i : Nat) (a : Ty),
    «variable» i (g1 ++ g2) = Except.ok a →
      «variable» (if i < g1.length then i else i + dd.length) (g1 ++ dd ++ g2) = Except.ok a
  | [], g2, i, a, h =>
      indexEq (i + dd.length) (if i < List.length ([] : List Ty) then i else i + dd.length)
        (dd ++ g2) a
        (if_neg (fun (hlt : i < List.length ([] : List Ty)) => Nat.not_lt_zero i hlt))
        (variableAppend dd g2 i a h)
  | x :: g1, g2, 0, a, h =>
      indexEq 0 (if 0 < List.length (x :: g1) then 0 else 0 + dd.length)
        (x :: (g1 ++ dd ++ g2)) a
        (if_pos (Nat.zero_lt_succ (List.length g1)))
        ((variableZero x (g1 ++ dd ++ g2)).trans (congrArg Except.ok (headEq x a (g1 ++ g2) h)))
  | x :: g1, g2, i + 1, a, h =>
      indexEq ((if i < List.length g1 then i else i + dd.length) + 1)
        (if i + 1 < List.length (x :: g1) then i + 1 else i + 1 + dd.length)
        (x :: (g1 ++ dd ++ g2)) a
        (cutoffStep i (List.length g1) (List.length dd))
        (variableStep x (g1 ++ dd ++ g2) (if i < List.length g1 then i else i + dd.length) a
          (variableWeakenCore dd g1 g2 i a (variableStepBack x (g1 ++ g2) i a h)))

mutual
/-- `shiftPure` is the term of `shift` alone, without the budget.
It mirrors the raising instance of `map_variables` at lib/finite_term.ml lines 112 to 135.
It states the map of docs/metatheory.md lines 149 to 151.
`shiftOkPure` relates it to `shift` of Subst.lean at every budget that succeeds.
The cutoff rises one unit inside each `case` branch and nowhere else, per decision S2-D8.
-/
def shiftPure (c d : Nat) (t : Term) : Term :=
  match t with
  | .var index => .var (if index < c then index else index + d)
  | .atom label => .atom label
  | .tag label payload => .tag label (shiftPure c d payload)
  | .«section» fields => .«section» (shiftPureEntries c d fields)
  | .«case» scrutinee scrutineeType branches =>
      .«case» (shiftPure c d scrutinee) scrutineeType (shiftPureEntries (c + 1) d branches)
  | .project field sectionType label => .project (shiftPure c d field) sectionType label

/-- `shiftPureEntries` is the entry list companion of `shiftPure`.
It mirrors `map_entries` at lib/finite_term.ml lines 130 to 135.
It keeps the label of each entry and it keeps the source order of the list.
It states the map of docs/metatheory.md lines 149 to 151 over one entry list.
-/
def shiftPureEntries (c d : Nat) (entries : List (String × Term)) : List (String × Term) :=
  match entries with
  | [] => []
  | (label, field) :: rest => (label, shiftPure c d field) :: shiftPureEntries c d rest
end

/-- `shiftTriples` raises the term of each aligned triple.
The triple list is the one `align` returns at lib/finite_term.ml lines 51 to 60.
It states the map of docs/metatheory.md lines 149 to 151 over one aligned triple list.
-/
def shiftTriples (c d : Nat) (pairs : List (String × Ty × Term)) : List (String × Ty × Term) :=
  match pairs with
  | [] => []
  | (label, fiber, body) :: rest => (label, fiber, shiftPure c d body) :: shiftTriples c d rest

/-- `cutoffFor` gives the cutoff of one entry list from the mode of `HasTypeEntries`.
The field mode keeps the cutoff, and the branch mode raises it one unit.
It mirrors the extended context of lib/finite_term.ml lines 92 and 93.
It states the binder of docs/metatheory.md lines 47 to 49, which line 159 raises the cutoff for.
-/
def cutoffFor (mode : Option Ty) (c : Nat) : Nat :=
  c + mode.toList.length

/-- `canonicalStep` names the tail of `canonicalEntries` of Check.lean.
It mirrors `canonical` at lib/finite_term.ml lines 20 to 23 over one term entry list.
It states the key alignment of docs/metatheory.md lines 53 to 59.
-/
def canonicalStep (labels : List String) (sorted : List (String × Term)) :
    Res (List (String × Term)) :=
  unique labels >>= fun (_ok : Unit) => Except.ok sorted

/-- `labelsShift` states that the raise keeps every label of one entry list.
It mirrors `map_entries` at lib/finite_term.ml lines 130 to 135, which reads no label.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the map of line 149.
-/
theorem labelsShift (c d : Nat) :
    ∀ (entries : List (String × Term)),
      (shiftPureEntries c d entries).map Prod.fst = entries.map Prod.fst
  | [] => rfl
  | (label, _field) :: rest =>
      congrArg (fun (z : List String) => label :: z) (labelsShift c d rest)

/-- `insertShift` moves the raise across one insertion step of the sort.
The insertion reads the labels alone, and the raise keeps every label.
It mirrors the sort at lib/finite_term.ml line 21, which `insertEntry` of Check.lean holds.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the map of line 149.
-/
theorem insertShift (c d : Nat) (label : String) (field : Term) :
    ∀ (entries : List (String × Term)),
      insertEntry (label, shiftPure c d field) (shiftPureEntries c d entries)
        = shiftPureEntries c d (insertEntry (label, field) entries)
  | [] => rfl
  | (key, payload) :: tail =>
      (iteCongr rfl
          (congrArg (fun (z : List (String × Term)) => (key, shiftPure c d payload) :: z)
            (insertShift c d label field tail))).trans
        (iteMap (shiftPureEntries c d) ((label, field) :: (key, payload) :: tail)
          ((key, payload) :: insertEntry (label, field) tail)).symm

/-- `sortShift` moves the raise across the whole sort.
It mirrors the sort at lib/finite_term.ml line 21, which `sortEntries` of Check.lean holds.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the map of line 149.
-/
theorem sortShift (c d : Nat) :
    ∀ (entries : List (String × Term)),
      sortEntries (shiftPureEntries c d entries) = shiftPureEntries c d (sortEntries entries)
  | [] => rfl
  | (label, field) :: rest =>
      (congrArg (insertEntry (label, shiftPure c d field)) (sortShift c d rest)).trans
        (insertShift c d label field (sortEntries rest))

/-- `bindConstMap` moves one map across one bind that drops its value.
It mirrors the sequencing of `canonical` at lib/finite_term.ml lines 20 to 23.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the map of line 149.
-/
theorem bindConstMap (m : Res Unit) (x : List (String × Term))
    (f : List (String × Term) → List (String × Term)) :
    (m >>= fun (_ok : Unit) => Except.ok (f x))
      = (m >>= fun (_ok : Unit) => Except.ok x).map f :=
  Except.rec
    (motive := fun (z : Res Unit) =>
      (z >>= fun (_ok : Unit) => Except.ok (f x))
        = (z >>= fun (_ok : Unit) => Except.ok x).map f)
    (fun _e => rfl) (fun _u => rfl) m

/-- `canonicalShift` moves the raise across `canonicalEntries` of Check.lean.
The canonical step reads the labels alone, and the raise keeps every label.
It mirrors `canonical` at lib/finite_term.ml lines 20 to 23, which line 81 and line 89 call.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the map of line 149.
-/
theorem canonicalShift (c d : Nat) (entries : List (String × Term)) :
    canonicalEntries (shiftPureEntries c d entries)
      = (canonicalEntries entries).map (shiftPureEntries c d) :=
  (congrArg (fun (z : List (String × Term)) => canonicalStep (z.map Prod.fst) z)
      (sortShift c d entries)).trans
    ((congrArg
        (fun (ls : List String) =>
          canonicalStep ls (shiftPureEntries c d (sortEntries entries)))
        (labelsShift c d (sortEntries entries))).trans
      (bindConstMap (unique ((sortEntries entries).map Prod.fst)) (sortEntries entries)
        (shiftPureEntries c d)))

/-- `alignStep` moves the raise across one aligned entry of `align`.
It mirrors the successful arm of `align` at lib/finite_term.ml lines 51 to 60.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the map of line 149.
-/
theorem alignStep (m : Res (List (String × Ty × Term))) (c d : Nat)
    (key : String) (fiber : Ty) (field : Term) :
    (m.map (shiftTriples c d) >>= fun (r : List (String × Ty × Term)) =>
        Except.ok ((key, fiber, shiftPure c d field) :: r))
      = (m >>= fun (r : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, field) :: r)).map (shiftTriples c d) :=
  Except.rec
    (motive := fun (z : Res (List (String × Ty × Term))) =>
      (z.map (shiftTriples c d) >>= fun (r : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, shiftPure c d field) :: r))
        = (z >>= fun (r : List (String × Ty × Term)) =>
            Except.ok ((key, fiber, field) :: r)).map (shiftTriples c d))
    (fun _e => rfl) (fun _a => rfl) m

/-- `ordMap` moves one function across one three way comparison.
The comparison is the one of `align` at lib/finite_term.ml lines 51 to 60.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the map of line 149.
-/
theorem ordMap {α β : Type} (g : α → β) (x1 x2 x3 : α) (y1 y2 y3 : β)
    (h1 : y1 = g x1) (h2 : y2 = g x2) (h3 : y3 = g x3) :
    ∀ (o : Ordering),
      (match o with
        | .lt => y1
        | .gt => y3
        | .eq => y2)
        = g (match o with
              | .lt => x1
              | .gt => x3
              | .eq => x2)
  | .lt => h1
  | .gt => h3
  | .eq => h2

/-- `alignShift` moves the raise across the whole walk of `align`.
It mirrors `align` at lib/finite_term.ml lines 51 to 60, which reads the labels alone.
It states the key alignment of docs/metatheory.md lines 53 to 59 under the map of line 149.
-/
theorem alignShift (c d : Nat) :
    ∀ (fibers : List (String × Ty)) (entries : List (String × Term)),
      align fibers (shiftPureEntries c d entries)
        = (align fibers entries).map (shiftTriples c d)
  | [], [] => rfl
  | .cons .., [] => rfl
  | [], .cons .. => rfl
  | (key, fiber) :: types, (label, field) :: terms =>
      ordMap (Except.map (shiftTriples c d))
        (Except.error (Err.missingLabel key))
        (align types terms >>= fun (r : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, field) :: r))
        (Except.error (Err.unexpectedLabel label))
        (Except.error (Err.missingLabel key))
        (align types (shiftPureEntries c d terms) >>= fun (r : List (String × Ty × Term)) =>
          Except.ok ((key, fiber, shiftPure c d field) :: r))
        (Except.error (Err.unexpectedLabel label)) rfl
        ((congrArg
            (fun (z : Res (List (String × Ty × Term))) =>
              z >>= fun (r : List (String × Ty × Term)) =>
                Except.ok ((key, fiber, shiftPure c d field) :: r))
            (alignShift c d types terms)).trans
          (alignStep (align types terms) c d key fiber field)) rfl
        (compare key label)

mutual
/-- `shiftOkPure` relates `shift` of Subst.lean to `shiftPure` at every budget that succeeds.
`shift` threads a budget and returns one pair, and the term of that pair is the raise alone.
It mirrors `map_variables` at lib/finite_term.ml lines 112 to 135, whose budget carries no term.
It states the map of docs/metatheory.md lines 149 to 151.
-/
theorem shiftOkPure (c d : Nat) : ∀ (t : Term) (fuel : Nat) (v : Term × Nat),
    shift c d fuel t = Except.ok v → v.1 = shiftPure c d t
  | .var index, fuel, v, h =>
      bindOkElim (tick fuel)
        (fun (f : Nat) => Except.ok (Term.var (if index < c then index else index + d), f)) v
        (fun (x : Nat) (_hx : tick fuel = Except.ok x)
            (hk : Except.ok (Term.var (if index < c then index else index + d), x)
              = Except.ok v) =>
          (congrArg (fun (p : Term × Nat) => p.1) (Except.ok.inj hk)).symm)
        h
  | .atom label, fuel, v, h =>
      bindOkElim (tick fuel) (fun (f : Nat) => Except.ok (Term.atom label, f)) v
        (fun (x : Nat) (_hx : tick fuel = Except.ok x)
            (hk : Except.ok (Term.atom label, x) = Except.ok v) =>
          (congrArg (fun (p : Term × Nat) => p.1) (Except.ok.inj hk)).symm)
        h
  | .tag label payload, fuel, v, h =>
      bindOkElim (tick fuel)
        (fun (f : Nat) =>
          shift c d f payload >>= fun (result : Term × Nat) =>
            Except.ok (Term.tag label result.1, result.2)) v
        (fun (x : Nat) (_hx : tick fuel = Except.ok x)
            (hk : (shift c d x payload >>= fun (result : Term × Nat) =>
                Except.ok (Term.tag label result.1, result.2)) = Except.ok v) =>
          bindOkElim (shift c d x payload)
            (fun (result : Term × Nat) => Except.ok (Term.tag label result.1, result.2)) v
            (fun (headPair : Term × Nat) (hs : shift c d x payload = Except.ok headPair)
                (hk2 : Except.ok (Term.tag label headPair.1, headPair.2) = Except.ok v) =>
              (congrArg (fun (p : Term × Nat) => p.1) (Except.ok.inj hk2)).symm.trans
                (congrArg (fun (z : Term) => Term.tag label z)
                  (shiftOkPure c d payload x headPair hs)))
            hk)
        h
  | .«section» fields, fuel, v, h =>
      bindOkElim (tick fuel)
        (fun (f : Nat) =>
          shiftEntries c d f fields >>= fun (result : List (String × Term) × Nat) =>
            Except.ok (Term.«section» result.1, result.2)) v
        (fun (x : Nat) (_hx : tick fuel = Except.ok x)
            (hk : (shiftEntries c d x fields >>= fun (result : List (String × Term) × Nat) =>
                Except.ok (Term.«section» result.1, result.2)) = Except.ok v) =>
          bindOkElim (shiftEntries c d x fields)
            (fun (result : List (String × Term) × Nat) =>
              Except.ok (Term.«section» result.1, result.2)) v
            (fun (tailPair : List (String × Term) × Nat)
                (ht : shiftEntries c d x fields = Except.ok tailPair)
                (hk2 : Except.ok (Term.«section» tailPair.1, tailPair.2) = Except.ok v) =>
              (congrArg (fun (p : Term × Nat) => p.1) (Except.ok.inj hk2)).symm.trans
                (congrArg (fun (z : List (String × Term)) => Term.«section» z)
                  (shiftEntriesOkPure c d fields x tailPair ht)))
            hk)
        h
  | .«case» scrutinee scrutineeType branches, fuel, v, h =>
      bindOkElim (tick fuel)
        (fun (f : Nat) =>
          shift c d f scrutinee >>= fun (head : Term × Nat) =>
            shiftEntries (c + 1) d head.2 branches >>= fun (rest : List (String × Term) × Nat) =>
              Except.ok (Term.«case» head.1 scrutineeType rest.1, rest.2)) v
        (fun (x : Nat) (_hx : tick fuel = Except.ok x)
            (hk : (shift c d x scrutinee >>= fun (head : Term × Nat) =>
                shiftEntries (c + 1) d head.2 branches
                  >>= fun (rest : List (String × Term) × Nat) =>
                    Except.ok (Term.«case» head.1 scrutineeType rest.1, rest.2)) = Except.ok v) =>
          bindOkElim (shift c d x scrutinee)
            (fun (head : Term × Nat) =>
              shiftEntries (c + 1) d head.2 branches
                >>= fun (rest : List (String × Term) × Nat) =>
                  Except.ok (Term.«case» head.1 scrutineeType rest.1, rest.2)) v
            (fun (headPair : Term × Nat) (hs : shift c d x scrutinee = Except.ok headPair)
                (hk2 : (shiftEntries (c + 1) d headPair.2 branches
                    >>= fun (rest : List (String × Term) × Nat) =>
                      Except.ok (Term.«case» headPair.1 scrutineeType rest.1, rest.2))
                  = Except.ok v) =>
              bindOkElim (shiftEntries (c + 1) d headPair.2 branches)
                (fun (rest : List (String × Term) × Nat) =>
                  Except.ok (Term.«case» headPair.1 scrutineeType rest.1, rest.2)) v
                (fun (tailPair : List (String × Term) × Nat)
                    (ht : shiftEntries (c + 1) d headPair.2 branches = Except.ok tailPair)
                    (hk3 : Except.ok (Term.«case» headPair.1 scrutineeType tailPair.1, tailPair.2)
                      = Except.ok v) =>
                  (congrArg (fun (p : Term × Nat) => p.1) (Except.ok.inj hk3)).symm.trans
                    ((congrArg (fun (z : Term) => Term.«case» z scrutineeType tailPair.1)
                        (shiftOkPure c d scrutinee x headPair hs)).trans
                      (congrArg
                        (fun (z : List (String × Term)) =>
                          Term.«case» (shiftPure c d scrutinee) scrutineeType z)
                        (shiftEntriesOkPure (c + 1) d branches headPair.2 tailPair ht))))
                hk2)
            hk)
        h
  | .project field sectionType label, fuel, v, h =>
      bindOkElim (tick fuel)
        (fun (f : Nat) =>
          shift c d f field >>= fun (result : Term × Nat) =>
            Except.ok (Term.project result.1 sectionType label, result.2)) v
        (fun (x : Nat) (_hx : tick fuel = Except.ok x)
            (hk : (shift c d x field >>= fun (result : Term × Nat) =>
                Except.ok (Term.project result.1 sectionType label, result.2)) = Except.ok v) =>
          bindOkElim (shift c d x field)
            (fun (result : Term × Nat) =>
              Except.ok (Term.project result.1 sectionType label, result.2)) v
            (fun (headPair : Term × Nat) (hs : shift c d x field = Except.ok headPair)
                (hk2 : Except.ok (Term.project headPair.1 sectionType label, headPair.2)
                  = Except.ok v) =>
              (congrArg (fun (p : Term × Nat) => p.1) (Except.ok.inj hk2)).symm.trans
                (congrArg (fun (z : Term) => Term.project z sectionType label)
                  (shiftOkPure c d field x headPair hs)))
            hk)
        h

/-- `shiftEntriesOkPure` is the entry list companion of `shiftOkPure`.
It mirrors `map_entries` at lib/finite_term.ml lines 130 to 135.
It states the map of docs/metatheory.md lines 149 to 151 over one entry list.
-/
theorem shiftEntriesOkPure (c d : Nat) : ∀ (entries : List (String × Term)) (fuel : Nat)
    (v : List (String × Term) × Nat),
    shiftEntries c d fuel entries = Except.ok v → v.1 = shiftPureEntries c d entries
  | [], _fuel, _v, h =>
      (congrArg (fun (p : List (String × Term) × Nat) => p.1) (Except.ok.inj h)).symm
  | (label, field) :: rest, fuel, v, h =>
      bindOkElim (shift c d fuel field)
        (fun (head : Term × Nat) =>
          shiftEntries c d head.2 rest >>= fun (tail : List (String × Term) × Nat) =>
            Except.ok ((label, head.1) :: tail.1, tail.2)) v
        (fun (headPair : Term × Nat) (hs : shift c d fuel field = Except.ok headPair)
            (hk : (shiftEntries c d headPair.2 rest
                >>= fun (tail : List (String × Term) × Nat) =>
                  Except.ok ((label, headPair.1) :: tail.1, tail.2)) = Except.ok v) =>
          bindOkElim (shiftEntries c d headPair.2 rest)
            (fun (tail : List (String × Term) × Nat) =>
              Except.ok ((label, headPair.1) :: tail.1, tail.2)) v
            (fun (tailPair : List (String × Term) × Nat)
                (ht : shiftEntries c d headPair.2 rest = Except.ok tailPair)
                (hk2 : Except.ok ((label, headPair.1) :: tailPair.1, tailPair.2) = Except.ok v) =>
              (congrArg (fun (p : List (String × Term) × Nat) => p.1)
                  (Except.ok.inj hk2)).symm.trans
                ((congrArg (fun (z : Term) => (label, z) :: tailPair.1)
                    (shiftOkPure c d field fuel headPair hs)).trans
                  (congrArg (fun (z : List (String × Term)) => (label, shiftPure c d field) :: z)
                    (shiftEntriesOkPure c d rest headPair.2 tailPair ht))))
            hk)
        h
end

mutual
/-- `weakeningPure` states Theorem2 of the stage brief on the raise alone.
A context insertion at the cutoff keeps the derivation.
Every index at the cutoff or above it rises the length of the inserted context.
It walks the derivation of `HasType`.
Each rule of that relation mirrors one arm of `check_term` at lib/finite_term.ml lines 62 to 105.
It states docs/metatheory.md section 7 lines 147 to 170, whose index step is lines 163 to 166.
-/
theorem weakeningPure : ∀ (ctx : List Ty) (t : Term) (b : Ty), HasType ctx t b →
    ∀ (g1 g2 : List Ty), ctx = g1 ++ g2 → ∀ (dd : List Ty),
      HasType (g1 ++ dd ++ g2) (shiftPure g1.length dd.length t) b
  | _, _, _, .var _ctx index a hv, g1, g2, heq, dd =>
      .var (g1 ++ dd ++ g2) (if index < g1.length then index else index + dd.length) a
        (variableWeakenCore dd g1 g2 index a
          (Eq.mp (congrArg (fun (z : List Ty) => «variable» index z = Except.ok a) heq) hv))
  | _, _, _, .atom _ctx name labels hm, g1, g2, _heq, dd =>
      .atom (g1 ++ dd ++ g2) name labels hm
  | _, _, _, .tag ctx label payload fibers fiber hlookup hpayload, g1, g2, heq, dd =>
      .tag (g1 ++ dd ++ g2) label (shiftPure g1.length dd.length payload) fibers fiber hlookup
        (weakeningPure ctx payload fiber hpayload g1 g2 heq dd)
  | _, _, _, .«section» ctx entries fibers sorted pairs hcanon halign hentries, g1, g2, heq, dd =>
      .«section» (g1 ++ dd ++ g2) (shiftPureEntries g1.length dd.length entries) fibers
        (shiftPureEntries g1.length dd.length sorted) (shiftTriples g1.length dd.length pairs)
        ((canonicalShift g1.length dd.length entries).trans
          (congrArg
            (fun (z : Res (List (String × Term))) =>
              z.map (shiftPureEntries g1.length dd.length))
            hcanon))
        ((alignShift g1.length dd.length fibers sorted).trans
          (congrArg
            (fun (z : Res (List (String × Ty × Term))) =>
              z.map (shiftTriples g1.length dd.length))
            halign))
        (weakeningPureEntries ctx pairs .none hentries g1 g2 heq dd)
  | _, _, _,
      .«case» ctx scrutinee fibers branches sorted pairs expected hcanon halign hscrut hbranches,
      g1, g2, heq, dd =>
      .«case» (g1 ++ dd ++ g2) (shiftPure g1.length dd.length scrutinee) fibers
        (shiftPureEntries (g1.length + 1) dd.length branches)
        (shiftPureEntries (g1.length + 1) dd.length sorted)
        (shiftTriples (g1.length + 1) dd.length pairs) expected
        ((canonicalShift (g1.length + 1) dd.length branches).trans
          (congrArg
            (fun (z : Res (List (String × Term))) =>
              z.map (shiftPureEntries (g1.length + 1) dd.length))
            hcanon))
        ((alignShift (g1.length + 1) dd.length fibers sorted).trans
          (congrArg
            (fun (z : Res (List (String × Ty × Term))) =>
              z.map (shiftTriples (g1.length + 1) dd.length))
            halign))
        (weakeningPure ctx scrutinee (.lan fibers) hscrut g1 g2 heq dd)
        (weakeningPureEntries ctx pairs (.some expected) hbranches g1 g2 heq dd)
  | _, _, _, .project ctx sectionTerm fibers label a hlookup hsection, g1, g2, heq, dd =>
      .project (g1 ++ dd ++ g2) (shiftPure g1.length dd.length sectionTerm) fibers label a hlookup
        (weakeningPure ctx sectionTerm (.ran fibers) hsection g1 g2 heq dd)

/-- `weakeningPureEntries` is the entry list companion of `weakeningPure`.
The mode of `HasTypeEntries` fixes the cutoff, which `cutoffFor` reads.
The field mode keeps the cutoff of the term, and the branch mode raises it one unit.
A branch reads the extended context of lib/finite_term.ml lines 92 and 93.
It states docs/metatheory.md section 7 lines 147 to 170 over one aligned triple list.
-/
theorem weakeningPureEntries : ∀ (ctx : List Ty) (pairs : List (String × Ty × Term))
    (mode : Option Ty), HasTypeEntries ctx pairs mode →
    ∀ (g1 g2 : List Ty), ctx = g1 ++ g2 → ∀ (dd : List Ty),
      HasTypeEntries (g1 ++ dd ++ g2)
        (shiftTriples (cutoffFor mode g1.length) dd.length pairs) mode
  | _, _, _, .nil _ctx mode, g1, g2, _heq, dd => .nil (g1 ++ dd ++ g2) mode
  | _, _, _, .field ctx label fiber fieldTerm rest hfield hrest, g1, g2, heq, dd =>
      .field (g1 ++ dd ++ g2) label fiber (shiftPure g1.length dd.length fieldTerm)
        (shiftTriples g1.length dd.length rest)
        (weakeningPure ctx fieldTerm fiber hfield g1 g2 heq dd)
        (weakeningPureEntries ctx rest .none hrest g1 g2 heq dd)
  | _, _, _, .branch ctx label payloadType body rest expected hbody hrest, g1, g2, heq, dd =>
      .branch (g1 ++ dd ++ g2) label payloadType (shiftPure (g1.length + 1) dd.length body)
        (shiftTriples (g1.length + 1) dd.length rest) expected
        (weakeningPure (payloadType :: ctx) body expected hbody (payloadType :: g1) g2
          (congrArg (fun (z : List Ty) => payloadType :: z) heq) dd)
        (weakeningPureEntries ctx rest (.some expected) hrest g1 g2 heq dd)
end

end Weakening

/-- `weakening_shift` is Theorem2 of the stage brief.
It reads one derivation at the context `g1 ++ g2` and one context `dd` of length `d`.
The cutoff `c` is the length of `g1`.
It gives the derivation at `g1 ++ dd ++ g2` for the term that `shift c d` returns.
`shift` of Subst.lean threads a budget, so the hypothesis names the term of a successful run.
`Weakening.shiftOkPure` states that this term is the raise alone.
It states docs/metatheory.md section 7 lines 147 to 170.
-/
theorem weakening_shift (g1 dd g2 : List Ty) (c d fuel remaining : Nat) (t t' : Term) (b : Ty)
    (typed : HasType (g1 ++ g2) t b) (hc : g1.length = c) (hd : dd.length = d)
    (shifted : shift c d fuel t = Except.ok (t', remaining)) :
    HasType (g1 ++ dd ++ g2) t' b :=
  Eq.mp
    (congrArg (fun (z : Term) => HasType (g1 ++ dd ++ g2) z b)
      ((Weakening.shiftOkPure c d t fuel (t', remaining) shifted).trans
        ((congrArg (fun (n : Nat) => Weakening.shiftPure n d t) hc).symm.trans
          (congrArg (fun (n : Nat) => Weakening.shiftPure g1.length n t) hd).symm)).symm)
    (Weakening.weakeningPure (g1 ++ g2) t b typed g1 g2 rfl dd)
