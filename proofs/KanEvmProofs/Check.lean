import KanEvmProofs.Syntax

/-! # Type checker of the finite fragment

This module mirrors `check_term` and its helpers at lib/finite_term.ml lines 40 to 108.
It holds the fuel discipline of decision S2-D4 and the gas discipline of decision S2-D5.
`checkCore` carries the structural gas parameter, and `checkFields` and `checkBranches` of the same `mutual` block carry it too, per decision
S2-D5.
-/

/-- `tick` mirrors the OCaml `tick` at lib/finite_term.ml line 47.
It spends one unit of the budget and reports `Err.resourceExhausted` at an empty budget.
The OCaml test `fuel <= 0` becomes the test `fuel = 0` over `Nat`.
Decision S2-D4 makes this function the only charge point of the module.
-/
def tick (fuel : Nat) : Res Nat :=
  if fuel = 0 then .error .resourceExhausted else .ok (fuel - 1)

/-- `lookup` mirrors the OCaml `lookup` at lib/finite_term.ml lines 40 and 41.
It finds the first entry that carries the given label.
A miss becomes `Err.unexpectedLabel`, as decision S2-D3 requires of a total helper.
`List.lookup` replaces `List.assoc_opt` and `Option.elim` replaces `Option.to_result`.
The OCaml function is polymorphic in the payload, so this one is polymorphic too.
-/
def lookup {α : Type} (label : String) (entries : List (String × α)) : Res α :=
  (entries.lookup label).elim (.error (.unexpectedLabel label)) .ok

/-- `variable` mirrors the OCaml `variable` at lib/finite_term.ml lines 43 to 45.
It reads the context at the given index.
A miss becomes `Err.invalidVariable`, as decision S2-D3 requires of a total helper.
The OCaml guard for a negative index has no image over `Nat`, as Syntax.lean records.
The name is a Lean keyword, so the declaration takes the guillemet form.
-/
def «variable» (index : Nat) (entries : List Ty) : Res Ty :=
  entries[index]?.elim (.error (.invalidVariable index)) .ok

/-- `align` mirrors the OCaml `align` at lib/finite_term.ml lines 51 to 60.
Both lists hold the ascending label order, so one walk pairs each fiber with its field.
A label of the type side alone becomes `Err.missingLabel`.
A label of the term side alone becomes `Err.unexpectedLabel`.
The shared label names each aligned triple, as the comment at lines 49 and 50 states.
-/
def align : List (String × Ty) → List (String × Term) → Res (List (String × Ty × Term))
  | [], [] => .ok []
  | (key, _fiber) :: _rest, [] => .error (.missingLabel key)
  | [], (key, _field) :: _rest => .error (.unexpectedLabel key)
  | (key, fiber) :: types, (label, field) :: terms =>
      match compare key label with
      | .lt => .error (.missingLabel key)
      | .gt => .error (.unexpectedLabel label)
      | .eq => align types terms >>= fun rest => .ok ((key, fiber, field) :: rest)

/-- `insertEntry` puts one entry into a list that already holds the ascending label order.
`insertEntry` is the step of `sortEntries`, which mirrors the sort at lib/finite_term.ml line 21.
It repeats `insertFiber` of Syntax.lean over an arbitrary payload.
-/
def insertEntry {α : Type} (entry : String × α) : List (String × α) → List (String × α)
  | [] => [entry]
  | head :: rest =>
      if labelLe entry.1 head.1 then entry :: head :: rest else head :: insertEntry entry rest

/-- `sortEntries` sorts an entry list into ascending label order.
`sortEntries` mirrors `List.sort` at lib/finite_term.ml line 21 over an arbitrary payload.
Decision S2-D5 names `List.mergeSort`, and Syntax.lean records why a structural sort replaces it.
-/
def sortEntries {α : Type} : List (String × α) → List (String × α)
  | [] => []
  | head :: rest => insertEntry head (sortEntries rest)

/-- `canonicalEntries` mirrors the OCaml `canonical` at lib/finite_term.ml lines 20 to 23.
The OCaml function is polymorphic in the payload, and lines 81 and 89 call it on a term list.
`canonical` of Syntax.lean covers the fiber list, so this function covers the term list.
It sorts the entries into ascending label order, then it rejects a repeated label.
-/
def canonicalEntries {α : Type} (entries : List (String × α)) : Res (List (String × α)) :=
  let sorted := sortEntries entries
  unique (sorted.map Prod.fst) >>= fun (_ok : Unit) => .ok sorted

mutual
/-- `size` counts the term nodes of one term.
The term shapes are the ones at lib/finite_term.ml lines 31 to 38, and each node counts one unit.
`size` is the measure of Lemma2 of the theorem inventory, which pairs one tick with one node.
-/
def size : Term → Nat
  | .var .. => 1
  | .atom .. => 1
  | .tag _ payload => 1 + size payload
  | .«section» fields => 1 + sizeEntries fields
  | .«case» scrutinee _ branches => 1 + size scrutinee + sizeEntries branches
  | .project field .. => 1 + size field

/-- `sizeEntries` counts the term nodes of an entry list. `sizeEntries` is the list partner of `size` for the nested inductive of decision
S2-D1. `sizeEntries` is the list partner of `size` over the term shape of lib/finite_term.ml lines 31 to 38, and it feeds the measure
`size(t)` of docs/metatheory.md lines 92 to 96.
-/
def sizeEntries : List (String × Term) → Nat
  | [] => 0
  | (_label, field) :: rest => size field + sizeEntries rest
end

mutual
/-- `checkCore` mirrors the OCaml `check_term` at lib/finite_term.ml lines 62 to 105.
It ticks once, then it reads the term and the expected type.
Decision S2-D5 adds the structural gas parameter, since a sorted entry list is no sublist.
Each nested call passes `gas - 1`, and an empty gas reports `Err.resourceExhausted`.
The public `check` supplies `2 * fuel + 2` gas, which no run of this function reaches.
-/
def checkCore (gas fuel : Nat) (ctx : List Ty) (t : Term) (expected : Ty) : Res Nat :=
  match gas with
  | 0 => .error .resourceExhausted
  | gasPred + 1 =>
      tick fuel >>= fun fuel =>
        match t with
        | .var index =>
            «variable» index ctx >>= fun actual =>
              if actual == expected then .ok fuel else .error .typeMismatch
        | .atom name =>
            match expected with
            | .atoms labels =>
                if labels.contains name then .ok fuel else .error (.invalidAtom name)
            | .lan .. => .error .typeMismatch
            | .ran .. => .error .typeMismatch
        | .tag label payload =>
            match expected with
            | .lan fibers =>
                lookup label fibers >>= fun fiber =>
                  checkCore gasPred fuel ctx payload fiber
            | .atoms .. => .error .expectedLan
            | .ran .. => .error .expectedLan
        | .«section» entries =>
            match expected with
            | .ran fibers =>
                canonicalEntries entries >>= fun sorted =>
                  align fibers sorted >>= fun pairs =>
                    checkFields gasPred fuel ctx pairs
            | .atoms .. => .error .expectedRan
            | .lan .. => .error .expectedRan
        | .«case» scrutinee scrutineeType branches =>
            match scrutineeType with
            | .lan fibers =>
                canonicalEntries branches >>= fun sorted =>
                  align fibers sorted >>= fun pairs =>
                    checkCore gasPred fuel ctx scrutinee scrutineeType >>= fun fuel =>
                      checkBranches gasPred fuel ctx pairs expected
            | .atoms .. => .error .expectedLan
            | .ran .. => .error .expectedLan
        | .project field sectionType label =>
            match sectionType with
            | .ran fibers =>
                lookup label fibers >>= fun actual =>
                  if actual == expected then checkCore gasPred fuel ctx field sectionType
                  else .error .typeMismatch
            | .atoms .. => .error .expectedRan
            | .lan .. => .error .expectedRan

/-- `checkFields` replaces the higher order `check_many` at lib/finite_term.ml lines 103 to 105.
It walks the aligned field list of the section rule at lines 78 to 85.
Each field runs at the fiber type of its own label and at the unchanged context.
Decision S2-D5 keeps this helper first order, and the gas of each nested call is `gas - 1`.
-/
def checkFields (gas fuel : Nat) (ctx : List Ty) (pairs : List (String × Ty × Term)) : Res Nat :=
  match gas with
  | 0 => .error .resourceExhausted
  | gasPred + 1 =>
      match pairs with
      | [] => .ok fuel
      | (_label, fiber, field) :: rest =>
          checkCore gasPred fuel ctx field fiber >>= fun fuel =>
            checkFields gasPred fuel ctx rest

/-- `checkBranches` replaces the higher order `check_many` at lib/finite_term.ml lines 103 to 105.
It walks the aligned branch list of the case rule at lines 86 to 95.
Each body runs at the expected type and at the context that the payload type extends.
Decision S2-D5 keeps this helper first order, and the gas of each nested call is `gas - 1`.
-/
def checkBranches (gas fuel : Nat) (ctx : List Ty) (pairs : List (String × Ty × Term))
    (expected : Ty) : Res Nat :=
  match gas with
  | 0 => .error .resourceExhausted
  | gasPred + 1 =>
      match pairs with
      | [] => .ok fuel
      | (_label, payloadType, body) :: rest =>
          checkCore gasPred fuel (payloadType :: ctx) body expected >>= fun fuel =>
            checkBranches gasPred fuel ctx rest expected
end

/-- `check` mirrors the OCaml `check` at lib/finite_term.ml lines 107 and 108.
It runs `checkCore` and it drops the remaining budget, as decision S2-D4 states.
The gas is `2 * fuel + 2`, per decision S2-D5, since one chain spends at most two gas per unit.
-/
def check (fuel : Nat) (ctx : List Ty) (t : Term) (expected : Ty) : Res Unit :=
  checkCore (2 * fuel + 2) fuel ctx t expected >>= fun (_remaining : Nat) => .ok ()
