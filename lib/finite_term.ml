type ty = Atoms of string list | Lan of (string * ty) list | Ran of (string * ty) list
type error =
  | Duplicate_label of string
  | Missing_label of string
  | Unexpected_label of string
  | Invalid_variable of int
  | Invalid_atom of string
  | Type_mismatch
  | Expected_lan
  | Expected_ran
  | Resource_exhausted

let ( let* ) = Result.bind

let rec unique = function
  | [] | [_] -> Ok ()
  | a :: (b :: _ as rest) ->
      if String.equal a b then Error (Duplicate_label a) else unique rest

let canonical entries =
  let entries = List.sort (fun (a, _) (b, _) -> String.compare a b) entries in
  let* () = unique (List.map fst entries) in
  Ok entries

let atoms labels =
  let labels = List.sort String.compare labels in
  let* () = unique labels in Ok (Atoms labels)
let lan entries = let* entries = canonical entries in Ok (Lan entries)
let ran entries = let* entries = canonical entries in Ok (Ran entries)

type term =
  | Var of int
  | Atom of string
  | Tag of string * term
  | Section of (string * term) list
  | Case of { scrutinee : term; scrutinee_type : ty;
              branches : (string * term) list }
  | Project of { section : term; section_type : ty; label : string }

let lookup label entries =
  List.assoc_opt label entries |> Option.to_result ~none:(Unexpected_label label)

let variable index entries =
  if index < 0 then Error (Invalid_variable index)
  else List.nth_opt entries index |> Option.to_result ~none:(Invalid_variable index)

let tick fuel = if fuel <= 0 then Error Resource_exhausted else Ok (fuel - 1)

(* Both lists are sorted, so matching is independent of source field order. The
   shared key names each aligned triple. *)
let rec align types terms =
  match types, terms with
  | [], [] -> Ok []
  | (key, _) :: _, [] -> Error (Missing_label key)
  | [], (key, _) :: _ -> Error (Unexpected_label key)
  | (key, ty) :: types, (label, term) :: terms ->
      let order = String.compare key label in
      if order < 0 then Error (Missing_label key)
      else if order > 0 then Error (Unexpected_label label)
      else let* rest = align types terms in Ok ((key, ty, term) :: rest)

let rec check_term fuel context term expected =
  let* fuel = tick fuel in
  match term with
  | Var index ->
      let* actual = variable index context in
      if actual = expected then Ok fuel else Error Type_mismatch
  | Atom atom ->
      (match expected with
       | Atoms labels ->
           if List.mem atom labels then Ok fuel else Error (Invalid_atom atom)
       | Lan _ | Ran _ -> Error Type_mismatch)
  | Tag (label, payload) ->
      (match expected with
       | Lan fibers ->
           let* ty = lookup label fibers in check_term fuel context payload ty
       | Atoms _ | Ran _ -> Error Expected_lan)
  | Section entries ->
      (match expected with
       | Ran fibers ->
           let* entries = canonical entries in
           let* pairs = align fibers entries in
           check_many fuel
             (fun fuel (_label, ty, term) -> check_term fuel context term ty) pairs
       | Atoms _ | Lan _ -> Error Expected_ran)
  | Case { scrutinee; scrutinee_type; branches } ->
      (match scrutinee_type with
       | Lan fibers ->
           let* branches = canonical branches in
           let* pairs = align fibers branches in
           let* fuel = check_term fuel context scrutinee scrutinee_type in
           check_many fuel
             (fun fuel (_label, payload_type, body) ->
               check_term fuel (payload_type :: context) body expected) pairs
       | Atoms _ | Ran _ -> Error Expected_lan)
  | Project { section; section_type; label } ->
      (match section_type with
       | Ran fibers ->
           let* actual = lookup label fibers in
           if actual <> expected then Error Type_mismatch
           else check_term fuel context section section_type
       | Atoms _ | Lan _ -> Error Expected_ran)
and check_many fuel check = function
  | [] -> Ok fuel
  | item :: rest -> let* fuel = check fuel item in check_many fuel check rest

let check ~fuel ~context term ty =
  let* _remaining = check_term fuel context term ty in Ok ()

(* The callback sees the number of Case payload binders crossed. Traversal
   preserves source field order and annotations; types contain no variables. *)
let rec map_variables fuel depth replace term =
  let* fuel = tick fuel in
  match term with
  | Var index -> replace fuel depth index
  | Atom _ -> Ok (term, fuel)
  | Tag (label, payload) ->
      let* payload, fuel = map_variables fuel depth replace payload in
      Ok (Tag (label, payload), fuel)
  | Section entries ->
      let* entries, fuel = map_entries fuel depth replace entries in
      Ok (Section entries, fuel)
  | Case { scrutinee; scrutinee_type; branches } ->
      let* scrutinee, fuel = map_variables fuel depth replace scrutinee in
      let* branches, fuel = map_entries fuel (depth + 1) replace branches in
      Ok (Case { scrutinee; scrutinee_type; branches }, fuel)
  | Project { section; section_type; label } ->
      let* section, fuel = map_variables fuel depth replace section in
      Ok (Project { section; section_type; label }, fuel)
and map_entries fuel depth replace = function
  | [] -> Ok ([], fuel)
  | (label, term) :: rest ->
      let* term, fuel = map_variables fuel depth replace term in
      let* rest, fuel = map_entries fuel depth replace rest in
      Ok ((label, term) :: rest, fuel)

(* Unchecked substitution of [replacement] for index zero in [body]. Callers
   must supply already checked inputs. It returns the remaining budget. *)
let substitute_core fuel replacement body =
  let replace fuel depth index =
    if index < depth then Ok (Var index, fuel)
    else if index > depth then Ok (Var (index - 1), fuel)
    else
      (* Only free variables of the replacement move under the body's binders.
         Binders inside the replacement retain their own indices. *)
      map_variables fuel 0
        (fun fuel cutoff index ->
          Ok (Var (if index < cutoff then index else index + depth), fuel))
        replacement
  in
  map_variables fuel 0 replace body

let substitute ~fuel ~context ~replacement ~replacement_type body expected =
  let* fuel = check_term fuel context replacement replacement_type in
  let* fuel = check_term fuel (replacement_type :: context) body expected in
  let* term, _remaining = substitute_core fuel replacement body in Ok term

(* One unit per visited node, as in [map_variables] and [evaluate]. A Case of a
   Tag also pays [substitute_core] and the reduction of the substituted body.
   The expected type and the annotations direct every step, so reduction needs
   no context: this fragment is nondependent. *)
let rec reduce fuel term expected =
  let* fuel = tick fuel in
  match term with
  | Var _ | Atom _ -> Ok (term, fuel)
  | Tag (label, payload) ->
      (match expected with
       | Lan fibers ->
           let* fiber = lookup label fibers in
           let* payload, fuel = reduce fuel payload fiber in
           Ok (Tag (label, payload), fuel)
       | Atoms _ | Ran _ -> Error Expected_lan)
  | Section entries ->
      (match expected with
       | Ran fibers ->
           let* entries = canonical entries in
           let* fields = align fibers entries in
           let* entries, fuel = reduce_fields fuel fields in
           Ok (Section entries, fuel)
       | Atoms _ | Lan _ -> Error Expected_ran)
  | Case { scrutinee; scrutinee_type; branches } ->
      (match scrutinee_type with
       | Lan fibers ->
           let* branches = canonical branches in
           let* scrutinee, fuel = reduce fuel scrutinee scrutinee_type in
           (match scrutinee with
            | Tag (label, payload) ->
                let* body = lookup label branches in
                let* body, fuel = substitute_core fuel payload body in
                reduce fuel body expected
            | Var _ | Case _ | Project _ ->
                let* fields = align fibers branches in
                let* branches, fuel = reduce_branches fuel fields expected in
                Ok (Case { scrutinee; scrutinee_type; branches }, fuel)
            (* Checking rejects these scrutinees. The error keeps [reduce] total. *)
            | Atom _ | Section _ -> Error Expected_lan)
       | Atoms _ | Ran _ -> Error Expected_lan)
  | Project { section; section_type; label } ->
      (match section_type with
       | Ran fibers ->
           let* actual = lookup label fibers in
           if actual <> expected then Error Type_mismatch
           else
             let* section, fuel = reduce fuel section section_type in
             (match section with
              | Section entries -> let* field = lookup label entries in Ok (field, fuel)
              | Var _ | Case _ | Project _ ->
                  Ok (Project { section; section_type; label }, fuel)
              | Atom _ | Tag _ -> Error Expected_ran)
       | Atoms _ | Lan _ -> Error Expected_ran)
and reduce_fields fuel = function
  | [] -> Ok ([], fuel)
  | (label, fiber, term) :: rest ->
      let* term, fuel = reduce fuel term fiber in
      let* rest, fuel = reduce_fields fuel rest in
      Ok ((label, term) :: rest, fuel)
(* Each aligned fiber binds the payload at index zero of its branch. That fiber
   does not direct the reduction of the body; the expected type does. *)
and reduce_branches fuel fields expected =
  match fields with
  | [] -> Ok ([], fuel)
  | (label, _fiber, body) :: rest ->
      let* body, fuel = reduce fuel body expected in
      let* rest, fuel = reduce_branches fuel rest expected in
      Ok ((label, body) :: rest, fuel)

let normalize ~fuel ~context term expected =
  let* fuel = check_term fuel context term expected in
  let* term, _remaining = reduce fuel term expected in Ok term

type value =
  | Atom_value of string
  | Tag_value of string * value
  | Section_value of (string * value) list

let rec evaluate fuel environment term =
  let* fuel = tick fuel in
  match term with
  | Var index -> let* value = variable index environment in Ok (value, fuel)
  | Atom atom -> Ok (Atom_value atom, fuel)
  | Tag (label, payload) ->
      let* value, fuel = evaluate fuel environment payload in
      Ok (Tag_value (label, value), fuel)
  | Section entries ->
      let* entries = canonical entries in
      let* values, fuel = evaluate_entries fuel environment entries in
      Ok (Section_value values, fuel)
  | Case { scrutinee; scrutinee_type = _; branches } ->
      let* value, fuel = evaluate fuel environment scrutinee in
      (match value with
       | Tag_value (label, payload) ->
           let* body = lookup label branches in
           evaluate fuel (payload :: environment) body
       | Atom_value _ | Section_value _ -> Error Expected_lan)
  | Project { section; section_type = _; label } ->
      let* value, fuel = evaluate fuel environment section in
      (match value with
       | Section_value entries ->
           let* value = lookup label entries in Ok (value, fuel)
       | Atom_value _ | Tag_value _ -> Error Expected_ran)
and evaluate_entries fuel environment = function
  | [] -> Ok ([], fuel)
  | (label, term) :: rest ->
      let* value, fuel = evaluate fuel environment term in
      let* values, fuel = evaluate_entries fuel environment rest in
      Ok ((label, value) :: values, fuel)

let run ~fuel term ty =
  let* fuel = check_term fuel [] term ty in
  let* value, _remaining = evaluate fuel [] term in Ok value
