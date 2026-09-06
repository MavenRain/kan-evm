type error =
  | Duplicate of string
  | Missing of string
  | Unexpected of string
  | Wrong_target of string
  | Invalid_atom of string

type diagram = {
  codomain : string list;
  mapping : (string * string) list;
  fibers : (string * string list) list;
}
type lan_value = { source : string; atom : string }
type ran_value = Section of (string * string) list

let ( let* ) = Result.bind

let rec unique seen = function
  | [] -> Ok ()
  | key :: rest ->
      if List.mem key seen then Error (Duplicate key)
      else unique (key :: seen) rest

let rec check_all check = function
  | [] -> Ok ()
  | item :: rest -> let* () = check item in check_all check rest

let require_member choices key =
  if List.mem key choices then Ok () else Error (Unexpected key)

let lookup key entries =
  List.assoc_opt key entries |> Option.to_result ~none:(Missing key)

let exact_keys expected entries =
  let keys = List.map fst entries in
  let* () = unique [] keys in
  let* () = check_all (require_member expected) keys in
  check_all
    (fun key -> if List.mem key keys then Ok () else Error (Missing key))
    expected

let make ~domain ~codomain ~mapping ~fibers =
  let* () = unique [] domain in
  let* () = unique [] codomain in
  let* () = exact_keys domain mapping in
  let* () = exact_keys domain fibers in
  let* () = check_all (fun (_, b) -> require_member codomain b) mapping in
  let* () = check_all (fun (_, atoms) -> unique [] atoms) fibers in
  Ok { codomain; mapping; fibers }

let check_atom diagram source atom =
  let* atoms = lookup source diagram.fibers in
  if List.mem atom atoms then Ok () else Error (Invalid_atom atom)

let lan_intro diagram ~target ~source atom =
  let* () = require_member diagram.codomain target in
  let* actual = lookup source diagram.mapping in
  if not (String.equal actual target) then Error (Wrong_target source)
  else
    let* () = check_atom diagram source atom in
    Ok { source; atom }

let lan_elim value branch = branch value.source value.atom

let ran_intro diagram ~target entries =
  let* () = require_member diagram.codomain target in
  let sources = List.filter_map
    (fun (a, b) -> if String.equal b target then Some a else None)
    diagram.mapping in
  let* () = exact_keys sources entries in
  let* () = check_all (fun (a, atom) -> check_atom diagram a atom) entries in
  Ok (Section entries)

let ran_elim (Section entries) ~source = lookup source entries

let string_of_error = function
  | Duplicate key -> "duplicate: " ^ key
  | Missing key -> "missing: " ^ key
  | Unexpected key -> "unexpected: " ^ key
  | Wrong_target key -> "wrong target for source: " ^ key
  | Invalid_atom atom -> "invalid atom: " ^ atom
