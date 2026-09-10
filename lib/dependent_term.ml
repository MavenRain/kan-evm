include Dependent_core

(* These reducers are internal. Public callers first validate contexts, types
   and terms; checker comparisons use them only on formed types and indices. *)
let rec reduce_type fuel ty =
  let* fuel = tick fuel in
  match ty with
  | Atoms labels ->
      let* labels = canonical_labels labels in Ok (Atoms labels, fuel)
  | Nat -> Ok (Nat, fuel)
  | Vec (element, length) ->
      let* element, fuel = reduce_type fuel element in
      let* length, fuel = reduce_term fuel length in
      Ok (Vec (element, length), fuel)
  | Pi (domain, codomain) ->
      let* domain, fuel = reduce_type fuel domain in
      let* codomain, fuel = reduce_type fuel codomain in
      Ok (Pi (domain, codomain), fuel)
  | Sigma (domain, codomain) ->
      let* domain, fuel = reduce_type fuel domain in
      let* codomain, fuel = reduce_type fuel codomain in
      Ok (Sigma (domain, codomain), fuel)
and reduce_term fuel term =
  let* fuel = tick fuel in
  match term with
  | Var index ->
      if index < 0 then Error (Invalid_variable index) else Ok (term, fuel)
  | Atom _ | Zero | Nil -> Ok (term, fuel)
  | Succ value ->
      let* value, fuel = reduce_term fuel value in Ok (Succ value, fuel)
  | Cons { length; head; tail } ->
      let* length, fuel = reduce_term fuel length in
      let* head, fuel = reduce_term fuel head in
      let* tail, fuel = reduce_term fuel tail in
      Ok (Cons { length; head; tail }, fuel)
  | Lam body ->
      let* body, fuel = reduce_term fuel body in Ok (Lam body, fuel)
  | App { fn; domain; codomain; argument } ->
      let* domain, fuel = reduce_type fuel domain in
      let* codomain, fuel = reduce_type fuel codomain in
      let* fn, fuel = reduce_term fuel fn in
      let* argument, fuel = reduce_term fuel argument in
      (match fn with
       | Lam body ->
           let* body, fuel = subst_term fuel [argument] body in
           reduce_term fuel body
       | Var _ | App _ | Split _ ->
           Ok (App { fn; domain; codomain; argument }, fuel)
       | Atom _ | Zero | Succ _ | Nil | Cons _ | Pair _ -> Error Expected_pi)
  | Pair (first, second) ->
      let* first, fuel = reduce_term fuel first in
      let* second, fuel = reduce_term fuel second in
      Ok (Pair (first, second), fuel)
  | Split { pair; domain; codomain; motive; body } ->
      let* domain, fuel = reduce_type fuel domain in
      let* codomain, fuel = reduce_type fuel codomain in
      let* motive, fuel = reduce_type fuel motive in
      let* pair, fuel = reduce_term fuel pair in
      (match pair with
       | Pair (first, second) ->
           let* body, fuel = subst_term fuel [second; first] body in
           reduce_term fuel body
       | Var _ | App _ | Split _ ->
           let* body, fuel = reduce_term fuel body in
           Ok (Split { pair; domain; codomain; motive; body }, fuel)
       | Atom _ | Zero | Succ _ | Nil | Cons _ | Lam _ -> Error Expected_sigma)

let equal_types fuel left right =
  let* left, fuel = reduce_type fuel left in
  let* right, fuel = reduce_type fuel right in
  if left = right then Ok fuel else Error Type_mismatch

let equal_indices fuel left right =
  let* left, fuel = reduce_term fuel left in
  let* right, fuel = reduce_term fuel right in
  if left = right then Ok fuel else Error Type_mismatch

(* Entries are stored in their older tail. Entry i therefore crosses i + 1
   binders when it is used in the full context, including its own binder. *)
let variable_type fuel context index =
  if index < 0 || index = max_int then Error (Invalid_variable index)
  else
    let* ty = List.nth_opt context index
      |> Option.to_result ~none:(Invalid_variable index) in
    shift_type fuel (index + 1) 0 ty

(* C starts under one pair binder. Insert the two component binders below it
   before replacing that pair with (1, 0). Older context entries remain free. *)
let split_body_type fuel motive =
  let* motive, fuel = shift_type fuel 2 1 motive in
  subst_type fuel [Pair (Var 1, Var 0)] motive

let rec form_type fuel context ty =
  let* fuel = tick fuel in
  match ty with
  | Atoms labels ->
      let* _labels = canonical_labels labels in Ok fuel
  | Nat -> Ok fuel
  | Vec (element, length) ->
      let* fuel = form_type fuel context element in
      check_term fuel context length Nat
  | Pi (domain, codomain) | Sigma (domain, codomain) ->
      let* fuel = form_type fuel context domain in
      form_type fuel (domain :: context) codomain
and check_term fuel context term expected =
  let* fuel = tick fuel in
  match term with
  | Var index ->
      let* actual, fuel = variable_type fuel context index in
      equal_types fuel actual expected
  | Atom atom ->
      (match expected with
       | Atoms labels ->
           if List.mem atom labels then Ok fuel else Error (Invalid_atom atom)
       | Nat | Vec _ | Pi _ | Sigma _ -> Error Type_mismatch)
  | Zero ->
      (match expected with
       | Nat -> Ok fuel
       | Atoms _ | Vec _ | Pi _ | Sigma _ -> Error Expected_nat)
  | Succ value ->
      (match expected with
       | Nat -> check_term fuel context value Nat
       | Atoms _ | Vec _ | Pi _ | Sigma _ -> Error Expected_nat)
  | Nil ->
      (match expected with
       | Vec (_element, length) -> equal_indices fuel Zero length
       | Atoms _ | Nat | Pi _ | Sigma _ -> Error Expected_vec)
  | Cons { length; head; tail } ->
      (match expected with
       | Vec (element, expected_length) ->
           let* fuel = check_term fuel context length Nat in
           let* fuel = equal_indices fuel (Succ length) expected_length in
           let* fuel = check_term fuel context head element in
           check_term fuel context tail (Vec (element, length))
       | Atoms _ | Nat | Pi _ | Sigma _ -> Error Expected_vec)
  | Lam body ->
      (match expected with
       | Pi (domain, codomain) ->
           check_term fuel (domain :: context) body codomain
       | Atoms _ | Nat | Vec _ | Sigma _ -> Error Expected_pi)
  | App { fn; domain; codomain; argument } ->
      let annotation = Pi (domain, codomain) in
      let* fuel = form_type fuel context annotation in
      let* fuel = check_term fuel context fn annotation in
      let* fuel = check_term fuel context argument domain in
      let* actual, fuel = subst_type fuel [argument] codomain in
      equal_types fuel actual expected
  | Pair (first, second) ->
      (match expected with
       | Sigma (domain, codomain) ->
           let* fuel = check_term fuel context first domain in
           let* actual, fuel = subst_type fuel [first] codomain in
           check_term fuel context second actual
       | Atoms _ | Nat | Vec _ | Pi _ -> Error Expected_sigma)
  | Split { pair; domain; codomain; motive; body } ->
      let annotation = Sigma (domain, codomain) in
      let* fuel = form_type fuel context annotation in
      let* fuel = form_type fuel (annotation :: context) motive in
      let* fuel = check_term fuel context pair annotation in
      let* body_type, fuel = split_body_type fuel motive in
      let* fuel = check_term fuel (codomain :: domain :: context) body body_type in
      let* actual, fuel = subst_type fuel [pair] motive in
      equal_types fuel actual expected

let rec check_context fuel = function
  | [] -> Ok fuel
  | ty :: older ->
      let* fuel = tick fuel in
      let* fuel = check_context fuel older in
      form_type fuel older ty

let prepare fuel context expected =
  let* fuel = check_context fuel context in
  form_type fuel context expected

let check_type ~fuel ~context ty =
  let* _remaining = prepare fuel context ty in Ok ()

let check ~fuel ~context term expected =
  let* fuel = prepare fuel context expected in
  let* _remaining = check_term fuel context term expected in Ok ()

let normalize_type ~fuel ~context ty =
  let* fuel = prepare fuel context ty in
  let* ty, _remaining = reduce_type fuel ty in Ok ty

let normalize_core fuel context term expected =
  let* fuel = check_term fuel context term expected in
  reduce_term fuel term

let normalize ~fuel ~context term expected =
  let* fuel = prepare fuel context expected in
  let* term, _remaining = normalize_core fuel context term expected in Ok term

let convert_types ~fuel ~context left right =
  let* fuel = check_context fuel context in
  let* fuel = form_type fuel context left in
  let* left, fuel = reduce_type fuel left in
  let* fuel = form_type fuel context right in
  let* right, _remaining = reduce_type fuel right in
  Ok (left = right)

let convert ~fuel ~context left right expected =
  let* fuel = prepare fuel context expected in
  let* left, fuel = normalize_core fuel context left expected in
  let* right, _remaining = normalize_core fuel context right expected in
  Ok (left = right)

let prepare_substitution fuel context replacement replacement_type =
  let* fuel = prepare fuel context replacement_type in
  check_term fuel context replacement replacement_type

let substitute ~fuel ~context ~replacement ~replacement_type body expected =
  let* fuel = prepare_substitution fuel context replacement replacement_type in
  let extended = replacement_type :: context in
  let* fuel = form_type fuel extended expected in
  let* fuel = check_term fuel extended body expected in
  let* body, _remaining = subst_term fuel [replacement] body in Ok body

let substitute_type ~fuel ~context ~replacement ~replacement_type ty =
  let* fuel = prepare_substitution fuel context replacement replacement_type in
  let* fuel = form_type fuel (replacement_type :: context) ty in
  let* ty, _remaining = subst_type fuel [replacement] ty in Ok ty
