type ty =
  | Atoms of string list
  | Nat
  | Vec of ty * term
  | Pi of ty * ty
  | Sigma of ty * ty
and term =
  | Var of int
  | Atom of string
  | Zero
  | Succ of term
  | Nil
  | Cons of { length : term; head : term; tail : term }
  | Lam of term
  | App of { fn : term; domain : ty; codomain : ty; argument : term }
  | Pair of term * term
  | Split of { pair : term; domain : ty; codomain : ty;
               motive : ty; body : term }

type error =
  | Duplicate_label of string
  | Invalid_variable of int
  | Invalid_atom of string
  | Type_mismatch
  | Expected_pi
  | Expected_sigma
  | Expected_nat
  | Expected_vec
  | Resource_exhausted

let ( let* ) = Result.bind

let tick fuel =
  if fuel <= 0 then Error Resource_exhausted else Ok (fuel - 1)

let canonical_labels labels =
  let sorted = List.sort String.compare labels in
  let rec check = function
    | [] | [_] -> Ok sorted
    | left :: ((right :: _) as rest) ->
        if String.equal left right then Error (Duplicate_label left)
        else check rest
  in
  check sorted

let enter_binders depth count =
  if depth < 0 || depth > max_int - count then Error (Invalid_variable depth)
  else Ok (depth + count)

(* A variable visitor receives the budget after the variable node was metered.
   Every annotation uses the same traversal and binder depths as its term. *)
let rec walk_term visit fuel depth term =
  let* fuel = tick fuel in
  match term with
  | Var index ->
      if index < 0 then Error (Invalid_variable index)
      else visit fuel depth index
  | Atom label -> Ok (Atom label, fuel)
  | Zero -> Ok (Zero, fuel)
  | Succ term ->
      let* term, fuel = walk_term visit fuel depth term in
      Ok (Succ term, fuel)
  | Nil -> Ok (Nil, fuel)
  | Cons { length; head; tail } ->
      let* length, fuel = walk_term visit fuel depth length in
      let* head, fuel = walk_term visit fuel depth head in
      let* tail, fuel = walk_term visit fuel depth tail in
      Ok (Cons { length; head; tail }, fuel)
  | Lam body ->
      let* body_depth = enter_binders depth 1 in
      let* body, fuel = walk_term visit fuel body_depth body in
      Ok (Lam body, fuel)
  | App { fn; domain; codomain; argument } ->
      let* fn, fuel = walk_term visit fuel depth fn in
      let* domain, fuel = walk_type visit fuel depth domain in
      let* codomain_depth = enter_binders depth 1 in
      let* codomain, fuel = walk_type visit fuel codomain_depth codomain in
      let* argument, fuel = walk_term visit fuel depth argument in
      Ok (App { fn; domain; codomain; argument }, fuel)
  | Pair (first, second) ->
      let* first, fuel = walk_term visit fuel depth first in
      let* second, fuel = walk_term visit fuel depth second in
      Ok (Pair (first, second), fuel)
  | Split { pair; domain; codomain; motive; body } ->
      let* pair, fuel = walk_term visit fuel depth pair in
      let* domain, fuel = walk_type visit fuel depth domain in
      let* family_depth = enter_binders depth 1 in
      let* codomain, fuel = walk_type visit fuel family_depth codomain in
      let* motive, fuel = walk_type visit fuel family_depth motive in
      let* body_depth = enter_binders depth 2 in
      let* body, fuel = walk_term visit fuel body_depth body in
      Ok (Split { pair; domain; codomain; motive; body }, fuel)
and walk_type visit fuel depth ty =
  let* fuel = tick fuel in
  match ty with
  | Atoms labels -> Ok (Atoms labels, fuel)
  | Nat -> Ok (Nat, fuel)
  | Vec (element, length) ->
      let* element, fuel = walk_type visit fuel depth element in
      let* length, fuel = walk_term visit fuel depth length in
      Ok (Vec (element, length), fuel)
  | Pi (domain, codomain) ->
      let* domain, fuel = walk_type visit fuel depth domain in
      let* codomain_depth = enter_binders depth 1 in
      let* codomain, fuel = walk_type visit fuel codomain_depth codomain in
      Ok (Pi (domain, codomain), fuel)
  | Sigma (domain, codomain) ->
      let* domain, fuel = walk_type visit fuel depth domain in
      let* codomain_depth = enter_binders depth 1 in
      let* codomain, fuel = walk_type visit fuel codomain_depth codomain in
      Ok (Sigma (domain, codomain), fuel)

let shift_variable amount cutoff fuel depth index =
  match () with
  | () when index < depth || index - depth < cutoff -> Ok (Var index, fuel)
  | () when amount >= 0 && index > max_int - amount ->
      Error (Invalid_variable index)
  | () when amount < 0 && amount < -index -> Error (Invalid_variable index)
  | () -> Ok (Var (index + amount), fuel)

let shift_term fuel amount cutoff term =
  if cutoff < 0 then Error (Invalid_variable cutoff)
  else walk_term (shift_variable amount cutoff) fuel 0 term

let shift_type fuel amount cutoff ty =
  if cutoff < 0 then Error (Invalid_variable cutoff)
  else walk_type (shift_variable amount cutoff) fuel 0 ty

let substitute_variable replacements count fuel depth index =
  match () with
  | () when index < depth -> Ok (Var index, fuel)
  | () when index - depth >= count -> Ok (Var (index - count), fuel)
  | () ->
      let* replacement =
        Option.to_result ~none:(Invalid_variable index)
          (List.nth_opt replacements (index - depth))
      in
      shift_term fuel depth 0 replacement

let subst_term fuel replacements term =
  walk_term
    (substitute_variable replacements (List.length replacements)) fuel 0 term

let subst_type fuel replacements ty =
  walk_type
    (substitute_variable replacements (List.length replacements)) fuel 0 ty
