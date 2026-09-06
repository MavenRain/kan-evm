open Finite_term

let ( let* ) = Result.bind
let ensure condition message = if condition then Ok () else Error message
let get result = Result.map_error (fun _ -> "unexpected substitution/checking error") result
let rejects expected = Result.fold
  ~error:(fun actual -> ensure (actual = expected) "wrong rejection")
  ~ok:(fun _ -> Error "accepted invalid input")
let rec each f = function
  | [] -> Ok ()
  | x :: rest -> let* () = f x in each f rest

let tests () =
  let* a = get (atoms ["x"; "y"]) in
  let* b = get (atoms ["z"]) in
  let* sum = get (lan ["k", a]) in
  let* pair = get (ran ["local", a; "outer", a; "target", a]) in
  let subst context replacement body ty =
    get (substitute ~fuel:100000 ~context ~replacement ~replacement_type:a body ty)
  in
  let case scrutinee body =
    Case { scrutinee; scrutinee_type = sum; branches = ["k", body] }
  in
  (* The replacement has both its own bound variable and a free variable. *)
  let replacement = case (Tag ("k", Var 0))
    (case (Tag ("k", Var 0)) (Var 2)) in
  let body = case (Tag ("k", Var 0))
    (Section ["target", Var 1; "local", Var 0; "outer", Var 2]) in
  let shifted = case (Tag ("k", Var 1))
    (case (Tag ("k", Var 0)) (Var 3)) in
  let expected = case (Tag ("k", replacement))
    (Section ["target", shifted; "local", Var 0; "outer", Var 1]) in
  let* actual = subst [a] replacement body pair in
  let* () = ensure (actual = expected) "nested substitution captured a variable or changed field order" in
  let* () = get (check ~fuel:1000 ~context:[a] actual pair) in
  let* () = each (fun (body, expected) ->
    let* actual = subst [a; a] (Var 1) body a in
    ensure (actual = expected) "wrong context entry removed")
    [Var 0, Var 1; Var 1, Var 0; Var 2, Var 1] in
  let* unit_ty = get (ran []) in
  let* empty_ty = get (lan []) in
  let* empty = subst [] (Atom "x") (Section []) unit_ty in
  let* () = ensure (empty = Section []) "empty section changed" in
  let* absurd = subst [empty_ty] (Atom "x")
    (Case { scrutinee = Var 1; scrutinee_type = empty_ty; branches = [] }) b in
  let* () = get (check ~fuel:100 ~context:[empty_ty] absurd b) in
  let call fuel replacement body =
    substitute ~fuel ~context:[] ~replacement ~replacement_type:a body a in
  let* () = rejects (Invalid_atom "z") (call 100 (Atom "z") (Atom "x")) in
  let* () = rejects (Invalid_variable 0) (call 100 (Var 0) (Atom "x")) in
  let* () = rejects (Invalid_variable 1) (call 100 (Atom "x") (Var 1)) in
  let* () = rejects (Invalid_variable (-1)) (call 100 (Atom "x") (Var (-1))) in
  let* () = rejects (Invalid_atom "z")
    (call 100 (Atom "x") (case (Tag ("k", Atom "y")) (Atom "z"))) in
  let* () = each (fun fuel -> rejects Resource_exhausted (call fuel (Atom "x") (Var 0)))
    [-1; 0; 1; 2; 3] in
  let* _ = get (call 4 (Atom "x") (Var 0)) in
  let* () = rejects Resource_exhausted (call 2 (Atom "x") (Atom "y")) in
  let* _ = get (call 3 (Atom "x") (Atom "y")) in
  let* two = get (ran ["a", a; "b", a]) in
  let duplicate fuel = substitute ~fuel ~context:[] ~replacement:(Atom "x")
    ~replacement_type:a (Section ["b", Var 0; "a", Var 0]) two in
  let* () = rejects Resource_exhausted (duplicate 8) in
  let* _ = get (duplicate 9) in
  (* A bounded, type-directed corpus. Close outer variables through Case
     evaluation, independently of the substitution implementation. *)
  let variables context ty = List.filter_map
    (fun (index, actual) -> if actual = ty then Some (Var index) else None)
    (List.mapi (fun index ty -> index, ty) context) in
  let base context ty = variables context ty @
    (match () with
     | () when ty = a -> [Atom "x"; Atom "y"]
     | () when ty = b -> [Atom "z"]
     | () when ty = sum -> [Tag ("k", Atom "x"); Tag ("k", Atom "y")]
     | () when ty = two -> [Section ["a", Atom "x"; "b", Atom "y"]]
     | () -> []) in
  let terms context ty =
    base context ty @
    List.concat_map (fun scrutinee ->
      List.map (case scrutinee) (base (a :: context) ty)) (base context sum) @
    (match () with
     | () when ty = a -> List.map (fun section ->
         Project { section; section_type = two; label = "b" }) (base context two)
     | () when ty = sum -> List.map (fun t -> Tag ("k", t)) (base context a)
     | () when ty = two -> List.concat_map (fun left ->
         List.map (fun right -> Section ["b", right; "a", left]) (base context a))
         (base context a)
     | () -> []) in
  let rec close bindings body = match bindings with
    | [] -> body
    | (ty, replacement) :: rest ->
        close rest (Case { scrutinee = Tag ("k", replacement);
          scrutinee_type = ty; branches = ["k", body] }) in
  let* b_sum = get (lan ["k", b]) in
  let* sum_sum = get (lan ["k", sum]) in
  let* two_sum = get (lan ["k", two]) in
  let count = ref 0 in
  let* () = each (fun (context, bindings) ->
    each (fun (replacement_type, replacement_sum) ->
      each (fun replacement ->
        each (fun ty ->
          each (fun body ->
            let* actual = get (substitute ~fuel:100000 ~context ~replacement
              ~replacement_type body ty) in
            let* () = get (check ~fuel:100000 ~context actual ty) in
            let original = Case { scrutinee = Tag ("k", replacement);
              scrutinee_type = replacement_sum; branches = ["k", body] } in
            let* before = get (run ~fuel:100000 (close bindings original) ty) in
            let* after = get (run ~fuel:100000 (close bindings actual) ty) in
            let* () = ensure (before = after) "substitution disagrees with environment evaluation" in
            incr count; Ok ()) (terms (replacement_type :: context) ty))
          [a; b; sum; two]) (terms context replacement_type))
      [a, sum; b, b_sum; sum, sum_sum; two, two_sum])
    [[], []; [a], [sum, Atom "x"];
     [a; a], [sum, Atom "x"; sum, Atom "y"];
     [b; a], [b_sum, Atom "z"; sum, Atom "y"]] in
  Printf.printf "PASS %d substitution typing and evaluation comparisons\n" !count;
  Ok ()

let () = Result.fold
  ~ok:(fun () -> print_endline "PASS finite substitution, capture avoidance and resource limits")
  ~error:(fun message -> prerr_endline ("FAIL " ^ message); exit 1) (tests ())
