open Finite_term

let ( let* ) = Result.bind
let ensure condition message = if condition then Ok () else Error message
let get result = Result.map_error (fun _ -> "unexpected normalization/checking error") result
let rejects expected = Result.fold
  ~error:(fun actual -> ensure (actual = expected) "wrong rejection")
  ~ok:(fun _ -> Error "accepted invalid input")
let rec each f = function
  | [] -> Ok ()
  | x :: rest -> let* () = f x in each f rest
let rec fold_each f accumulator = function
  | [] -> Ok accumulator
  | x :: rest -> let* accumulator = f accumulator x in fold_each f accumulator rest

(* The term form of a value. Closed normal forms must equal it. *)
let rec term_of_value = function
  | Atom_value atom -> Atom atom
  | Tag_value (label, payload) -> Tag (label, term_of_value payload)
  | Section_value entries ->
      Section (List.map (fun (label, value) -> label, term_of_value value) entries)

let tests () =
  let* a = get (atoms ["x"; "y"]) in
  let* b = get (atoms ["z"]) in
  let* one = get (atoms ["x"]) in
  let* sum = get (lan ["k", a]) in
  let* one_sum = get (lan ["a", one]) in
  let* pair_sum = get (lan ["k", a; "m", b]) in
  let* two = get (ran ["a", a; "b", a]) in
  let norm context term ty = get (normalize ~fuel:100000 ~context term ty) in
  let case scrutinee body =
    Case { scrutinee; scrutinee_type = sum; branches = ["k", body] } in
  (* Two fibers, two payload types. Branch bodies are given in reversed label
     order, so canonical output order is exercised as well. *)
  let pair_case scrutinee left right =
    Case { scrutinee; scrutinee_type = pair_sum;
           branches = ["m", right; "k", left] } in
  let project section label = Project { section; section_type = two; label } in

  (* Exact minimal budgets. Each entry states the reduced form as well. *)
  let boundary (context, term, ty, needed, expected) =
    let* () = rejects Resource_exhausted
      (normalize ~fuel:(needed - 1) ~context term ty) in
    let* actual = get (normalize ~fuel:needed ~context term ty) in
    ensure (actual = expected) "exact fuel example gave the wrong normal form" in
  let neutral_case =
    Case { scrutinee = Var 0; scrutinee_type = sum; branches = ["k", Var 0] } in
  let* () = each boundary [
    (* Check 4, reduce 3, substitute 2, reduce the substituted body 1. *)
    ([], Case { scrutinee = Tag ("a", Atom "x"); scrutinee_type = one_sum;
                branches = ["a", Var 0] }, one, 10, Atom "x");
    (* Check 4, reduce 4. The selected field needs no extra visit. *)
    ([], project (Section ["b", Atom "y"; "a", Atom "x"]) "b", a, 8, Atom "y");
    (* Check 3, reduce 3. A neutral scrutinee blocks the substitution. *)
    ([sum], neutral_case, a, 6, neutral_case)] in

  (* Open terms. A neutral scrutinee keeps the Case and reduces the branches
     under the fiber type. *)
  let inner = case (Tag ("k", Var 0)) (Var 1) in
  let* actual = norm [sum]
    (Case { scrutinee = Var 0; scrutinee_type = sum; branches = ["k", inner] }) a in
  let* () = ensure (actual = neutral_case)
    "a nested redex under a neutral branch did not reduce" in
  (* A Case of a Tag under an outer binder. The payload of the inner Tag is the
     outer bound variable, so the shift must keep it after the substitution. *)
  let shifting = case (Tag ("k", Var 0)) (case (Tag ("k", Atom "x")) (Var 1)) in
  let* actual = norm [sum]
    (Case { scrutinee = Var 0; scrutinee_type = sum; branches = ["k", shifting] }) a in
  let* () = ensure (actual = neutral_case) "the shift arithmetic moved the payload" in
  let* actual = norm [a; sum] shifting a in
  let* () = ensure (actual = Var 0) "the outer variable did not survive the substitution" in
  (* A Project of a neutral section stays a Project. *)
  let* actual = norm [two] (project (Var 0) "b") a in
  let* () = ensure (actual = project (Var 0) "b") "a neutral projection reduced" in
  let* actual = norm [two; sum]
    (project (Case { scrutinee = Var 1; scrutinee_type = sum;
                     branches = ["k", case (Tag ("k", Var 0)) (Var 2)] }) "a") a in
  let* () = ensure
    (actual = project (Case { scrutinee = Var 1; scrutinee_type = sum;
                              branches = ["k", Var 1] }) "a")
    "a projection of a neutral Case lost a branch reduction" in

  (* Canonical label order, whatever the source order is. *)
  let* actual = norm [] (Section ["b", Atom "y"; "a", Atom "x"]) two in
  let* () = ensure (actual = Section ["a", Atom "x"; "b", Atom "y"])
    "section fields are not in canonical order" in
  let* actual = norm [pair_sum]
    (Case { scrutinee = Var 0; scrutinee_type = pair_sum;
            branches = ["m", Atom "x"; "k", Atom "y"] }) a in
  let* () = ensure
    (actual = Case { scrutinee = Var 0; scrutinee_type = pair_sum;
                     branches = ["k", Atom "y"; "m", Atom "x"] })
    "branches are not in canonical order" in

  (* Rejected inputs return the checking error and no term. *)
  let* () = rejects (Missing_label "b")
    (normalize ~fuel:1000 ~context:[] (Section ["a", Atom "x"]) two) in
  let* () = rejects (Unexpected_label "c")
    (normalize ~fuel:1000 ~context:[]
      (Section ["a", Atom "x"; "b", Atom "y"; "c", Atom "x"]) two) in
  let* () = rejects Type_mismatch (normalize ~fuel:1000 ~context:[b] (Var 0) a) in
  let* () = rejects Type_mismatch
    (normalize ~fuel:1000 ~context:[] (Atom "x") sum) in
  let* () = rejects (Invalid_atom "z")
    (normalize ~fuel:1000 ~context:[] (case (Tag ("k", Atom "x")) (Atom "z")) a) in

  (* A bounded, type-directed corpus, in the shape of the substitution test. *)
  let variables context ty = List.filter_map
    (fun (index, actual) -> if actual = ty then Some (Var index) else None)
    (List.mapi (fun index ty -> index, ty) context) in
  let base context ty = variables context ty @
    (match () with
     | () when ty = a -> [Atom "x"; Atom "y"]
     | () when ty = b -> [Atom "z"]
     | () when ty = sum -> [Tag ("k", Atom "x"); Tag ("k", Atom "y")]
     | () when ty = pair_sum -> [Tag ("k", Atom "x"); Tag ("m", Atom "z")]
     | () when ty = two -> [Section ["a", Atom "x"; "b", Atom "y"]]
     | () -> []) in
  let terms context ty =
    base context ty @
    List.concat_map (fun scrutinee ->
      List.map (case scrutinee) (base (a :: context) ty)) (base context sum) @
    (* Multi-branch Cases. Each branch body ranges over the payload variable at
       index zero and the closed atoms, so a wrong branch or a mislaid payload
       changes the result. *)
    List.concat_map (fun scrutinee ->
      List.concat_map (fun left ->
        List.map (pair_case scrutinee left) (base (b :: context) ty))
        (base (a :: context) ty))
      (base context pair_sum) @
    (match () with
     | () when ty = a -> List.map (fun section -> project section "b") (base context two)
     | () when ty = sum -> List.map (fun t -> Tag ("k", t)) (base context a)
     | () when ty = two -> List.concat_map (fun left ->
         List.map (fun right -> Section ["b", right; "a", left]) (base context a))
         (base context a)
     | () -> []) in
  let checked context ty = List.filter
    (fun term -> Result.fold ~ok:(fun () -> true) ~error:(fun _ -> false)
      (check ~fuel:100000 ~context term ty))
    (terms context ty) in
  (* Closed terms: the normal form is the term form of the evaluated value. *)
  let* closed = fold_each (fun count ty ->
      fold_each (fun count term ->
          let* value = get (run ~fuel:100000 term ty) in
          let* actual = norm [] term ty in
          let* () = ensure (actual = term_of_value value)
            "a closed normal form disagrees with the evaluated value" in
          Ok (count + 1))
        count (checked [] ty))
    0 [a; b; sum; two] in
  (* Open terms: the output rechecks, and normalization is idempotent. *)
  let* opened = fold_each (fun count context ->
      fold_each (fun count ty ->
          fold_each (fun count term ->
              let* actual = norm context term ty in
              let* () = get (check ~fuel:100000 ~context actual ty) in
              let* again = norm context actual ty in
              let* () = ensure (again = actual) "normalization is not idempotent" in
              Ok (count + 1))
            count (checked context ty))
        count [a; b; sum; two])
    0 [[]; [a]; [sum]; [b; a]; [two]; [pair_sum]] in
  Printf.printf "PASS %d closed normal form and value comparisons\n" closed;
  Printf.printf "PASS %d open term recheck and idempotence comparisons\n" opened;
  Ok ()

let () = Result.fold
  ~ok:(fun () -> print_endline
    "PASS finite normalization, neutral forms, canonical order and resource limits")
  ~error:(fun message -> prerr_endline ("FAIL " ^ message); exit 1) (tests ())
