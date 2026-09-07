open Finite_term

let ( let* ) = Result.bind
let ensure condition message = if condition then Ok () else Error message
let get result = Result.map_error (fun _ -> "unexpected conversion/checking error") result
let rejects expected = Result.fold
  ~error:(fun actual -> ensure (actual = expected) "wrong conversion rejection")
  ~ok:(fun _ -> Error "conversion accepted invalid input or insufficient fuel")
let rec each f = function
  | [] -> Ok ()
  | x :: rest -> let* () = f x in each f rest
let rec fold_each f accumulator = function
  | [] -> Ok accumulator
  | x :: rest -> let* accumulator = f accumulator x in fold_each f accumulator rest

let tests () =
  let* a = get (atoms ["x"; "y"]) in
  let* b = get (atoms ["z"]) in
  let* sum = get (lan ["k", a; "m", a]) in
  let* single = get (lan ["k", a]) in
  let* pair = get (ran ["a", a; "b", a]) in
  let* empty_atoms = get (atoms []) in
  let* empty_lan = get (lan []) in
  let* empty_ran = get (ran []) in
  let case scrutinee left right =
    Case { scrutinee; scrutinee_type = sum;
           branches = ["m", right; "k", left] } in
  let one_case scrutinee body =
    Case { scrutinee; scrutinee_type = single; branches = ["k", body] } in
  let project section label = Project { section; section_type = pair; label } in
  let decide context left right ty expected =
    let* actual = get (convert ~fuel:100000 ~context left right ty) in
    ensure (actual = expected) "conversion returned the wrong decision" in
  let boundary (context, left, right, ty, needed, expected) =
    let* () = rejects Resource_exhausted
      (convert ~fuel:(needed - 1) ~context left right ty) in
    let* actual = get (convert ~fuel:needed ~context left right ty) in
    ensure (actual = expected) "exact conversion fuel gave the wrong decision" in
  let beta = one_case (Tag ("k", Atom "x")) (Var 0) in
  let fields = Section ["b", Atom "y"; "a", Atom "x"] in
  let* () = each boundary [
    ([], Atom "x", Atom "x", a, 4, true);
    ([], Atom "x", Atom "y", a, 4, false);
    ([], Tag ("k", Atom "x"), Tag ("m", Atom "x"), sum, 8, false);
    ([], beta, Atom "x", a, 12, true);
    ([], Atom "x", beta, a, 12, true);
    ([], beta, beta, a, 20, true);
    ([], project fields "b", Atom "y", a, 10, true);
    ([], Section [], Section [], empty_ran, 4, true);
    ([a], Var 0, Var 0, a, 4, true)] in
  let* () = each (fun fuel -> rejects Resource_exhausted
    (convert ~fuel ~context:[] (Atom "x") (Atom "x") a)) [-1; 0; 1; 2] in
  let* () = decide [] (Tag ("k", beta)) (Tag ("k", Atom "x")) sum true in
  let* () = decide [] (Tag ("k", Atom "x")) (Tag ("k", Atom "y")) sum false in
  let* () = decide [] (case (Tag ("m", Atom "y")) (Atom "x") (Var 0))
    (Atom "y") a true in

  (* Canonical order applies to both sections and branches of neutral Cases. *)
  let* () = decide [] fields (Section ["a", Atom "x"; "b", Atom "y"]) pair true in
  let neutral = case (Var 0) (Var 0) (Atom "x") in
  let reordered = Case { scrutinee = Var 0; scrutinee_type = sum;
                          branches = ["k", Var 0; "m", Atom "x"] } in
  let* () = decide [sum] neutral reordered a true in
  let* () = decide [sum] neutral (case (Var 0) (Atom "x") (Var 0)) a false in

  (* Two neutral binders survive the beta step. The free replacement must move
     from index zero to index two, while the intervening payload stays bound. *)
  let nested = one_case (Tag ("k", Var 0))
    (one_case (Var 2)
      (one_case (Var 3) (Section ["a", Var 2; "b", Var 1]))) in
  let nested_normal = one_case (Var 1)
    (one_case (Var 2) (Section ["a", Var 2; "b", Var 1])) in
  let captured = one_case (Var 1)
    (one_case (Var 2) (Section ["a", Var 0; "b", Var 1])) in
  let* () = decide [a; single] nested nested_normal pair true in
  let* () = decide [a; single] nested captured pair false in

  (* Beta conversion intentionally has no product eta rule, even for a unit. *)
  let expanded = Section ["a", project (Var 0) "a"; "b", project (Var 0) "b"] in
  let* () = decide [pair] (Var 0) expanded pair false in
  let* () = decide [empty_ran] (Var 0) (Section []) empty_ran false in
  let absurd scrutinee = Case { scrutinee; scrutinee_type = empty_lan; branches = [] } in
  let* () = decide [empty_lan] (absurd (Var 0)) (absurd (Var 0)) empty_atoms true in
  let* () = decide [empty_lan; empty_lan]
    (absurd (Var 0)) (absurd (Var 1)) empty_atoms false in
  let* () = decide [empty_atoms] (Var 0) (Var 0) empty_atoms true in
  let* single_ran = get (ran ["a", a]) in
  let annotated section_type =
    Project { section = absurd (Var 0); section_type; label = "a" } in
  let* () = decide [empty_lan] (annotated single_ran) (annotated pair) a false in

  (* Neither equal syntax nor an unexecuted branch may bypass checking. *)
  let bad_branch = case (Tag ("k", Atom "x")) (Var 0) (Atom "z") in
  let malformed = [
    ([], Var 0, a, Invalid_variable 0);
    ([], Atom "z", a, Invalid_atom "z");
    ([], Atom "x", empty_atoms, Invalid_atom "x");
    ([b], Var 0, a, Type_mismatch);
    ([], Section ["a", Atom "x"], pair, Missing_label "b");
    ([], Section ["a", Atom "x"; "a", Atom "y"], pair, Duplicate_label "a");
    ([], Tag ("k", Atom "x"), empty_lan, Unexpected_label "k");
    ([], bad_branch, a, Invalid_atom "z")] in
  let* () = each (fun (context, term, ty, error) ->
    rejects error (convert ~fuel:100000 ~context term term ty)) malformed in
  let* () = rejects (Invalid_variable 0)
    (convert ~fuel:100000 ~context:[] (Atom "x") (Var 0) a) in
  let* () = rejects (Invalid_atom "z")
    (convert ~fuel:100000 ~context:[] (Atom "x") bad_branch a) in
  let* () = rejects (Invalid_atom "z")
    (convert ~fuel:100000 ~context:[] (Atom "z") (Var 0) a) in
  let* () = rejects (Invalid_variable 0)
    (convert ~fuel:100000 ~context:[] (Var 0) (Atom "z") a) in
  (* Left normalization finishes before the right check starts. The right
     invalid atom is observable only after the left has spent ten units. *)
  let* () = rejects Resource_exhausted
    (convert ~fuel:9 ~context:[] beta (Atom "z") a) in
  let* () = rejects Resource_exhausted
    (convert ~fuel:10 ~context:[] beta (Atom "z") a) in
  let* () = rejects (Invalid_atom "z")
    (convert ~fuel:11 ~context:[] beta (Atom "z") a) in

  (* All pairs in this closed corpus use evaluation as an independent oracle.
     In particular, equal syntax is only a small subset of the positive pairs. *)
  let atomic = [Atom "x"; Atom "y"] in
  let tags = List.concat_map (fun label -> List.map (fun t -> Tag (label, t)) atomic)
    ["k"; "m"] in
  let sections = List.concat_map (fun left ->
    List.map (fun right -> Section ["b", right; "a", left]) atomic) atomic in
  let closed base bodies = base @
    List.concat_map (fun scrutinee ->
      List.concat_map (fun left -> List.map (case scrutinee left) bodies) bodies) tags in
  let closed_corpora = [
    (a, closed atomic (Var 0 :: atomic) @ List.concat_map
      (fun section -> [project section "a"; project section "b"]) sections);
    (sum, closed tags tags);
    (pair, closed sections sections);
    (empty_ran, closed [Section []] [Section []])] in
  let* closed_pairs = fold_each (fun count (ty, terms) ->
    let* valued = fold_each (fun values term ->
      let* value = get (run ~fuel:100000 term ty) in
      Ok ((term, value) :: values)) [] terms in
    fold_each (fun count (left, left_value) ->
      fold_each (fun count (right, right_value) ->
        let* () = decide [] left right ty (left_value = right_value) in
        Ok (count + 1)) count valued) count valued) 0 closed_corpora in

  (* Independently discover each operand's minimum normalize budget. Their sum
     must be exactly the conversion threshold for every pair of open terms. *)
  let rec minimum context ty term fuel =
    if fuel > 500 then Error "open corpus exceeded its bounded fuel search"
    else Result.fold
      ~ok:(fun normal -> Ok (term, normal, fuel))
      ~error:(function
        | Resource_exhausted -> minimum context ty term (fuel + 1)
        | Duplicate_label _ | Missing_label _ | Unexpected_label _
        | Invalid_variable _ | Invalid_atom _ | Type_mismatch
        | Expected_lan | Expected_ran -> Error "invalid open corpus term")
      (normalize ~fuel ~context term ty) in
  let open_corpora = [
    ([a; sum; pair], a, [
      Var 0; Atom "x"; Atom "y"; project (Var 2) "a"; project (Var 2) "b";
      case (Var 1) (Var 0) (Var 0);
      case (Var 1) (Var 1) (Var 1);
      case (Tag ("k", Var 0)) (Var 0) (Atom "x");
      project (Section ["a", Var 0; "b", Atom "x"]) "a"]);
    ([a; single], pair, [nested; nested_normal; captured]);
    ([pair], pair, [Var 0; expanded]);
    ([empty_lan; empty_lan], empty_atoms, [absurd (Var 0); absurd (Var 1)])] in
  let* open_pairs = fold_each (fun count (context, ty, terms) ->
    let* measured = fold_each (fun measured term ->
      let* sample = minimum context ty term 0 in
      Ok (sample :: measured)) [] terms in
    fold_each (fun count (left, left_normal, left_fuel) ->
      fold_each (fun count (right, right_normal, right_fuel) ->
        let* () = boundary (context, left, right, ty, left_fuel + right_fuel,
          left_normal = right_normal) in
        Ok (count + 1)) count measured) count measured) 0 open_corpora in
  Printf.printf "PASS %d closed conversion and evaluation comparisons\n" closed_pairs;
  Printf.printf "PASS %d open conversion decisions and exact fuel boundaries\n" open_pairs;
  Ok ()

let () = Result.fold
  ~ok:(fun () -> print_endline
    "PASS finite conversion, canonical forms, checked operands and shared fuel")
  ~error:(fun message -> prerr_endline ("FAIL " ^ message); exit 1) (tests ())
