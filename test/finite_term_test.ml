open Finite_term

let ( let* ) = Result.bind
let ensure condition message = if condition then Ok () else Error message
let get result = Result.map_error (fun _ -> "unexpected checker error") result
let rejects expected actual = Result.fold
  ~error:(fun actual -> ensure (actual = expected) "wrong rejection")
  ~ok:(fun _ -> Error "accepted invalid input") actual
let evaluates term ty value =
  let* actual = get (run ~fuel:1000 term ty) in
  ensure (actual = value) "wrong evaluation"

let tests () =
  let* a = get (atoms ["y"; "x"]) in
  let* a_reordered = get (atoms ["x"; "y"]) in
  let* other = get (atoms ["z"]) in
  let* sum = get (lan ["right", a; "left", a]) in
  let* product = get (ran ["right", other; "left", a]) in
  let* empty_sum = get (lan []) in
  let* empty_product = get (ran []) in
  let* empty_atoms = get (atoms []) in
  let check context term ty = check ~fuel:1000 ~context term ty in
  let* () = rejects (Duplicate_label "x") (atoms ["x"; "x"]) in
  let* () = rejects (Duplicate_label "a") (lan ["a", a; "a", other]) in
  let* () = rejects (Duplicate_label "a") (ran ["a", a; "a", other]) in
  let* () = get (check [a] (Var 0) a_reordered) in
  let* () = rejects Type_mismatch (check [a] (Var 0) other) in
  let* () = rejects (Invalid_variable (-1)) (check [a] (Var (-1)) a) in
  let* () = rejects (Invalid_variable 1) (check [a] (Var 1) a) in
  let* () = rejects (Invalid_variable 0) (run ~fuel:100 (Var 0) a) in
  let* () = rejects (Invalid_atom "x") (check [] (Atom "x") empty_atoms) in
  let* () = evaluates (Section []) empty_product (Section_value []) in
  let* () = rejects (Unexpected_label "left")
    (check [] (Tag ("left", Atom "x")) empty_sum) in
  let section = Section ["right", Atom "z"; "left", Atom "x"] in
  let* () = evaluates section product
    (Section_value ["left", Atom_value "x"; "right", Atom_value "z"]) in
  let* () = evaluates
    (Project { section; section_type = product; label = "left" }) a (Atom_value "x") in
  let case branches = Case {
    scrutinee = Tag ("left", Atom "y"); scrutinee_type = sum; branches } in
  let* () = evaluates (case ["right", Var 0; "left", Var 0]) a (Atom_value "y") in
  (* The inner binder must preserve the outer payload at index 1. *)
  let nested = case ["left", Case {
    scrutinee = Tag ("right", Atom "x"); scrutinee_type = sum;
    branches = ["left", Var 1; "right", Var 1] }; "right", Var 0] in
  let* () = evaluates nested a (Atom_value "y") in
  let* () = rejects (Invalid_atom "z")
    (check [] (case ["left", Var 0; "right", Atom "z"]) a) in
  let* () = rejects (Invalid_variable 1)
    (check [] (case ["left", Var 1; "right", Var 0]) a) in
  let* () = rejects (Missing_label "right") (check [] (case ["left", Var 0]) a) in
  let* () = rejects (Duplicate_label "left")
    (check [] (case ["left", Var 0; "left", Var 0; "right", Var 0]) a) in
  let* () = rejects (Unexpected_label "z")
    (check [] (case ["left", Var 0; "right", Var 0; "z", Var 0]) a) in
  let* () = rejects (Missing_label "right")
    (check [] (Section ["left", Atom "x"]) product) in
  let* () = rejects (Duplicate_label "left")
    (check [] (Section ["left", Atom "x"; "left", Atom "y"]) product) in
  let* () = rejects (Unexpected_label "z")
    (check [] (Section ["z", Atom "x"]) empty_product) in
  let* () = rejects (Invalid_atom "x")
    (check [] (Section ["left", Atom "x"; "right", Atom "x"]) product) in
  let* () = rejects Type_mismatch
    (check [] (Project { section; section_type = product; label = "right" }) a) in
  let* () = rejects (Unexpected_label "missing")
    (check [] (Project { section; section_type = product; label = "missing" }) a) in
  let* () = rejects Expected_ran
    (check [] (Project { section; section_type = sum; label = "left" }) a) in
  let* () = rejects Expected_lan
    (check [] (Case { scrutinee = Atom "x"; scrutinee_type = a; branches = [] }) a) in
  let* () = rejects Type_mismatch (check [] (Atom "x") sum) in
  let* () = rejects Expected_lan (check [] (Tag ("left", Atom "x")) a) in
  let* () = rejects Expected_ran (check [] (Section []) a) in
  let* () = get (check [empty_sum]
    (Case { scrutinee = Var 0; scrutinee_type = empty_sum; branches = [] }) other) in
  let* () = rejects Resource_exhausted (Finite_term.check ~fuel:0 ~context:[] (Atom "x") a) in
  let* () = rejects Resource_exhausted (run ~fuel:(-1) (Atom "x") a) in
  let* () = get (Finite_term.check ~fuel:1 ~context:[] (Atom "x") a) in
  let* () = rejects Resource_exhausted (run ~fuel:1 (Atom "x") a) in
  let* value = get (run ~fuel:2 (Atom "x") a) in
  let* () = ensure (value = Atom_value "x") "exact budget boundary" in
  (* Siblings share a budget. Checking and evaluation share a budget too. *)
  let* () = rejects Resource_exhausted (Finite_term.check ~fuel:2 ~context:[] section product) in
  let* () = get (Finite_term.check ~fuel:3 ~context:[] section product) in
  let* () = rejects Resource_exhausted (run ~fuel:5 section product) in
  let* _ = get (run ~fuel:6 section product) in
  Ok ()

let () = Result.fold
  ~ok:(fun () -> print_endline "PASS finite term checking, beta evaluation, binders and resource limits")
  ~error:(fun message -> prerr_endline ("FAIL " ^ message); exit 1) (tests ())
