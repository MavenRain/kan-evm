open Dependent_term

let ( let* ) = Result.bind
let fuel = 200_000
let ensure condition message = if condition then Ok () else Error message
let get result = Result.map_error (fun _ -> "unexpected checker error") result
let rejects expected actual = Result.fold
  ~error:(fun actual -> ensure (actual = expected) "wrong rejection")
  ~ok:(fun _ -> Error "accepted invalid input") actual
let rejects_invalid actual = Result.fold
  ~error:(function
    | Resource_exhausted -> Error "invalid input exhausted generous budget"
    | Duplicate_label _ | Invalid_variable _ | Invalid_atom _ | Type_mismatch
    | Expected_pi | Expected_sigma | Expected_nat | Expected_vec -> Ok ())
  ~ok:(fun _ -> Error "accepted invalid input") actual
let equal expected actual =
  let* actual = get actual in
  ensure (actual = expected) "unexpected result"

let atoms = Atoms ["x"; "y"]
let unsorted_atoms = Atoms ["y"; "x"]
let one = Succ Zero
let singleton = Cons { length = Zero; head = Atom "x"; tail = Nil }
let vector length = Vec (atoms, length)
let dependent_body = Pi (vector (Var 0), vector (Var 1))
let dependent_identity_type = Pi (Nat, dependent_body)
let dependent_identity = Lam (Lam (Var 0))
let identity_at argument = App {
  fn = dependent_identity; domain = Nat; codomain = dependent_body; argument }
let nat_identity argument = App {
  fn = Lam (Var 0); domain = Nat; codomain = Nat; argument }
let first pair = Split {
  pair; domain = Nat; codomain = vector (Var 0); motive = Nat; body = Var 1 }
let second pair = Split {
  pair; domain = Nat; codomain = vector (Var 0);
  motive = vector (first (Var 0)); body = Var 0 }

let dependent_formation () =
  let* () = get (check_type ~fuel ~context:[] dependent_identity_type) in
  let* () = get (check ~fuel ~context:[] dependent_identity dependent_identity_type) in
  let* () = get (check_type ~fuel ~context:[] (Sigma (Nat, vector (Var 0)))) in
  let* () = get (check ~fuel ~context:[] (Pair (one, singleton))
    (Sigma (Nat, vector (Var 0)))) in
  let* () = get (check ~fuel ~context:[vector (Var 0); Nat]
    (Var 0) (vector (Var 1))) in
  let application = App {
    fn = identity_at one; domain = vector one; codomain = vector one;
    argument = singleton } in
  let* () = equal singleton (normalize ~fuel ~context:[] application (vector one)) in
  let* () = equal singleton
    (normalize ~fuel ~context:[] (second (Pair (one, singleton))) (vector one)) in
  equal one (normalize ~fuel ~context:[] (first (Pair (one, singleton))) Nat)

let vector_indices () =
  let* () = get (check ~fuel ~context:[] Nil (vector (nat_identity Zero))) in
  let* () = get (check ~fuel ~context:[] singleton (vector (nat_identity one))) in
  let* () = get (check ~fuel ~context:[]
    (Cons { length = nat_identity Zero; head = Atom "x"; tail = Nil })
    (vector one)) in
  let* () = equal (vector one)
    (normalize_type ~fuel ~context:[] (vector (nat_identity one))) in
  let* () = rejects_invalid (check ~fuel ~context:[] Nil (vector one)) in
  let* () = rejects_invalid (check ~fuel ~context:[] singleton (vector Zero)) in
  let* () = rejects (Invalid_atom "z") (check ~fuel ~context:[]
    (Cons { length = Zero; head = Atom "z"; tail = Nil }) (vector one)) in
  let* () = rejects_invalid (check ~fuel ~context:[]
    (Cons { length = one; head = Atom "x"; tail = Nil }) (vector (Succ one))) in
  let* () = rejects_invalid (check ~fuel ~context:[]
    (Cons { length = Zero; head = Atom "x"; tail = singleton }) (vector one)) in
  rejects_invalid (check_type ~fuel ~context:[] (vector (Atom "x")))

let application_capture () =
  let inner = App {
    fn = App { fn = Var 2; domain = Nat; codomain = dependent_body;
      argument = Var 1 };
    domain = vector (Var 1); codomain = vector (Var 2); argument = Var 0 } in
  let expected_inner = App {
    fn = App { fn = Var 1; domain = Nat; codomain = dependent_body;
      argument = Var 2 };
    domain = vector (Var 2); codomain = vector (Var 3); argument = Var 0 } in
  let term = App {
    fn = Lam (Lam inner); domain = Nat; codomain = dependent_body;
    argument = Var 1 } in
  let context = [dependent_identity_type; Nat] in
  let ty = Pi (vector (Var 1), vector (Var 2)) in
  equal (Lam expected_inner) (normalize ~fuel ~context term ty)

let split_capture () =
  let context = [vector (Var 0); Nat; dependent_identity_type] in
  let inner = App {
    fn = App { fn = Var 5; domain = Nat; codomain = dependent_body;
      argument = Var 2 };
    domain = vector (Var 2); codomain = vector (Var 3); argument = Var 1 } in
  let expected_inner = App {
    fn = App { fn = Var 3; domain = Nat; codomain = dependent_body;
      argument = Var 2 };
    domain = vector (Var 2); codomain = vector (Var 3); argument = Var 1 } in
  let term = Split {
    pair = Pair (Var 1, Var 0); domain = Nat; codomain = vector (Var 0);
    motive = Pi (Nat, vector (first (Var 1))); body = Lam inner } in
  let ty = Pi (Nat, vector (Var 2)) in
  let* () = equal (Lam expected_inner) (normalize ~fuel ~context term ty) in
  let older_motive = Split {
    pair = Pair (Zero, one); domain = Nat; codomain = Nat;
    motive = Pi (vector (Var 1), vector (Var 2)); body = Lam (Var 0) } in
  let* () = equal (Lam (Var 0)) (normalize ~fuel ~context:[Nat]
    older_motive dependent_body) in
  let distinct_components = Split {
    pair = Pair (one, Var 0); domain = Nat; codomain = Nat;
    motive = Pi (Nat, Sigma (Nat, Nat));
    body = Lam (Pair (Var 2, Var 1)) } in
  equal (Lam (Pair (one, Var 1)))
    (normalize ~fuel ~context:[Nat] distinct_components (Pi (Nat, Sigma (Nat, Nat))))

let conversion_and_neutrals () =
  let* () = equal true (convert_types ~fuel ~context:[] atoms unsorted_atoms) in
  let* () = equal atoms (normalize_type ~fuel ~context:[] unsorted_atoms) in
  let* () = equal true (convert_types ~fuel ~context:[]
    (Pi (Nat, Vec (unsorted_atoms, nat_identity (Var 0))))
    (Pi (Nat, vector (Var 0)))) in
  let* () = equal true (convert_types ~fuel ~context:[]
    (Sigma (Nat, vector (nat_identity (Var 0))))
    (Sigma (Nat, vector (Var 0)))) in
  let* () = equal false (convert_types ~fuel ~context:[] (vector Zero) (vector one)) in
  let* () = equal true (convert ~fuel ~context:[]
    (nat_identity one) one Nat) in
  let* () = equal true (convert ~fuel ~context:[]
    (nat_identity one) (nat_identity one) Nat) in
  let* () = equal false (convert ~fuel ~context:[]
    Zero (nat_identity one) Nat) in
  let* () = equal false (convert ~fuel ~context:[] Zero one Nat) in
  let neutral = App {
    fn = Var 0; domain = unsorted_atoms; codomain = unsorted_atoms;
    argument = Atom "x" } in
  let canonical_neutral = App {
    fn = Var 0; domain = atoms; codomain = atoms; argument = Atom "x" } in
  let* () = equal canonical_neutral (normalize ~fuel
    ~context:[Pi (atoms, atoms)] neutral atoms) in
  let indexed_neutral = App {
    fn = Var 0; domain = vector (nat_identity Zero);
    codomain = vector (nat_identity Zero); argument = Nil } in
  let* () = equal (App {
    fn = Var 0; domain = vector Zero; codomain = vector Zero; argument = Nil })
    (normalize ~fuel ~context:[Pi (vector Zero, vector Zero)]
      indexed_neutral (vector Zero)) in
  let neutral_split = Split {
    pair = Var 0; domain = Nat; codomain = Nat; motive = Nat; body = Var 1 } in
  let* () = equal neutral_split
    (normalize ~fuel ~context:[Sigma (Nat, Nat)] neutral_split Nat) in
  let neutral_annots = Split {
    pair = Var 0; domain = unsorted_atoms; codomain = unsorted_atoms;
    motive = Vec (unsorted_atoms, nat_identity one);
    body = Cons { length = Zero;
      head = App { fn = Lam (Var 0); domain = unsorted_atoms;
        codomain = unsorted_atoms; argument = Var 1 };
      tail = Nil } } in
  let* () = equal (Split {
    pair = Var 0; domain = atoms; codomain = atoms; motive = vector one;
    body = Cons { length = Zero; head = Var 1; tail = Nil } })
    (normalize ~fuel ~context:[Sigma (atoms, atoms)]
      neutral_annots (vector one)) in
  let eta = Lam (App {
    fn = Var 1; domain = Nat; codomain = Nat; argument = Var 0 }) in
  let* () = equal false
    (convert ~fuel ~context:[Pi (Nat, Nat)] (Var 0) eta (Pi (Nat, Nat))) in
  let pair_eta = Split {
    pair = Var 0; domain = Nat; codomain = Nat;
    motive = Sigma (Nat, Nat); body = Pair (Var 1, Var 0) } in
  equal false (convert ~fuel ~context:[Sigma (Nat, Nat)]
    (Var 0) pair_eta (Sigma (Nat, Nat)))

let substitutions () =
  let* () = equal (Lam (Var 0)) (substitute ~fuel ~context:[]
    ~replacement:one ~replacement_type:Nat (Lam (Var 0)) dependent_body) in
  let* () = equal (Pi (Nat, vector (Succ (Var 1))))
    (substitute_type ~fuel ~context:[Nat]
      ~replacement:(Succ (Var 0)) ~replacement_type:Nat
      (Pi (Nat, vector (Var 1)))) in
  let body = Lam (App {
    fn = Lam (Var 0); domain = vector (Var 1);
    codomain = vector (Var 2); argument = Var 0 }) in
  let expected = Lam (App {
    fn = Lam (Var 0); domain = vector (Succ (Var 1));
    codomain = vector (Succ (Var 2)); argument = Var 0 }) in
  let* actual = get (substitute ~fuel ~context:[Nat]
    ~replacement:(Succ (Var 0)) ~replacement_type:Nat body dependent_body) in
  let* () = ensure (actual = expected) "substitution captured annotation indices" in
  let* () = get (check ~fuel ~context:[Nat] actual
    (Pi (vector (Succ (Var 0)), vector (Succ (Var 1))))) in
  let split_body = Split {
    pair = Pair (Zero, Lam (Var 0)); domain = Nat;
    codomain = Pi (vector (Var 1), vector (Var 2));
    motive = Pi (vector (Var 1), vector (Var 2)); body = Var 0 } in
  let expected_split = Split {
    pair = Pair (Zero, Lam (Var 0)); domain = Nat;
    codomain = Pi (vector (Succ (Var 1)), vector (Succ (Var 2)));
    motive = Pi (vector (Succ (Var 1)), vector (Succ (Var 2))); body = Var 0 } in
  let* () = equal expected_split (substitute ~fuel ~context:[Nat]
    ~replacement:(Succ (Var 0)) ~replacement_type:Nat split_body dependent_body) in
  let* () = rejects_invalid (substitute ~fuel ~context:[]
    ~replacement:Zero ~replacement_type:Nat Nil (vector (Var 0))) in
  let* () = rejects (Invalid_atom "z") (substitute ~fuel ~context:[]
    ~replacement:(Atom "z") ~replacement_type:atoms Zero Nat) in
  rejects (Invalid_atom "z") (substitute_type ~fuel ~context:[]
    ~replacement:(Atom "z") ~replacement_type:atoms Nat)

let invalid_inputs () =
  let duplicate = Atoms ["x"; "x"] in
  let* () = rejects (Duplicate_label "x") (check_type ~fuel ~context:[] duplicate) in
  let* () = rejects (Duplicate_label "x")
    (normalize_type ~fuel ~context:[] (Pi (Nat, duplicate))) in
  let* () = rejects (Duplicate_label "x")
    (convert_types ~fuel ~context:[] duplicate duplicate) in
  let* () = rejects (Duplicate_label "x")
    (check ~fuel ~context:[duplicate] Zero Nat) in
  let* () = rejects (Invalid_variable 0)
    (check_type ~fuel ~context:[vector (Var 0)] Nat) in
  let* () = rejects (Invalid_variable (-1))
    (check ~fuel ~context:[Nat] (Var (-1)) Nat) in
  let* () = rejects (Invalid_variable 1)
    (normalize ~fuel ~context:[Nat] (Var 1) Nat) in
  let* () = rejects (Invalid_variable 0)
    (convert ~fuel ~context:[] (Var 0) (Var 0) Nat) in
  let* () = rejects (Invalid_variable 0)
    (convert ~fuel ~context:[] Zero (Var 0) Nat) in
  let* () = rejects (Invalid_atom "z")
    (convert ~fuel ~context:[] (Atom "z") (Var 0) atoms) in
  let* () = rejects (Invalid_variable 0)
    (convert ~fuel ~context:[] (Var 0) (Atom "z") atoms) in
  let* () = rejects (Duplicate_label "x")
    (convert_types ~fuel ~context:[] Nat duplicate) in
  let* () = rejects (Duplicate_label "x")
    (convert_types ~fuel ~context:[] duplicate (vector (Var 0))) in
  let* () = rejects (Invalid_variable 0)
    (convert_types ~fuel ~context:[] (vector (Var 0)) duplicate) in
  let* () = rejects (Invalid_variable (-1))
    (check_type ~fuel ~context:[] (vector (Var (-1)))) in
  let* () = rejects Type_mismatch (check ~fuel ~context:[Nat] (Var 0) atoms) in
  let* () = rejects Type_mismatch (check ~fuel ~context:[]
    (App { fn = Lam Zero; domain = Nat; codomain = Nat; argument = Zero }) atoms) in
  let* () = rejects Type_mismatch (check ~fuel ~context:[]
    (Split { pair = Pair (Zero, Zero); domain = Nat; codomain = Nat;
      motive = Nat; body = Var 1 }) atoms) in
  let* () = rejects Type_mismatch (check ~fuel ~context:[]
    (App { fn = Lam Zero; domain = Nat; codomain = Nat; argument = Atom "x" }) Nat) in
  let* () = rejects Expected_nat (normalize ~fuel ~context:[]
    (App { fn = Zero; domain = Nat; codomain = Nat; argument = Zero }) Nat) in
  let* () = rejects (Invalid_variable 9) (check ~fuel ~context:[]
    (App { fn = Lam Zero; domain = Nat; codomain = vector (Var 9);
      argument = Zero }) Nat) in
  let unused_second = Split {
    pair = Pair (Zero, Atom "x"); domain = Nat; codomain = Nat;
    motive = Nat; body = Var 1 } in
  let* () = rejects Type_mismatch (normalize ~fuel ~context:[] unused_second Nat) in
  let* () = rejects (Invalid_atom "z") (normalize ~fuel ~context:[]
    (Split { pair = Pair (Zero, Zero); domain = Nat; codomain = Nat;
      motive = atoms; body = Atom "z" }) atoms) in
  let* () = rejects (Invalid_variable 2) (normalize ~fuel ~context:[]
    (Split { pair = Pair (Zero, Zero); domain = Nat; codomain = Nat;
      motive = Nat; body = Var 2 }) Nat) in
  let* () = rejects Type_mismatch (check ~fuel ~context:[]
    (Split { pair = Pair (Zero, Nil); domain = Nat; codomain = vector (Var 0);
      motive = vector (first (Var 0)); body = Nil }) (vector Zero)) in
  let* () = rejects Type_mismatch (check ~fuel ~context:[]
    (Pair (Zero, Nil)) (Sigma (Nat, vector one))) in
  let* () = rejects (Duplicate_label "x") (substitute ~fuel ~context:[duplicate]
    ~replacement:Zero ~replacement_type:Nat Zero Nat) in
  rejects (Invalid_variable 1) (substitute_type ~fuel ~context:[]
    ~replacement:Zero ~replacement_type:Nat (vector (Var 1)))

let unit_result result = Result.map (fun _ -> ()) result

let generated_beta () =
  let rec successors count base =
    if count <= 0 then base else Succ (successors (count - 1) base)
  in
  let rec generated count variable =
    let build previous =
      match () with
      | () when count mod 3 = 0 -> nat_identity (Succ previous)
      | () when count mod 3 = 1 -> Split {
          pair = Pair (Succ previous, Zero); domain = Nat; codomain = Nat;
          motive = Nat; body = Var 1 }
      | () -> App {
          fn = Lam (Succ (Var 0)); domain = Nat; codomain = Nat;
          argument = previous }
    in
    match () with
    | () when count <= 0 -> Var variable
    | () -> build (generated (count - 1) variable)
  in
  let context = [Nat] in
  let rec exercise depth =
    if depth > 8 then Ok ()
    else
      let term = generated depth 0 in
      let normal = successors depth (Var 0) in
      let lifted_normal = successors depth (Var 1) in
      let* actual = get (normalize ~fuel ~context term Nat) in
      let* () = ensure (actual = normal) "generated Nat beta result" in
      let* () = get (check ~fuel ~context actual Nat) in
      let function_term = App {
        fn = Lam (Lam (Var 1)); domain = Nat; codomain = Pi (Nat, Nat);
        argument = term } in
      let* actual = get (normalize ~fuel ~context function_term (Pi (Nat, Nat))) in
      let* () = ensure (actual = Lam lifted_normal) "generated Pi beta result" in
      let* () = get (check ~fuel ~context actual (Pi (Nat, Nat))) in
      let pair_term = Split {
        pair = Pair (term, Succ term); domain = Nat; codomain = Nat;
        motive = Pi (Nat, Sigma (Nat, Nat)); body = Lam (Pair (Var 2, Var 1)) } in
      let pair_type = Pi (Nat, Sigma (Nat, Nat)) in
      let* actual = get (normalize ~fuel ~context pair_term pair_type) in
      let* () = ensure (actual = Lam (Pair (lifted_normal, Succ lifted_normal)))
        "generated Sigma beta result" in
      let* () = get (check ~fuel ~context actual pair_type) in
      let body = Lam (App {
        fn = Lam (Var 0); domain = vector (Var 1);
        codomain = vector (Var 2); argument = Var 0 }) in
      let instantiated_type = Pi (vector term, vector (generated depth 1)) in
      let* actual = get (substitute ~fuel ~context ~replacement:term
        ~replacement_type:Nat body dependent_body) in
      let* () = get (check ~fuel ~context actual instantiated_type) in
      let* () = equal (Lam (Var 0))
        (normalize ~fuel ~context actual instantiated_type) in
      let* actual_type = get (substitute_type ~fuel ~context ~replacement:term
        ~replacement_type:Nat (Pi (Nat, vector (Var 1)))) in
      let* () = ensure (actual_type = Pi (Nat, vector (generated depth 1)))
        "generated dependent type substitution" in
      let* () = get (check_type ~fuel ~context actual_type) in
      exercise (depth + 1)
  in
  exercise 0

let resource_error retry = function
  | Resource_exhausted -> retry ()
  | Duplicate_label _ | Invalid_variable _ | Invalid_atom _ | Type_mismatch
  | Expected_pi | Expected_sigma | Expected_nat | Expected_vec ->
      Error "resource probe rejected valid input"

let minimum_budget operation =
  let rec bound budget =
    if budget > fuel then Error "no successful resource bound"
    else Result.fold ~ok:(fun () -> Ok budget)
      ~error:(resource_error (fun () -> bound (budget * 2))) (operation budget)
  in
  let rec narrow low high =
    if high - low <= 1 then Ok high
    else
      (* The guard above gives high - low greater than 1, so a logical shift
         right halves a nonnegative gap. *)
      let middle = low + ((high - low) lsr 1) in
      Result.fold ~ok:(fun () -> narrow low middle)
        ~error:(resource_error (fun () -> narrow middle high)) (operation middle)
  in
  let* high = bound 1 in
  narrow 0 high

let fuel_limits () =
  let context = [Nat] in
  let operations = [
    (fun fuel -> check_type ~fuel ~context (vector (nat_identity (Var 0))));
    (fun fuel -> check ~fuel ~context (nat_identity (Var 0)) Nat);
    (fun fuel -> unit_result (normalize_type ~fuel ~context
      (vector (nat_identity (Var 0)))));
    (fun fuel -> unit_result (normalize ~fuel ~context (nat_identity (Var 0)) Nat));
    (fun fuel -> unit_result (convert_types ~fuel ~context
      (vector (nat_identity (Var 0))) (vector (Var 0))));
    (fun fuel -> unit_result (convert ~fuel ~context
      (nat_identity (Var 0)) (Var 0) Nat));
    (fun fuel -> unit_result (substitute ~fuel ~context
      ~replacement:(Succ (Var 0)) ~replacement_type:Nat
      (Lam (Var 1)) (Pi (Nat, Nat))));
    (fun fuel -> unit_result (substitute_type ~fuel ~context
      ~replacement:(Succ (Var 0)) ~replacement_type:Nat
      (Pi (Nat, vector (Var 1))))) ] in
  let rec exercise = function
    | [] -> Ok ()
    | operation :: rest ->
        let* () = rejects Resource_exhausted (operation 0) in
        let* () = rejects Resource_exhausted (operation (-1)) in
        let* minimum = minimum_budget operation in
        let* () = rejects Resource_exhausted (operation (minimum - 1)) in
        let rec successes = function
          | [] -> Ok ()
          | budget :: tail -> let* () = get (operation budget) in successes tail
        in
        let* () = successes [minimum; minimum + 1; minimum + 7; minimum * 2] in
        exercise rest
  in
  let* () = exercise operations in
  let exact_operations = [
    1, (fun fuel -> check_type ~fuel ~context:[] Nat);
    2, (fun fuel -> check ~fuel ~context:[] Zero Nat);
    2, (fun fuel -> unit_result (normalize_type ~fuel ~context:[] Nat));
    3, (fun fuel -> unit_result (normalize ~fuel ~context:[] Zero Nat));
    4, (fun fuel -> unit_result (convert_types ~fuel ~context:[] Nat Nat));
    5, (fun fuel -> unit_result (convert ~fuel ~context:[] Zero Zero Nat)) ] in
  let rec exact = function
    | [] -> Ok ()
    | (minimum, operation) :: rest ->
        let* () = rejects Resource_exhausted (operation (minimum - 1)) in
        let* () = get (operation minimum) in
        exact rest
  in
  let* () = exact exact_operations in
  let checked fuel = check ~fuel ~context (nat_identity (Var 0)) Nat in
  let normalized fuel = unit_result
    (normalize ~fuel ~context (nat_identity (Var 0)) Nat) in
  let converted fuel = unit_result
    (convert ~fuel ~context (nat_identity (Var 0)) (nat_identity (Var 0)) Nat) in
  let* check_budget = minimum_budget checked in
  let* normalize_budget = minimum_budget normalized in
  let* () = ensure (normalize_budget > check_budget) "checking and reduction reset fuel" in
  let* () = rejects Resource_exhausted (normalized check_budget) in
  let* () = rejects Resource_exhausted (converted normalize_budget) in
  let* plain_budget = minimum_budget (fun fuel -> check_type ~fuel ~context:[] Nat) in
  let* () = rejects Resource_exhausted (check_type ~fuel:plain_budget ~context:[Nat; Nat] Nat) in
  let* child_budget = minimum_budget
    (fun fuel -> check ~fuel ~context:[] one Nat) in
  rejects Resource_exhausted
    (check ~fuel:child_budget ~context:[] (Pair (one, one)) (Sigma (Nat, Nat)))

let tests () =
  let rec run = function
    | [] -> Ok ()
    | (name, test) :: rest ->
        let* () = Result.map_error (fun message -> name ^ ": " ^ message) (test ()) in
        run rest
  in
  run [
    "dependent formation and elimination", dependent_formation;
    "vector indices", vector_indices;
    "application capture avoidance", application_capture;
    "split capture avoidance", split_capture;
    "conversion and neutrals", conversion_and_neutrals;
    "substitution", substitutions;
    "invalid inputs", invalid_inputs;
    "generated beta corpus", generated_beta;
    "shared fuel and monotonicity", fuel_limits ]

let () = Result.fold
  ~ok:(fun () -> print_endline "PASS dependent formation, beta reduction, substitution, conversion and resource limits")
  ~error:(fun message -> prerr_endline ("FAIL " ^ message); exit 1) (tests ())
