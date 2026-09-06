open Finite_kan

let ( let* ) = Result.bind
let lift result = Result.map_error string_of_error result
let check condition message = if condition then Ok () else Error message
let rec each f = function
  | [] -> Ok ()
  | x :: xs -> let* () = f x in each f xs

let get key entries =
  List.assoc_opt key entries |> Option.to_result ~none:"test lookup failed"

let rec assignments = function
  | [] -> [[]]
  | (key, choices) :: rest ->
      let tails = assignments rest in
      List.concat_map
        (fun choice -> List.map (fun tail -> (key, choice) :: tail) tails)
        choices

let rec traverse f = function
  | [] -> Ok []
  | x :: xs -> let* y = f x in let* ys = traverse f xs in Ok (y :: ys)

let same_entries left right =
  List.sort Stdlib.compare left = List.sort Stdlib.compare right

let expect_error expected actual =
  Result.fold
    ~error:(fun found -> check (found = expected) "unexpected error variant")
    ~ok:(fun _ -> Error "invalid construction was accepted") actual

let base () = make ~domain:["a"; "c"] ~codomain:["b"; "empty"]
  ~mapping:["a", "b"; "c", "b"]
  ~fibers:["a", ["x"; "y"]; "c", ["x"]] |> lift

let malformed () =
  let* () = expect_error (Duplicate "a")
    (make ~domain:["a"; "a"] ~codomain:[] ~mapping:[] ~fibers:[]) in
  let* () = expect_error (Duplicate "b")
    (make ~domain:[] ~codomain:["b"; "b"] ~mapping:[] ~fibers:[]) in
  let* () = expect_error (Missing "a")
    (make ~domain:["a"] ~codomain:["b"] ~mapping:[] ~fibers:[]) in
  let* () = expect_error (Unexpected "c")
    (make ~domain:["a"] ~codomain:["b"]
       ~mapping:["a", "b"; "c", "b"] ~fibers:[]) in
  let* () = expect_error (Duplicate "a")
    (make ~domain:["a"] ~codomain:["b"]
       ~mapping:["a", "b"; "a", "b"] ~fibers:[]) in
  let* () = expect_error (Missing "a")
    (make ~domain:["a"] ~codomain:["b"]
       ~mapping:["a", "b"] ~fibers:[]) in
  let* () = expect_error (Unexpected "outside")
    (make ~domain:["a"] ~codomain:["b"]
       ~mapping:["a", "outside"] ~fibers:["a", []]) in
  expect_error (Duplicate "x")
    (make ~domain:["a"] ~codomain:["b"]
       ~mapping:["a", "b"] ~fibers:["a", ["x"; "x"]])

let introductions () =
  let* d = base () in
  let* tag = lan_intro d ~target:"b" ~source:"a" "x" |> lift in
  let* () = check (lan_elim tag (fun a x -> a, x) = ("a", "x")) "Lan beta" in
  let* () = expect_error (Wrong_target "a")
    (lan_intro d ~target:"empty" ~source:"a" "x") in
  let* () = expect_error (Unexpected "outside")
    (lan_intro d ~target:"outside" ~source:"a" "x") in
  let* () = expect_error (Missing "outside")
    (lan_intro d ~target:"b" ~source:"outside" "x") in
  let* () = expect_error (Invalid_atom "bad")
    (lan_intro d ~target:"b" ~source:"a" "bad") in
  let* section = ran_intro d ~target:"b" ["c", "x"; "a", "y"] |> lift in
  let* a = ran_elim section ~source:"a" |> lift in
  let* c = ran_elim section ~source:"c" |> lift in
  let* () = check (a = "y" && c = "x") "Ran beta / order independence" in
  let* () = expect_error (Missing "c") (ran_intro d ~target:"b" ["a", "x"]) in
  let* () = expect_error (Duplicate "a")
    (ran_intro d ~target:"b" ["a", "x"; "a", "y"; "c", "x"]) in
  let* () = expect_error (Unexpected "outside")
    (ran_intro d ~target:"b" ["a", "x"; "c", "x"; "outside", "x"]) in
  let* () = expect_error (Invalid_atom "y")
    (ran_intro d ~target:"b" ["a", "x"; "c", "y"]) in
  let* () = expect_error (Unexpected "outside") (ran_intro d ~target:"outside" []) in
  let* empty = ran_intro d ~target:"empty" [] |> lift in
  let* () = expect_error (Missing "a") (ran_elim empty ~source:"a") in
  let* d0 = make ~domain:["a"] ~codomain:["b"] ~mapping:["a", "b"]
    ~fibers:["a", []] |> lift in
  let* () = expect_error (Invalid_atom "x")
    (lan_intro d0 ~target:"b" ~source:"a" "x") in
  expect_error (Invalid_atom "x") (ran_intro d0 ~target:"b" ["a", "x"])

(* Exhaust all functions on both sides of each adjunction for f : A -> {b}.
   The parameter sweep includes empty A, empty X fibers and empty Y. *)
let adjunctions fibers ys =
  let domain = List.map fst fibers in
  let* d = make ~domain ~codomain:["b"]
    ~mapping:(List.map (fun a -> a, "b") domain) ~fibers |> lift in
  let tagged = List.concat_map
    (fun (a, xs) -> List.map (fun x -> a, x) xs) fibers in
  let lan_maps = assignments (List.map (fun ax -> ax, ys) tagged) in
  let component_maps = assignments
    (List.map (fun (a, xs) -> a, assignments (List.map (fun x -> x, ys) xs)) fibers) in
  let split h = traverse (fun (a, xs) ->
    let* components = traverse (fun x ->
      let* tag = lan_intro d ~target:"b" ~source:a x |> lift in
      let* y = lan_elim tag (fun a x -> get (a, x) h) in
      Ok (x, y)) xs in
    Ok (a, components)) fibers in
  let flatten k = traverse (fun (a, x) ->
    let* component = get a k in
    let* y = get x component in Ok ((a, x), y)) tagged in
  let* () = check (List.length lan_maps = List.length component_maps) "Lan hom-set size" in
  let* () = each (fun h ->
    let* k = split h in let* h' = flatten k in
    check (same_entries h h') "Lan adjunction forward roundtrip") lan_maps in
  let* () = each (fun k ->
    let* h = flatten k in let* k' = split h in
    check (same_entries k k') "Lan adjunction reverse roundtrip") component_maps in
  let sections = assignments fibers in
  let ran_maps = assignments (List.map (fun y -> y, sections) ys) in
  let reindexed_maps = assignments
    (List.map (fun (a, xs) -> a, assignments (List.map (fun y -> y, xs) ys)) fibers) in
  let unpack h = traverse (fun a ->
    let* components = traverse (fun y ->
      let* entries = get y h in
      let* section = ran_intro d ~target:"b" entries |> lift in
      let* x = ran_elim section ~source:a |> lift in Ok (y, x)) ys in
    Ok (a, components)) domain in
  let pack k = traverse (fun y ->
    let* entries = traverse (fun a ->
      let* component = get a k in let* x = get y component in Ok (a, x)) domain in
    let* section = ran_intro d ~target:"b" entries |> lift in
    let* checked_entries = traverse (fun a ->
      let* x = ran_elim section ~source:a |> lift in Ok (a, x)) domain in
    Ok (y, checked_entries)) ys in
  let* () = check (List.length ran_maps = List.length reindexed_maps) "Ran hom-set size" in
  let* () = each (fun h ->
    let* k = unpack h in let* h' = pack k in
    check (same_entries h h') "Ran adjunction forward roundtrip") ran_maps in
  each (fun k ->
    let* h = pack k in let* k' = unpack h in
    check (same_entries k k') "Ran adjunction reverse roundtrip") reindexed_maps

let exhaustive () =
  let choices = [[]; ["x"]; ["x"; "y"]] in
  let families = [] :: List.concat_map (fun xs ->
    ["a", xs] :: List.map (fun zs -> ["a", xs; "c", zs]) choices) choices in
  each (fun fibers -> each (adjunctions fibers) [[]; ["0"]; ["0"; "1"]]) families

let () =
  let tests = ["malformed diagrams", malformed;
               "introductions and eliminations", introductions;
               "39 exhaustive finite adjunction scenarios", exhaustive] in
  let failures = List.filter_map (fun (name, run) ->
    Result.fold
      ~ok:(fun () -> Printf.printf "PASS %s\n" name; None)
      ~error:(fun message -> Some (name ^ ": " ^ message)) (run ())) tests in
  List.iter prerr_endline failures;
  if failures = [] then exit 0 else exit 1
