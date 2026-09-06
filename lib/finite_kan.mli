(** A finite discrete semantic model, not the proposed language's kernel.
    All labels are compared exactly, without normalization. *)
type error =
  | Duplicate of string
  | Missing of string
  | Unexpected of string
  | Wrong_target of string
  | Invalid_atom of string

type diagram
type lan_value
type ran_value

(** Validate f : A -> B and X : A -> FinSet. Each source must have exactly
    one mapping and one fiber. All sets and association keys must be unique. *)
val make :
  domain:string list -> codomain:string list ->
  mapping:(string * string) list -> fibers:(string * string list) list ->
  (diagram, error) result

(** Lan_f X(b) has tagged elements (a, x) with f(a)=b and x in X(a). *)
val lan_intro : diagram -> target:string -> source:string -> string ->
  (lan_value, error) result
val lan_elim : lan_value -> (string -> string -> 'a) -> 'a

(** Ran_f X(b) consists of sections choosing one element in each X(a)
    with f(a)=b. Section order is irrelevant. Missing/extra keys are errors. *)
val ran_intro : diagram -> target:string -> (string * string) list ->
  (ran_value, error) result
val ran_elim : ran_value -> source:string -> (string, error) result

val string_of_error : error -> string
