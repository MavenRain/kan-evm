(** Explicit terms for one fiber of a finite discrete Kan extension.
    This is a nondependent reference fragment, not a proof kernel. *)
type ty
type error =
  | Duplicate_label of string
  | Missing_label of string
  | Unexpected_label of string
  | Invalid_variable of int
  | Invalid_atom of string
  | Type_mismatch
  | Expected_lan
  | Expected_ran
  | Resource_exhausted

(** Finite atom sets are metatheoretic inputs. Constructors canonicalize label
    order and reject duplicates. Empty atom sets and empty fibers are allowed. *)
val atoms : string list -> (ty, error) result
val lan : (string * ty) list -> (ty, error) result
val ran : (string * ty) list -> (ty, error) result

type term =
  | Var of int
  | Atom of string
  | Tag of string * term
  | Section of (string * term) list
  | Case of { scrutinee : term; scrutinee_type : ty;
              branches : (string * term) list }
  | Project of { section : term; section_type : ty; label : string }

(** Contexts are nearest-binder first. Each Case branch binds its payload at
    index zero. Every branch is checked, including branches not executed.
    Fuel bounds visited term nodes, not elapsed time or host allocation. *)
val check : fuel:int -> context:ty list -> term -> ty -> (unit, error) result

type value =
  | Atom_value of string
  | Tag_value of string * value
  | Section_value of (string * value) list

(** Check a closed term, then evaluate it with the remaining shared node budget.
    Exhaustion is an error, never evidence of successful checking. Evaluation
    is eager; sections are evaluated in canonical label order. *)
val run : fuel:int -> term -> ty -> (value, error) result
