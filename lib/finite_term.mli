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

(** [substitute ~fuel ~context ~replacement ~replacement_type body expected]
    first checks [replacement] against [replacement_type] in [context], then
    [body] against [expected] in [replacement_type :: context]. It removes
    that nearest context entry by capture-avoiding substitution. The result
    has type [expected] in [context]; it is not normalized or evaluated.

    One budget covers both checks, each body node traversed, and each node of
    the replacement traversed at every substituted occurrence. All branches
    are visited. Field order and type annotations are preserved. Like [check],
    this meters term visits only, not host stack, allocation or type operations.
    Errors from either check propagate, even if the replacement is unused. *)
val substitute : fuel:int -> context:ty list -> replacement:term ->
  replacement_type:ty -> term -> ty -> (term, error) result

(** [normalize ~fuel ~context term expected] first checks [term] against
    [expected] in [context]. Then it reduces the term to beta normal form. No
    Case in the result has a Tag scrutinee. No Project in the result has a
    Section section. Neutral forms stay: a variable, a Case on a neutral
    scrutinee, and a Project of a neutral section. The branches of a neutral
    Case are reduced at the expected type. In this nondependent fragment the
    binder fiber does not direct beta reduction. Result sections and branches
    use canonical label order, even when the input order differs. Annotations
    do not change. There is no eta rule.

    One budget covers the check and the reduction. The check charges one unit
    per node. The reduction charges one unit per visited node. Each Case of a
    Tag charges the substitution in addition: one unit per node of the selected
    branch, plus one unit per replacement node at each substituted occurrence.
    It then charges the reduction of the substituted body. For example,
    [normalize] of a Case with scrutinee [Tag ("a", Atom "x")], annotation
    [Lan ["a", Atoms ["x"]]] and branch [Var 0] at [Atoms ["x"]] needs ten
    units: four to check, three to reduce the Case node and its scrutinee, two
    to substitute, and one to reduce the substituted body. Exhaustion returns
    [Resource_exhausted]. The result is not rechecked internally. *)
val normalize : fuel:int -> context:ty list -> term -> ty -> (term, error) result

type value =
  | Atom_value of string
  | Tag_value of string * value
  | Section_value of (string * value) list

(** Check a closed term, then evaluate it with the remaining shared node budget.
    Exhaustion is an error, never evidence of successful checking. Evaluation
    is eager; sections are evaluated in canonical label order. *)
val run : fuel:int -> term -> ty -> (value, error) result
