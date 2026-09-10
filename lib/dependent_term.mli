(** Experimental dependent reference fragment. Nat and Vec are additional
    primitives, not derived finite Kan extensions. No universes, identity,
    eta, induction eliminators or dependent metatheory are supplied here. *)
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

(** Contexts are nearest-binder first. An entry is written in its older tail
    context, not in the full context. Pi/Sigma codomains bind index zero, and so
    do the codomain annotations of App and of Split; the domain annotation of
    App and of Split is written in the caller's context and binds nothing.
    Split's motive binds the pair; its body binds the first component at index
    one and the second at index zero.

    Public operations validate the entire context, expected types, annotations
    and every supplied term, including unused components. Raw atom labels are
    canonicalized for comparison and duplicate labels are rejected.

    One shared budget meters context entries and all visited type/term nodes
    during formation, checking, reduction, weakening and substitution. Sorting,
    list lookup, structural equality, allocation and the host stack are not
    metered. Inputs must be finite acyclic OCaml values. Nonpositive fuel is
    inconclusive [Error Resource_exhausted], never acceptance. *)
val check_type : fuel:int -> context:ty list -> ty -> (unit, error) result
val check : fuel:int -> context:ty list -> term -> ty -> (unit, error) result

(** Check before normalizing. Reduction traverses types, indices, annotations
    and binder bodies, retains neutral applications and splits, and performs
    only application and split beta reduction. No eta rule is applied. *)
val normalize_type : fuel:int -> context:ty list -> ty -> (ty, error) result
val normalize : fuel:int -> context:ty list -> term -> ty -> (term, error) result

(** Validate and normalize both operands, left first, with the same remaining
    budget. Compare canonical normal forms structurally, including normalized
    annotations. Even identical inputs are checked; errors never become false.
    These decisions have no declarative soundness/completeness proof yet. *)
val convert_types : fuel:int -> context:ty list -> ty -> ty -> (bool, error) result
val convert : fuel:int -> context:ty list -> term -> term -> ty ->
  (bool, error) result

(** Check the replacement in context, then the body in replacement_type ::
    context, and remove the nearest binder by capture-avoiding substitution.
    [expected] is written in that extended context and may mention index zero.
    Substitution traverses indices and annotations as well as term bodies.
    The output has the instantiated expected type; it is not rechecked. *)
val substitute : fuel:int -> context:ty list -> replacement:term ->
  replacement_type:ty -> term -> ty -> (term, error) result
val substitute_type : fuel:int -> context:ty list -> replacement:term ->
  replacement_type:ty -> ty -> (ty, error) result
