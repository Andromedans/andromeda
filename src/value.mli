(** Abstract syntax of types and terms. *)

type term = term' * Position.t
and term' = private
  | Type
  | Name of Common.name (** a free variable *)
  | Bound of Common.bound (** a bound variable *)
  | Lambda of (ty, term * ty) abstraction
    (** a lambda abstraction [fun (x1:A1) ... (xn:An) -> e : A] where
        [Ak] depends on [x1, ..., x{k-1}], while [e] and [A] depends on
        [x1, ..., xn] *)
  | Spine of term * (term * ty, ty) abstraction
    (** a spine [e [(x1,(e1,A1)); ..., (xn,(en,An))] : A] means that
        [e] is applied to [e1, ..., en], and that the type of [e] has type
        [forall (x1:A1) ... (xn:An), A]. Here again [Ak] depends on
        [x1, ..., x{k-1}] and [A] depends on [x1, ..., xn]. *)
  | Prod of (ty, ty) abstraction
    (** dependent product [forall (x1:A1) ... (xn:An), A], where [Ak] depends on
        [x1, ..., x{k-1}] and [A] depends on [x1, ..., xn]. *)
  | Eq of ty * term * term
    (** strict equality type [e1 == e2] where [e1] and [e2] have type [A]. *)
  | Refl of ty * term (** reflexivity [refl e] where [e] has type [A]. *)

(** Since we have [Type : Type] we do not distinguish terms from types,
    so the type of type [ty] is just a synonym for the type of terms. 
    However, we tag types with the [Ty] constructor to avoid nasty bugs. *)
and ty = private
    | Ty of term

(** An [(A,B) abstraction] is a [B] bound by [x1:a1, ..., xn:an] where
    the [a1, ..., an] have type [A]. *)
and ('a, 'b) abstraction = (Common.name * 'a) list * 'b

(** A value is the result of a computation. *)
type value = term * ty

(** A result of computation *)
type result =
  | Return of value

(** Term constructors *)
val mk_name: loc:Position.t -> Common.name -> term
val mk_bound: loc:Position.t -> Common.bound -> term
(* val mk_lambda: loc:Position.t -> (ty, term * ty) abstraction *)
(* val mk_spine: loc:Position.t -> term -> (term * ty, term) abstraction *)
val mk_type: loc:Position.t -> term
(* val mk_prod: loc:Position.t -> Common.name -> (ty, ty) abstraction *)
val mk_eq: loc:Position.t -> ty -> term -> term -> term
val mk_eq_ty: loc:Position.t -> ty -> term -> term -> ty
val mk_refl: loc:Position.t -> ty -> term -> term

(** Construct a value to a type (does not check whether this is legal). *)
val ty : term -> ty

(** The type Type *)
val typ : ty

(** Alpha equality of terms *)
val equal : term -> term -> bool

(** Alpha equality of types *)
val equal_ty : ty -> ty -> bool

(** Partially instantiate a lambda abstraction. Since the number of supplied
    terms may be greater than the number of arguments, we also return the
    list of unused terms. *)
val instantiate :
  term list ->
  (ty, term * ty) abstraction ->
  (ty, term * ty) abstraction * term list

(** Does de Bruijn index 0 get used in the given term? *)
val occurs : term -> bool

(** Does de Bruijn index 0 get used in the given type? *)
val occurs_ty : ty -> bool
