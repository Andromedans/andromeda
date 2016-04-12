(** Type checking of the metalanguage. *)

type meta

type param

module MetaOrd : sig
  type t = meta

  val compare : t -> t -> int
end

module MetaSet : Set.S with type elt = meta

type ty =
  | Jdg
  | String
  | Meta of meta
  | Param of param
  | Prod of ty list
  | Arrow of ty * ty
  | Handler of ty * ty
  | App of Name.ident * Syntax.level * ty list
  | Ref of ty

(** The unit type encoded as an empty product. *)
val unit_ty : ty

(** Generate a fresh meta variable *)
val fresh_meta : unit -> meta

(** Generate a fresh type parameter *)
val fresh_param : unit -> param

(** Generate a fresh meta variable as a type *)
val fresh_type : unit -> ty

(** The metavariables are generalised in the following values. *)
type 'a forall = param list * 'a

type ty_schema = ty forall

type constructor = Name.constructor * ty list

type ty_def =
  | Alias of ty forall
  | Sum of constructor list forall

(** Make a schema from a type without generalizing anything. *)
val ungeneralized_schema : ty -> ty_schema


(** The errors reported by type inference. *)
type error =
  | InvalidApplication of ty * ty * ty
  | TypeMismatch of ty * ty
  | UnsolvedApp of ty * ty * ty
  | HandlerExpected of ty
  | RefExpected of ty
  | UnknownExternal of string
  | ValueRestriction
  | Ungeneralizable of param list * ty

exception Error of error Location.located

val error : loc:Location.t -> error -> 'a

type print_env

val fresh_penv : unit -> print_env

val print_ty : penv:print_env -> ?max_level:Level.t -> ty -> Format.formatter -> unit

val print_ty_schema :  penv:print_env -> ?max_level:Level.t -> ty_schema -> Format.formatter -> unit

val print_error : error -> Format.formatter -> unit


val occurs : meta -> ty -> bool

val occuring : ty -> MetaSet.t

val occuring_schema : ty_schema -> MetaSet.t

(** Instantiate the type parameters with the given types. *)
val instantiate : (param * ty) list -> ty -> ty

(** Do any of the given parameters appear in the given type? *)
val params_occur : param list -> ty -> bool
