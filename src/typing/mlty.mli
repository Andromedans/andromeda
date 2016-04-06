(** Type checking of the metalanguage. *)

type meta

module MetaOrd : sig
  type t = meta

  val compare : t -> t -> int
end

type ty =
  | Jdg
  | String
  | Meta of meta
  | Prod of ty list
  | Arrow of ty * ty
  | Handler of ty * ty
  | App of Name.ident * Syntax.level * ty list
  | Ref of ty

(** The unit type encoded as an empty product. *)
val unit_ty : ty

val fresh_meta : unit -> meta

val fresh_type : unit -> ty

(** The metavariables are generalised in the following values. *)
type 'a forall = meta list * 'a

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

exception Error of error Location.located

val error : loc:Location.t -> error -> 'a

type print_env

val fresh_penv : unit -> print_env

val print_ty : penv:print_env -> ?max_level:Level.t -> ty -> Format.formatter -> unit

val print_error : error -> Format.formatter -> unit


val occurs : meta -> ty -> bool

module MetaSet : Set.S with type elt = meta

val occuring : ty -> MetaSet.t

val occuring_schema : ty_schema -> MetaSet.t

