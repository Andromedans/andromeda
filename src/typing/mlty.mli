(** ML types and basic operations on them. *)

(** The type of metavariables. *)
type meta

(** The type of type parameters. *)
type param

(** Metavariables are an ordered type. Used for [Map.Make]. *)
module MetaOrd : sig
  type t = meta

  val compare : t -> t -> int
end

(** Sets of metavariables. *)
module MetaSet : Set.S with type elt = meta

(** AML typing keeps track of judgement forms *)
type judgement =
  | IsType
  | IsTerm
  | EqType
  | EqTerm

(** AML typing keeps track of TT abstractions (without dependencies) *)
type abstracted_judgement =
  | NotAbstract of judgement
  | Abstract of abstracted_judgement

(** The type of ML types. *)
type ty =
  | Judgement of abstracted_judgement
  | String
  | Meta of meta
  | Param of param
  | Prod of ty list
  | Arrow of ty * ty
  | Handler of ty * ty
  | App of Name.ident * Dsyntax.level * ty list
  | Ref of ty
  | Dynamic of ty

(** The AML type of a TT constructor. *)
type tt_constructor_ty = abstracted_judgement list * judgement

(** The unit type encoded as an empty product. *)
val unit_ty : ty

(** Generate a fresh metavariable *)
val fresh_meta : unit -> meta

(** Generate a fresh type parameter *)
val fresh_param : unit -> param

(** Generate a fresh metavariable as a type *)
val fresh_type : unit -> ty

(** The parameters are bound in the following values. *)
type 'a forall = param list * 'a

(** The type of type schemas, i.e. polymorphic types. *)
type ty_schema = ty forall

(** An AML constructor name and the expected types of its arguments. *)
type aml_constructor = Name.aml_constructor * ty list

(** The type of type definitions. *)
type ty_def =
  | Alias of ty forall
  | Sum of aml_constructor list forall

(** The errors reported by type inference. *)
type error =
  | InvalidApplication of ty * ty * ty
  | TypeMismatch of ty * ty
  | UnsolvedApp of ty * ty * ty
  | HandlerExpected of ty
  | RefExpected of ty
  | DynamicExpected of ty
  | UnknownExternal of string
  | ValueRestriction
  | Ungeneralizable of param list * ty
  | JudgementExpected of ty
  | UnexpectedJudgement of judgement
  | UnexpectedJudgementAbstraction of judgement

exception Error of error Location.located

(** Convenience function to raise an error. *)
val error : loc:Location.t -> error -> 'a

(** The type of printing environments, which ensure readable printing of metavariables and type parameters. Mutable. *)
type print_env

(** Get a fresh printing environment. *)
val fresh_penv : unit -> print_env

(** Print a type according to the given printing environment, which may be modified. *)
val print_ty : penv:print_env -> ?max_level:Level.t -> ty -> Format.formatter -> unit

(** Print a type schema according to the given printing environment, which may be modified. *)
val print_ty_schema :  penv:print_env -> ?max_level:Level.t -> ty_schema -> Format.formatter -> unit

(** Print a typing error according to the given printing environment, which may be modified. *)
val print_error : error -> Format.formatter -> unit

(** Does the given metavariable occur in the given type? *)
val occurs : meta -> ty -> bool

(** Get the set of metavariables which occur in the given type. *)
val occuring : ty -> MetaSet.t

(** Get the set of metavariables which occur in the given type schema. *)
val occuring_schema : ty_schema -> MetaSet.t

(** Instantiate the type parameters with the associated types in the given type. *)
val instantiate : (param * ty) list -> ty -> ty

(** Do any of the given parameters appear in the given type? *)
val params_occur : param list -> ty -> bool
