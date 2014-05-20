(** Annotated abstract syntax for Brazilian type theory. *)

type name = string

(** We use de Bruijn indices *)
type variable = Common.debruijn

type universe = Universe.t

type ty = ty' * Position.t
and ty' =
  | Universe of universe
  | El of universe * term
  | Unit
  | Prod of name * ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term = term' * Position.t
and term' =
  | Var of variable
  | Equation of term * ty * term
  | Rewrite of term * ty * term
  | Ascribe of term * ty
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | UnitTerm
  | Idpath of ty * term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of ty * term
  | Coerce of universe * universe * term
  | NameUnit
  | NameProd of universe * universe * name * term * term
  | NameUniverse of universe
  | NamePaths of universe * term * term * term
  | NameId of universe *term * term * term


(*********************************)
(* Construction helper functions *)
(*********************************)

val mkUniverse : ?loc:Position.t -> universe -> ty
val mkEl : ?loc:Position.t -> universe -> term  -> ty
val mkUnit : ?loc:Position.t -> unit  -> ty
val mkProd : ?loc:Position.t -> name -> ty -> ty  -> ty
val mkPaths : ?loc:Position.t -> ty -> term -> term -> ty
val mkId  : ?loc:Position.t -> ty -> term -> term -> ty

val make_arrow: ?loc:Position.t -> ty -> ty -> ty

val mkVar : ?loc:Position.t -> variable -> term
val mkEquation : ?loc:Position.t -> term -> ty -> term -> term
val mkRewrite : ?loc:Position.t -> term -> ty -> term -> term
val mkAscribe : ?loc:Position.t -> term -> ty -> term
val mkLambda : ?loc:Position.t -> name -> ty -> ty -> term -> term
val mkApp : ?loc:Position.t -> name -> ty -> ty -> term -> term -> term
val mkUnitTerm : ?loc:Position.t -> unit -> term
val mkIdpath : ?loc:Position.t -> ty -> term -> term
val mkJ : ?loc:Position.t -> ty -> (name*name*name*ty) -> (name*term) -> term -> term -> term -> term
val mkRefl : ?loc:Position.t -> ty -> term -> term
val mkCoerce : ?loc:Position.t -> universe -> universe -> term -> term
val mkNameUnit : ?loc:Position.t -> unit -> term
val mkNameProd : ?loc:Position.t -> universe -> universe -> name -> term -> term -> term
val mkNameUniverse : ?loc:Position.t -> universe -> term
val mkNamePaths : ?loc:Position.t -> universe -> term -> term -> term -> term
val mkNameId : ?loc:Position.t -> universe -> term -> term -> term -> term



(********)
(* Code *)
(********)

(** Anonymous identifier *)
val anonymous : name

(** alpha equality of terms, ignoring hints *)
val equal    : term -> term -> bool

(** alpha equality of types, ignoring hints inside terms *)
val equal_ty : ty -> ty -> bool

(** [shift delta term] shifts the free variables in [term] by [delta],
    raising [exn] if a negative variable is produced by the shift.
    Variables whose index is below [bound] are considered bound and therefore
    not shifted. *)
val shift : ?exn:exn -> ?bound:int -> int -> term -> term

(** [shift_ty delta ty] shifts the free variables in [ty] by [delta],
    raising [exn] if a negative variable is produced by the shift.
    Variables whose index is below [bound] are considered bound and therefore
    not shifted. *)
val shift_ty : ?exn:exn -> ?bound:int -> int -> ty -> ty

(**
  If [G, x:t |- body : ...] and [G |- arg : t] then
  [beta body arg] is the substituted term [body[x->arg]].

  This is exactly the substitution required, for example, to
  beta-reduce a function application ([body] is the body of the lambda).
*)
val beta    : term -> term -> term

(**
  If [G, x:t |- body : type] and [G |- arg : t] then
  [beta_ty body arg] is the substituted type [body[x->arg]].

  This is exactly the substitution required, for example, to
  to substitute away the parameter in a [Pi] or [Sigma] type ([body] is
  the type of the codomain or second component, respectively).
*)
val beta_ty : ty -> term -> ty

(**
  If [G, x_1:t_1, .., x_n:t_n |- body : type] and [G |- arg_i : t_i]
  [betas_ty body [arg_1; ...; arg_n]] is the substituted type
  [G |- body[x_1->arg_1, ..., x_n->arg_n]].
*)
val betas_ty : ty -> term list -> ty


(**
  Suppose we have [G, x_1:t_1, ..., x_n:t_n |- exp : ...] and the inhabitants
  [e_1; ...; e_n] all well-formed in (i.e., indexed relative to) [G] (!).  Then
  [strengthen exp [e_1,...,e_n]] is the result of substituting away the
  [x_i]'s, resulting in a term well-formed in [G].

  In particular, [strengthen eBody [eArg]] is just [beta eBody eArg].
 *)
val strengthen    : term -> term list -> term

(** Like [strengthen], but for types *)
val strengthen_ty : ty   -> term list -> ty


(** If [G |- exp] then [G' |- weaken i exp], where [G'] has
    one extra (unused) variable inserted at former position [i]. The name of
    that variable doesn't matter, because we're in de Bruijn notation.

    E.g., if   [x3, x2,    x1, x0 |- e : t] then
          then [x3, x2, z, x1, x0 |- (weaken 2 e) : (weaken_ty 2 t)]

    In particular, [weaken 0 e] is the same as [shift 1 e].
*)
val weaken : int -> term -> term

(** Like [weaken], but for types *)
val weaken_ty : int -> ty -> ty

(** Try to compute the name of a type *)
val name_of : ty -> (term * universe) option

(** Check for occurrences of a free variable in a term *)
val occurs : Common.debruijn -> term -> bool

(** Check for occurrences of a free variable in a type *)
val occurs_ty : Common.debruijn -> ty -> bool


(** Simplify a term *)
val simplify : term -> term

(** Simplify a type *)
val simplify_ty : ty -> ty
