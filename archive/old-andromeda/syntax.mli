(** Annotated abstract syntax for Andromedan type theory. *)

type name = string

type label = string

(** We use de Bruijn indices *)
type variable = Common.debruijn

type ty = ty' * Position.t
and ty' =
  | Type
  | El of term
  | RecordTy of (label * (name * ty)) list
  | Prod of name * ty * ty
  | Id of ty * term * term

and term = term' * Position.t
and term' =
  | Var of variable
  | Ascribe of term * ty
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | Spine of variable * ty * term list
  | Record of (label * (name * ty * term)) list
  | Project of term * (label * (name * ty)) list * label
  | Refl of ty * term
  | NameType
  | NameRecordTy of (label * (name * term)) list
  | NameProd of name * term * term
  | NameId of term * term * term

(*********************************)
(* Construction helper functions *)
(*********************************)

val mkType : ?loc:Position.t -> unit -> ty
val mkEl : ?loc:Position.t -> term  -> ty
val mkRecordTy : ?loc:Position.t -> (label * (name * ty)) list -> ty
val mkProd : ?loc:Position.t -> name -> ty -> ty  -> ty
val mkId  : ?loc:Position.t -> ty -> term -> term -> ty

val make_arrow: ?loc:Position.t -> ty -> ty -> ty

val mkVar : ?loc:Position.t -> variable -> term
val mkAscribe : ?loc:Position.t -> term -> ty -> term
val mkLambda : ?loc:Position.t -> name -> ty -> ty -> term -> term
val mkApp : ?loc:Position.t -> name -> ty -> ty -> term -> term -> term
val mkSpine : ?loc:Position.t -> variable -> ty -> term list -> term
val mkRecord : ?loc:Position.t -> (label * (name * ty * term)) list -> term
val mkProject : ?loc:Position.t -> term -> (label * (name * ty)) list -> label -> term
val mkRefl : ?loc:Position.t -> ty -> term -> term
val mkNameRecordTy : ?loc:Position.t -> (label * (name * term)) list -> term
val mkNameProd : ?loc:Position.t -> name -> term -> term -> term
val mkNameType : ?loc:Position.t -> unit -> term
val mkNameId : ?loc:Position.t -> term -> term -> term -> term


(********)
(* Code *)
(********)

(** Anonymous identifier *)
val anonymous : name

(** alpha equality of terms, ignoring hints *)
val equal : term -> term -> bool

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
val beta : term -> term -> term

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
val strengthen : term -> term list -> term

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

(** Check for occurrences of a free variable in a term *)
val occurs : Common.debruijn -> term -> bool

(** Check for occurrences of a free variable in a type *)
val occurs_ty : Common.debruijn -> ty -> bool


(** Simplify a term *)
val simplify : term -> term

(** Simplify a type *)
val simplify_ty : ty -> ty

val from_spine : ?loc:Position.t -> variable -> ty -> term list -> term
val fold_left_spine : Position.t ->
                            (name -> ty -> ty -> 'b -> term -> 'b) ->
                            'b -> ty -> term list -> 'b
val fold_left2_spine : Position.t ->
                            (name -> ty -> ty -> 'b -> 'a -> term -> 'b) ->
                            'b -> ty -> 'a list -> term list -> 'b

val whnf : ty -> term -> term
val whnf_ty : ty -> ty
