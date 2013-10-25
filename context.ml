(** Context management *)

(** A context is represented as an associative list which maps a variable [x] to a pair
   [(t,e)] where [t] is its type and [e] is its value (optional).
*)

(** The entries in the context are declarations of parameters or definitions.
    A parameter declaration carries its type, while a definition carries the type and
    the defining expression. *)
type declaration =
  | Parameter of Syntax.ty
  | TyParameter of Syntax.kind
  | Definition of Syntax.ty * Syntax.expr
  | TyDefinition of Syntax.kind * Syntax.ty

(** A context consists of a list of names, used for pretty-printing and
    desugaring of variable names to de Bruijn indices, and a list of
    declarations. *)
type context = {
  names : string list ;
  decls : declaration list
}

(** On the zeroth day there was the empty context. *)
let empty_context = {
  names = [] ;
  decls = []
}

(** Drop the most recently added thing from the context. *)
let drop {names = ns; decls = ds} = {names = List.tl ns; decls = List.tl ds}

let shift_entry ?(c=0) d = function
  | Parameter t -> Parameter (Syntax.shiftTy ~c d t)
  | Definition (t, e) -> Definition (Syntax.shiftTy ~c d t, Syntax.shift ~c d e)
  | TyParameter k -> TyParameter (Syntax.shiftKind ~c d k)
  | TyDefinition (k, t) -> TyDefinition (Syntax.shiftKind ~c d k, Syntax.shiftTy ~c d t)

(** [lookup v ctx] returns the type or definition of [Var v] in context [ctx]. *)
let lookup v {decls=lst} =
  shift_entry (v+1) (List.nth lst v)

(** [lookup_ty v ctx] returns the type of [Var v] in context [ctx]. *)
let lookup_ty v ctx =
  let entry = lookup v ctx in
  match entry with
    | Parameter t | Definition (t, _) -> t
    | (TyParameter _ | TyDefinition _) ->
        Error.runtime "lookup_ty: index denotes a type variable"

let lookup_kind v ctx =
  let entry = lookup v ctx in
  match entry with
    | Parameter _ | Definition _ ->
        Error.runtime "lookup_kind: index denotes an expr variable"
    | TyParameter k | TyDefinition (k, _) -> k

(** [lookup_definition v ctx] returns the definition of [Var v] in context [ctx]. *)
let lookup_definition v ctx =
  let entry = lookup v ctx in
  match entry with
    | Definition (_, e) -> Some e
    | Parameter _       -> None
    | (TyParameter _ | TyDefinition _) ->
        Error.runtime "lookup_definition: index denotes a type variable"

(** [lookup_tydefinition v ctx] returns the definition of [TVar v] in context [ctx]. *)
let lookup_tydefinition v ctx =
  let entry = lookup v ctx in
  match entry with
    | TyDefinition (_, t) -> Some t
    | TyParameter _       -> None
    | (Parameter _ | Definition _) ->
        Error.runtime "lookup_tydefinition: index denotes a expr variable"

(** [add_parameter x t ctx] returns [ctx] with the parameter [x] of type [t]. *)
let add_parameter x t ctx =
  { names = x :: ctx.names ;
    decls = Parameter t :: ctx.decls }

(** [add_ty_parameter x k ctx] returns [ctx] with the parameter [x] of kind [k]. *)
let add_ty_parameter x k ctx =
  { names = x :: ctx.names ;
    decls = TyParameter k :: ctx.decls }

(** [add_definition x t e ctx] returns [ctx] with [x] of type [t] defined as [e]. *)
let add_definition x t e ctx =
  { names = x :: ctx.names ;
    decls = Definition (t, e) :: ctx.decls }

(** [add_ty_definition x k t ctx] returns [ctx] with [x] of kind [k] defined as [t]. *)
let add_ty_definition x k t ctx =
  { names = x :: ctx.names ;
    decls = TyDefinition (k, t) :: ctx.decls }


let print ctx =
  let names = ctx.names in
  let decls = ctx.decls in
  ignore
    (List.fold_left2
      (fun k x d ->
        (match (shift_entry (k+1) d) with
         | Parameter t ->
             Format.printf "@[%s : %t@]@." x (Print.ty names t)
         | Definition (t, e) ->
             Format.printf "@[%s = %t@]@\n    : %t@." x (Print.expr names e) (Print.ty names t)
         | TyParameter k ->
             Format.printf "@[%s : %t@]@." x (Print.kind  names k)
         | TyDefinition (k, t) ->
             Format.printf "@[%s = %t@]@\n    : %t@." x (Print.ty names t) (Print.kind names k));
             k + 1)
      0 names decls)


