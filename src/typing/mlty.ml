type ty_param = int

type ty =
  | Ident
  | Judgement
  | Handler of ty * ty
  | String
  | Arrow of ty * ty
  | Tuple of ty list
  | Apply of Name.ty * ty list
  | Param of ty_param

module Ctx = struct

  type scoping =
    | Lexical
    | Dynamic

  type elt =
    | Val of scoping * ty
    | Const
    | Data of (ty list * ty)
    | Op of (ty list * ty)
    | Sig

  type t = (Name.ident * elt) list
  let empty : t = []

  let rec is_decl x ys =
    match ys with
    | [] -> false
    | (y, _) :: _ when Name.eq_ident x y -> true
    | (_, Val _) :: ys -> is_decl x ys
    | _ :: ys -> is_decl x ys

  let add_bound : t -> Name.ident -> ty -> t =
    fun ctx x t -> (x, Val (Lexical, t)) :: ctx

  let add_operation ~loc ctx op tys =
    if is_decl op ctx
    then Error.runtime ~loc "operation %t is already declared" (Name.print_ident op)
    else (op, Op tys) :: ctx

  let add_data ~loc ctx d tys =
    if is_decl d ctx
    then Error.runtime ~loc "data constructor %t is already declared" (Name.print_ident d)
    else (d, Data tys) :: ctx

  let add_constant ~loc ctx c =
    if is_decl c ctx
    then Error.runtime ~loc "constant %t is already declared" (Name.print_ident c)
    else (c, Const) :: ctx

  let add_signature ~loc ctx s =
    if is_decl s ctx
    then Error.runtime ~loc "signature %t is already declared" (Name.print_ident s)
    else (s, Sig) :: ctx

  let add_dynamic ctx x t : t = (x, Val (Dynamic, t)) :: ctx


end

let infer ctx c =
  ctx (* TODO *)
  (* match c with *)

  (* | Syntax.Include_begin _ *)
  (* | Syntax.Include_end _ *)
  (* | Syntax.Verbosity _ *)
  (* | Syntax.Environment *)
  (* | Syntax.Help *)
  (* | Syntax.Quit -> *)
  (*    ctx *)

  (* | Syntax.DeclType (t, params, constrs) -> ctx *)

  (* | Syntax.DeclOperation (op, params, args, res) -> ctx *)

  (* | Syntax.DeclConstants (xs, c) -> ctx *)

  (* | Syntax.DeclSignature (s, lxcs) -> ctx *)

  (* | Syntax.TopHandle lst -> ctx *)

  (* | Syntax.TopLet xcs -> ctx *)

  (* | Syntax.TopLetRec fxcs -> ctx *)

  (* | Syntax.TopDynamic (x,c) -> ctx *)

  (* | Syntax.TopNow (x,c) -> ctx *)

  (* | Syntax.TopDo c -> ctx *)

  (* | Syntax.TopFail c -> *)
  (*    let c = Lazy.force c in *)
  (*    ctx *)
