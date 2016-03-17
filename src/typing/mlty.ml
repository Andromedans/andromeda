type ty_param = int

type ty =
  | Judgement
  | String
  | Ident
  | Handler of ty * ty
  | Arrow of ty * ty
  | Tuple of ty list
  | Apply of Name.ty * ty list
  | Param of ty_param

module Ctx = struct

  type scoping =
    | Lexical
    | Dynamic

  type elt =
    | Variable of scoping * ty
    | Constant
    | Constructor of (ty list * ty)
    | Operation of (ty list * ty)
    | Signature

  type t = (Name.ident * elt) list
  let empty : t = []

  let rec is_decl x ys =
    match ys with
    | [] -> false
    | (y, _) :: _ when Name.eq_ident x y -> true
    | (_, Variable _) :: ys -> is_decl x ys
    | _ :: ys -> is_decl x ys

  let add_bound : t -> Name.ident -> ty -> t =
    fun ctx x t -> (x, Variable (Lexical, t)) :: ctx

  let add_operation ~loc ctx op tys =
    (op, Operation tys) :: ctx

  let add_Constructor ~loc ctx d tys =
    (d, Constructor tys) :: ctx

  let add_Constantant ~loc ctx c =
    (c, Constant) :: ctx

  let add_signature ~loc ctx s =
    (s, Signature) :: ctx

  let add_dynamic ctx x t =
    (x, Variable (Dynamic, t)) :: ctx


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

  (* | Syntax.DeclType (t, params, Constantrs) -> ctx *)

  (* | Syntax.DeclOperationeration (op, params, args, res) -> ctx *)

  (* | Syntax.DeclConstantants (xs, c) -> ctx *)

  (* | Syntax.DeclSignaturenature (s, lxcs) -> ctx *)

  (* | Syntax.TopHandle lst -> ctx *)

  (* | Syntax.TopLet xcs -> ctx *)

  (* | Syntax.TopLetRec fxcs -> ctx *)

  (* | Syntax.TopDynamic (x,c) -> ctx *)

  (* | Syntax.TopNow (x,c) -> ctx *)

  (* | Syntax.TopDo c -> ctx *)

  (* | Syntax.TopFail c -> *)
  (*    let c = Lazy.force c in *)
  (*    ctx *)
