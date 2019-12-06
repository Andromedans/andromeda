(** Types for pattern matching *)
module Patt =
struct

  type is_type_whnf' =
    | TypeConstructor of Ident.t * argument list
    | TypeFreeMeta of Nonce.t * is_term' list

  and is_type' =
    | TypeAddMeta of int
    | TypeCheckMeta of int
    | TypeWhnf of is_type_whnf'

  and is_term_whnf' =
    | TermConstructor of Ident.t * argument list
    | TermFreeMeta of Nonce.t * is_term' list
    | TermAtom of Nonce.t

  and is_term' =
    | TermAddMeta of int
    | TermCheckMeta of int
    | TermWhnf of is_term_whnf'

  and argument =
    | ArgumentIsType of is_type'
    | ArgumentIsTerm of is_term'

  (** the exported types also record how many meta-variables we're capturing. *)
  type is_term = is_term' * int
  type is_type = is_type' * int

end



(** We index rules by the heads of expressions, which can be identifiers or meta-variables (nonces). *)
type symbol =
  | Ident of Ident.t
  | Nonce of Nonce.t

exception Equality_fail

exception Invalid_rule

(** A tag to indicate that a term or a type is in whnf form *)
type 'a whnf = Whnf of 'a

let invalid_rule () = raise Invalid_rule

let equality_fail () = raise Equality_fail

let compare_symbol x y =
  match x, y with
  | Ident _, Nonce _ -> -1
  | Ident i, Ident j -> Ident.compare i j
  | Nonce n, Nonce m -> Nonce.compare n m
  | Nonce _, Ident _ -> 1

module SymbolMap = Map.Make(
                   struct
                     type t = symbol
                     let compare = compare_symbol
                   end)

(** Is an exposed premise an object premise? *)
let rec is_object_premise = function
  | Nucleus_types.(NotAbstract (BoundaryIsType _ | BoundaryIsTerm _)) -> true
  | Nucleus_types.(NotAbstract (BoundaryEqType _ | BoundaryEqTerm _)) -> false
  | Nucleus_types.Abstract (_, _, prem) -> is_object_premise prem

(** The head symbol of an exposed term. *)
let head_symbol_term e =
  let rec fold = function
    | Nucleus_types.TermBoundVar _ -> assert false
    | Nucleus_types.(TermAtom {atom_nonce=n; _}) -> Nonce n
    | Nucleus_types.TermConstructor (c, _) -> Ident c
    | Nucleus_types.(TermMeta (MetaFree {meta_nonce=n;_}, _)) -> Nonce n
    | Nucleus_types.(TermMeta (MetaBound _, _)) -> assert false
    | Nucleus_types.TermConvert (e, _, _) -> fold e
  in
  fold e


(** The head symbol of an exposed type. *)
let head_symbol_type = function
  | Nucleus_types.TypeConstructor (c, _) -> Ident c
  | Nucleus_types.(TypeMeta (MetaFree {meta_nonce=n;_}, _)) -> Nonce n
  | Nucleus_types.(TypeMeta (MetaBound _, _)) -> assert false

(** Apply rap to a list of arguments *)
let rap_apply_args rap args =
  let rec fold rap args =
  match rap, args with
  | rap, [] -> rap
  | Nucleus.RapMore (_bdry, f), arg :: args -> fold (f arg) args
  | Nucleus.RapDone _, _::_ -> assert false
  in
  try
    Some (fold rap args)
  with
  | Nucleus.Error _ -> None
