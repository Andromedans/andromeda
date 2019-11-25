(** Type-directed equality checking based on user-provided rules. *)

(** The type of beta rules. *)
type beta_rule

(** The type of extensionality rules. *)
type extensionality_rule

(** We index rules by the heads of expressions, which canb be
    identifiers or meta-variables (nonces). *)
type symbol =
  | Ident of Ident.t
  | Nonce of Nonce.t

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

type checker = {
   beta_rules : beta_rule list SymbolMap.t ;
   ext_rules : extensionality_rule list SymbolMap.t
  }

exception Invalid_rule

let empty_checker = {
    beta_rules = SymbolMap.empty ;
    ext_rules = SymbolMap.empty
  }

let make_beta_rule sgn drv =
  (??)

let make_ext_rule sgn drv =
  (??)

let add_beta checker sgn drv =
  let sym, bt = make_beta_rule sgn drv in
  { checker with beta_rules = SymbolMap.add sym bt checker.beta_rules }

let add_extensionality checker sgn drv =
  let sym, bt = make_ext_rule sgn drv in
  { checker with ext_rules = SymbolMap.add sym bt checker.ext_rules }

let rec check_eqtype chk sgn ty1_abstr ty2_abstr =
  (??)

and check_eqterm chk sgn trm1_abstr trm2_abstr =
  (??)

and whnf_type chk sgn ty =
  (??)

and whnf_term chk sgn term =
  (??)
