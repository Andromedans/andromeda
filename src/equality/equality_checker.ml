(** Type-directed equality checking based on user-provided rules. *)

(** The types of beta rules. *)
type type_beta_rule
type term_beta_rule

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
   type_beta_rules : type_beta_rule list SymbolMap.t ;
   term_beta_rules : term_beta_rule list SymbolMap.t ;
   ext_rules : extensionality_rule list SymbolMap.t
  }

exception Invalid_rule


let empty_checker = {
    type_beta_rules = SymbolMap.empty ;
    term_beta_rules = SymbolMap.empty ;
    ext_rules = SymbolMap.empty
  }


let make_type_beta_rule sgn drv =
  (??)

let make_term_beta_rule sgn drv =
  (??)

let make_ext_rule sgn drv =
  (??)

let add_type_beta checker sgn drv =
  let sym, bt = make_type_beta_rule sgn drv in
  { checker with type_beta_rules = SymbolMap.add sym bt checker.type_beta_rules }

let add_term_beta checker sgn drv =
  let sym, bt = make_term_beta_rule sgn drv in
  { checker with term_beta_rules = SymbolMap.add sym bt checker.term_beta_rules }

let add_extensionality checker sgn drv =
  let sym, bt = make_ext_rule sgn drv in
  { checker with ext_rules = SymbolMap.add sym bt checker.ext_rules }


let apply_type_beta chk ty = (??)

let apply_term_beta chk e = (??)

let find_extensionality chk sgn e1 e2 ty = (??)


(** A local exception for signaling failure of equality check. *)
exception Equality_fail

(* A tag to indicate entities in whnf form *)
type 'a whnf = Whnf of 'a


let rec prove_eq_type_abstraction chk sgn abstr =
  match Nucleus.invert_eq_type_boundary_abstraction abstr with

  | Nucleus.Stump_NotAbstract eq ->
     Nucleus.(abstract_not_abstract ((prove_eq_type chk sgn eq)))

  | Nucleus.Stump_Abstract (atm, abstr) ->
     let abstr = prove_eq_type_abstraction chk sgn abstr in
     Nucleus.abstract_eq_type atm abstr

and prove_eq_term_abstraction chk sgn abstr =
  match Nucleus.invert_eq_term_boundary_abstraction abstr with

  | Nucleus.Stump_NotAbstract bdry ->
     Nucleus.(abstract_not_abstract ((prove_eq_term chk sgn bdry)))

  | Nucleus.Stump_Abstract (atm, abstr) ->
     let abstr = prove_eq_term_abstraction chk sgn abstr in
     Nucleus.abstract_eq_term atm abstr


and prove_eq_type chk sgn (ty1, ty2) =
  let ty1_eq_ty1', ty1' = whnf_type chk sgn ty1
  and ty2_eq_ty2', ty2' = whnf_type chk sgn ty2 in
  let ty1'_eq_ty2' = check_whnf_type chk sgn ty1' ty2' in
  Nucleus.transitivity_type
    (Nucleus.transitivity_type ty1_eq_ty1' ty1'_eq_ty2')
    (Nucleus.symmetry_type ty2_eq_ty2')


and prove_eq_term chk sgn bdry =
  let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
  match find_extensionality chk sgn e1 e2 t with

  | Some rap ->
     (* reduce the problem to an application of an extensionality rule *)
     resolve_rap chk sgn rap

  | None ->
     (* normalization phase *)
     let e1_eq_e1', e1' = whnf_term chk sgn e1
     and e2_eq_e2', e2' = whnf_term chk sgn e2 in
     let e1'_eq_e2' = check_whnf_term chk sgn e1' e2' in
     Nucleus.transitivity_term
       (Nucleus.transitivity_term e1_eq_e1' e1'_eq_e2')
       (Nucleus.symmetry_term e2_eq_e2')


and check_whnf_type chk sgn (Whnf ty1) (Whnf ty2) =
  match Nucleus.congruence_is_type sgn ty1 ty2 with

  | None -> raise Equality_fail

  | Some rap -> resolve_rap chk sgn rap

and check_whnf_term chk sgn (Whnf e1) (Whnf e2) =
  match Nucleus.congruence_is_term sgn e1 e2 with

  | None -> raise Equality_fail

  | Some rap -> resolve_rap chk sgn rap


(** Given a rule application, fill in the missing premises, as long as they
    are equations. *)
and resolve_rap :
  'a . checker -> Nucleus.signature -> 'a Nucleus.rule_application -> 'a
  = fun chk sgn rap ->
  let rec fold = function

    | Nucleus.RapDone ty1_eq_ty2 -> ty1_eq_ty2

    | Nucleus.RapMore (bdry, rap) ->
       let eq = prove_boundary_abstraction chk sgn bdry in
       fold (rap eq)
  in
  fold rap

and prove_boundary_abstraction chk sgn bdry =
  let rec check bdry =
  match Nucleus.invert_boundary_abstraction bdry with

  | Nucleus.(Stump_NotAbstract (BoundaryEqType eq)) ->
     Nucleus.(abstract_not_abstract (JudgementEqType (prove_eq_type chk sgn eq)))

  | Nucleus.(Stump_NotAbstract (BoundaryEqTerm eq)) ->
     Nucleus.(abstract_not_abstract (JudgementEqTerm (prove_eq_term chk sgn eq)))

  | Nucleus.Stump_Abstract (atm, abstr) ->
     let eq_abstr = check abstr in
     Nucleus.abstract_judgement atm eq_abstr

  | Nucleus.(Stump_NotAbstract (BoundaryIsTerm _ | BoundaryIsType _)) ->
     assert false

  in
  check bdry

and whnf_type chk sgn ty =
  let rec fold ty_eq_ty' ty' =

    match apply_type_beta chk ty' with

    | None -> ty_eq_ty', Whnf ty'

    | Some (ty'_eq_ty'', ty'') ->
       let ty_eq_ty'' = Nucleus.transitivity_type ty_eq_ty' ty'_eq_ty'' in
       fold ty_eq_ty'' ty''
  in
  fold (Nucleus.reflexivity_type ty) ty

and whnf_term chk sgn term =
  (??)
