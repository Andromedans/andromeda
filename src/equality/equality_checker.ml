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


(** A local exception for signaling failure of equality check. *)
exception Equality_fail

(* A tag to indicate entities in whnf form *)
type 'a whnf = Whnf of 'a


let rec check_type_abstraction chk sgn ty1_abstr ty2_abstr =
  let rec check ty1_abstr ty2_abstr =
    match Nucleus.type_at_abstraction ty1_abstr,
          Nucleus.type_at_abstraction ty2_abstr
    with

    | None, None ->
       begin match Nucleus.(as_not_abstract ty1_abstr, as_not_abstract ty2_abstr) with
       | Some ty1, Some ty2 ->
          let ty1_eq_ty2 = check_type chk sgn ty1 ty2 in
          Nucleus.abstract_not_abstract ty1_eq_ty2

       | (None, _) | (_, None) ->
          assert false
       end

    | Some u1, Some u2 ->
       let u1_eq_u2 = check_type chk sgn u1 u2 in
       begin match Nucleus.invert_is_type_abstraction ty1_abstr with

       | Nucleus.Stump_NotAbstract _ -> assert false

       | Nucleus.Stump_Abstract (atm1, ty1_abstr) ->
          let atm2 = Nucleus.(form_is_term_convert sgn (form_is_term_atom atm1) u1_eq_u2) in
          let ty2_abstr = Nucleus.apply_is_type_abstraction sgn ty2_abstr atm2 in
          let eq = check ty1_abstr ty2_abstr in
          Nucleus.abstract_eq_type atm1 eq
       end

    | ((Some _, None) | (None, Some _)) ->
       raise Equality_fail

  in
  check ty1_abstr ty2_abstr

and check_term_abstraction chk sgn trm1_abstr trm2_abstr =
  let rec check trm1_abstr trm2_abstr =
    match Nucleus.type_at_abstraction trm1_abstr,
          Nucleus.type_at_abstraction trm2_abstr
    with

    | None, None ->
       begin match Nucleus.(as_not_abstract trm1_abstr, as_not_abstract trm2_abstr) with
       | Some e1, Some e2 ->
          let e1_eq_e2 = check_term chk sgn e1 e2 in
          Nucleus.abstract_not_abstract e1_eq_e2

       | (None, _) | (_, None) ->
          assert false
       end

    | Some u1, Some u2 ->
       let u1_eq_u2 = check_type chk sgn u1 u2 in
       begin match Nucleus.invert_is_term_abstraction trm1_abstr with

       | Nucleus.Stump_NotAbstract _ -> assert false

       | Nucleus.Stump_Abstract (atm1, trm1_abstr) ->
          let atm2 = Nucleus.(form_is_term_convert sgn (form_is_term_atom atm1) u1_eq_u2) in
          let trm2_abstr = Nucleus.apply_is_term_abstraction sgn trm2_abstr atm2 in
          let eq = check trm1_abstr trm2_abstr in
          Nucleus.abstract_eq_term atm1 eq
       end

    | ((Some _, None) | (None, Some _)) ->
       raise Equality_fail
  in
  check trm1_abstr trm2_abstr


and check_type chk sgn ty1 ty2 =
  let ty1_eq_ty1', ty1' = whnf_type chk sgn ty1
  and ty2_eq_ty2', ty2' = whnf_type chk sgn ty2 in
  let ty1'_eq_ty2' = check_whnf_type chk sgn ty1' ty2' in
  Nucleus.transitivity_type
    (Nucleus.transitivity_type ty1_eq_ty1' ty1'_eq_ty2')
    (Nucleus.symmetry_type ty2_eq_ty2')

and check_term chk sgn e1 e2 =
  (* XXX missing type-directed phase *)
  let e1_eq_e1', e1' = whnf_term chk sgn e1
  and e2_eq_e2', e2' = whnf_term chk sgn e2 in
  let e1'_eq_e2' = check_whnf_term chk sgn e1' e2' in
  Nucleus.transitivity_term
    (Nucleus.transitivity_term e1_eq_e1' e1'_eq_e2')
    (Nucleus.symmetry_term e2_eq_e2')

and check_whnf_type chk sgn (Whnf ty1) (Whnf ty2) =
  match Nucleus.congruence_is_type sgn ty1 ty2 with

  | None -> raise Equality_fail

  | Some rap -> apply_congruence chk sgn rap

and check_whnf_term chk sgn (Whnf e1) (Whnf e2) =
  match Nucleus.congruence_is_term sgn e1 e2 with

  | None -> raise Equality_fail

  | Some rap -> apply_congruence chk sgn rap

and apply_congruence :
  'a . checker -> Nucleus.signature -> 'a Nucleus.rule_application -> 'a
  = fun chk sgn rap ->
  let rec fold = function

    | Nucleus.RapDone ty1_eq_ty2 -> ty1_eq_ty2

    | Nucleus.RapMore (bdry, rap) ->
       let eq = check_boundary_abstraction chk sgn bdry in
       fold (rap eq)
  in
  fold rap

and check_boundary_abstraction chk sgn bdry =
  let rec check bdry =
  match Nucleus.invert_boundary_abstraction bdry with

  | Nucleus.(Stump_NotAbstract (BoundaryEqType (ty1, ty2))) ->
     Nucleus.(abstract_not_abstract (JudgementEqType (check_type chk sgn ty1 ty2)))

  | Nucleus.(Stump_NotAbstract (BoundaryEqTerm bdry)) ->
     let (e1, e2, _) = Nucleus.invert_eq_term_boundary bdry in
     Nucleus.(abstract_not_abstract (JudgementEqTerm (check_term chk sgn e1 e2)))

  | Nucleus.Stump_Abstract (atm, abstr) ->
     let eq_abstr = check abstr in
     Nucleus.abstract_judgement atm eq_abstr

  | Nucleus.(Stump_NotAbstract (BoundaryIsTerm _ | BoundaryIsType _)) ->
     assert false

  in
  check bdry


and whnf_type chk sgn ty =
  (??)


and whnf_term chk sgn term =
  (??)
