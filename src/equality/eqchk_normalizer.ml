(** Normalization *)

open Eqchk_common

let penv = Nucleus.({
              forbidden = Name.set_empty ;
              debruijn_var = [] ;
              debruijn_meta = [] ;
              opens = Path.set_empty
            })
let rec print_sequence seq ppf =
  match seq with
  | [] -> ()
  | arg :: args ->
    Format.printf "arg: %t@." (ppf arg) ;
    print_sequence args ppf

(** Extract an optional value, or declare an equality failure *)
let deopt x msg =
  match x with
  | None -> raise (Normalization_fail msg)
  | Some x -> x

(** The types of beta rules. *)

type normalizer =
  { type_computations : (Patt.is_type * Nucleus.eq_type Nucleus.rule) list SymbolMap.t ;
    type_heads : IntSet.t SymbolMap.t ;
    term_computations : (Patt.is_term * Nucleus.eq_term Nucleus.rule) list SymbolMap.t ;
    term_heads : IntSet.t SymbolMap.t
  }

let empty_normalizer =
  { type_computations = SymbolMap.empty ;
    type_heads = SymbolMap.empty ;
    term_computations = SymbolMap.empty ;
    term_heads = SymbolMap.empty }

let find_type_computations sym {type_computations;_} =
  SymbolMap.find_opt sym type_computations

let find_term_computations sym {term_computations;_} =
  SymbolMap.find_opt sym term_computations


(** Functions [make_XYZ] convert a derivation to a rewrite rule, or raise the exception [Invalid_rule] when the derivation
    has the wrong form. *)

let make_type_computation drv =
  let rec fold k  = function

    | Nucleus_types.(Conclusion eq)  ->
       let (Nucleus_types.EqType (_asmp, t1, _t2)) = Nucleus.expose_eq_type eq in
       let patt =  Eqchk_pattern.make_is_type k t1 in
       let s = head_symbol_type t1 in
       (s, patt)

    | Nucleus_types.(Premise ({meta_boundary=bdry;_}, drv)) ->
       if is_object_premise bdry then
         fold (k+1) drv
       else
         raise (Invalid_rule "premise of a computation rule does not have an object boundary")
  in
  let drv =
    match Nucleus.as_eq_type_rule drv with
    | Some drv -> drv
    | None -> raise (Invalid_rule "Conclusion not a type equality boundary")
  in
  let (s, patt) = fold 0 (Nucleus.expose_rule drv) in
  s, (patt, drv)


let make_term_computation drv =
  let rec fold k = function

    | Nucleus_types.(Conclusion eq) ->
       let (Nucleus_types.EqTerm (_asmp, e1, _e2, _t)) = Nucleus.expose_eq_term eq in
       let patt = Eqchk_pattern.make_is_term k e1 in
       let s = head_symbol_term e1 in
       (s, patt)

    | Nucleus_types.(Premise ({meta_boundary=bdry;_}, drv)) ->
       if is_object_premise bdry then
         fold (k+1) drv
       else
         raise (Invalid_rule "premise of a computation rule does not have an object boundary")
  in
  let drv =
    match Nucleus.as_eq_term_rule drv with
    | Some drv -> drv
    | None -> raise (Invalid_rule "Conclusion not a term equality boundary")
  in
  let (s, patt) = fold 0 (Nucleus.expose_rule drv) in
  s, (patt, drv)


let add_type_computation normalizer drv =
  let sym, bt = make_type_computation drv in
  let rls =
    match find_type_computations sym normalizer with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  sym, bt,
  { normalizer with type_computations = SymbolMap.add sym rls normalizer.type_computations }


let add_term_computation normalizer drv =
  let sym, bt = make_term_computation drv in
  let rls =
    match find_term_computations sym normalizer with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  sym, bt,
  { normalizer with term_computations = SymbolMap.add sym rls normalizer.term_computations }

let set_type_heads nrm sym heads =
  { nrm with type_heads = SymbolMap.add sym heads nrm.type_heads }

let set_term_heads normalizer sym heads =
  { normalizer with term_heads = SymbolMap.add sym heads normalizer.term_heads }

let get_type_heads nrm sym =
  match SymbolMap.find_opt sym nrm.type_heads with
  | None -> IntSet.empty
  | Some hs -> hs

let get_term_heads nrm sym =
  match SymbolMap.find_opt sym nrm.term_heads with
  | None -> IntSet.empty
  | Some hs -> hs

(** Functions that apply rewrite rules *)

let is_alpha_equal_type_arg arg t =
  try
  begin
  match Nucleus.(as_is_type (deopt (as_not_abstract arg) "")) with
  | Some arg_ty -> Nucleus.(alpha_equal_type arg_ty t)
  | None -> false
  end
  with
     Normalization_fail _ -> false

let is_alpha_equal_term_arg arg e =
  try
  begin
  match Nucleus.(as_is_term (deopt (as_not_abstract arg) "")) with
  | Some arg_e -> Nucleus.(alpha_equal_term arg_e e)
  | None -> false
  end
  with
     Normalization_fail _ -> false

let rec is_alpha_equal_type_args sgn args args' args_eq_args' ty0 =
  match args, args', args_eq_args' with
    | [], [], [] -> None
    | arg :: args, arg' :: args', arg_eq_arg' :: args_eq_args' ->
      if is_alpha_equal_type_arg arg ty0 then
        let arg_eq_arg' = deopt Nucleus.(as_eq_type (deopt (as_not_abstract arg_eq_arg') "")) ""
        and arg' = deopt Nucleus.(as_is_type (deopt (as_not_abstract arg') "")) "" in
        Some (arg_eq_arg', arg')
      else
      is_alpha_equal_type_args sgn args args' args_eq_args' ty0
    | [], _ :: _, _ :: _
    | _ :: _, [], _ :: _
    | _ :: _, _ :: _, []
    | [], [], _ :: _
    | [], _ :: _, []
    | _ :: _, [], [] -> None

let rec is_alpha_equal_term_args sgn args args' args_eq_args' e0 =
  match args, args', args_eq_args' with
    | [], [], [] -> None
    | arg :: args, arg' :: args', arg_eq_arg' :: args_eq_args' ->
      if is_alpha_equal_term_arg arg e0 then
        let arg_eq_arg' = deopt Nucleus.(as_eq_term (deopt (as_not_abstract arg_eq_arg') "")) ""
        and arg' = deopt Nucleus.(as_is_term (deopt (as_not_abstract arg') "")) "" in
        Some (arg_eq_arg', arg')
      else
      is_alpha_equal_term_args sgn args args' args_eq_args' e0
    | [], _ :: _, _ :: _
    | _ :: _, [], _ :: _
    | _ :: _, _ :: _, []
    | [], [], _ :: _
    | [], _ :: _, []
    | _ :: _, [], [] -> None


(** Find a type computation rule and apply it to [t]. *)
let rec apply_type_beta betas sgn t =
  let s = head_symbol_type (Nucleus.expose_is_type t) in
  match SymbolMap.find_opt s betas with

  | None -> None

  | Some lst ->
     let rec fold = function
       | [] -> None

       | (patt, rl) :: lst ->
          begin match Eqchk_pattern.match_is_type sgn t patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_type_rap sgn rl in
             begin match rap_fully_apply rap args with
             | Some t_eq_t' -> Some t_eq_t'
             | None -> fold lst
             end
          end
     in
     fold lst


(** Find a term computation rule and apply it to [e]. *)
and apply_term_beta betas sgn e =
  let s = head_symbol_term (Nucleus.expose_is_term e) in
  match SymbolMap.find_opt s betas with

  | None -> None

  | Some lst ->
     let rec fold = function
       | [] -> None

       | (patt, rl) :: lst ->
          begin match Eqchk_pattern.match_is_term sgn e patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_term_rap sgn rl in
             begin match rap_fully_apply rap args with
             | Some e_eq_e' -> Some e_eq_e'
             | None -> fold lst
             end
          end
     in
     fold lst

(** Normalize a type *)
and normalize_type ~strong sgn nrm args args' args_eq_args' ty0 =
  let rec fold ty0_eq_ty1 ty1 =
    let ty1_eq_ty2, Normal ty2 = normalize_heads_type ~strong sgn nrm args args' args_eq_args' ty1 in
    let ty0_eq_ty2 = Nucleus.transitivity_type ty0_eq_ty1 ty1_eq_ty2 in

    match apply_type_beta nrm.type_computations sgn ty2 with

    | None -> ty0_eq_ty2, Normal ty2

    | Some ty2_eq_ty3 ->
       let (Nucleus.Stump_EqType (_, _, ty3)) = Nucleus.invert_eq_type ty2_eq_ty3 in
       let ty0_eq_ty3 = Nucleus.transitivity_type ty0_eq_ty2 ty2_eq_ty3 in
       fold ty0_eq_ty3 ty3
  in
  fold (Nucleus.reflexivity_type ty0) ty0


and normalize_term ~strong sgn nrm args args' args_eq_args' e0 =
  let rec fold e0_eq_e1 e1 =
    let e1_eq_e2, Normal e2 = normalize_heads_term ~strong sgn nrm args args' args_eq_args' e1 in
    let e0_eq_e2 = Nucleus.transitivity_term e0_eq_e1 e1_eq_e2 in

    match apply_term_beta nrm.term_computations sgn e2 with

    | None -> e0_eq_e2, Normal e2

    | Some e2_eq_e3 ->
       let (Nucleus.Stump_EqTerm (_, _, e3, _)) = Nucleus.invert_eq_term sgn e2_eq_e3 in
       (* XXX normalize heads somewhere *)
       (* XXX this will fail because e_eq_e' and e'_eq_e'' may happen at different types *)
       (* XXX figure out how to convert e'_eq_e'' using Nucleus.convert_eq_term *)
       let e0_eq_e3 = Nucleus.transitivity_term e0_eq_e2 e2_eq_e3 in
       fold e0_eq_e3 e3
  in
  fold (Nucleus.reflexivity_term sgn e0) e0


(* Normalize those arguments of [ty0] which are considered to be heads and convert them along previously normalized arguments [args]. *)
and normalize_heads_type ~strong sgn nrm args args' args_eq_args' ty0 =
  match is_alpha_equal_type_args sgn args args' args_eq_args' ty0 with
  | Some (ty0_eq_ty1, ty1) -> ty0_eq_ty1, Normal ty1
  | None ->
    begin
      match Nucleus.invert_is_type sgn ty0 with

      | Nucleus.Stump_TypeConstructor (s, cargs) ->
         let heads = get_type_heads nrm (Ident s) in
         let rap = (Nucleus.form_constructor_rap sgn s) in
         let cargs_eq_cargs', Normal cargs', jdg1 = normalize_arguments ~strong sgn nrm heads rap args args' args_eq_args' cargs in
         let ty1 = deopt (Nucleus.as_is_type jdg1) "application of the constructor did not result in type judgement" in
         let ty0_eq_ty1 =
           let rap = deopt (Nucleus.congruence_is_type sgn ty0 ty1) "unable to construct a type congruence rule" in
           deopt (rap_fully_apply rap cargs_eq_cargs') "unable to apply the type congruence rule to arguments"
         in
         ty0_eq_ty1, Normal ty1

      | Nucleus.Stump_TypeMeta (mv, es) ->
         let heads = get_type_heads nrm (Nonce (Nucleus.meta_nonce mv)) in
         let es = List.map (fun e -> Nucleus.(abstract_not_abstract (JudgementIsTerm e))) es in
         let rap = (Nucleus.form_meta_rap sgn mv) in
         let es_eq_es', Normal es', jdg1 = normalize_arguments ~strong sgn nrm heads rap args args' args_eq_args' es in
         let ty1 =
           deopt (Nucleus.as_is_type jdg1) "application of the type matavariable did not result in type judgement"
         in
         let ty0_eq_ty1 =
           let rap = deopt (Nucleus.congruence_is_type sgn ty0 ty1)  "unable to construct a type congruence rule" in
           deopt (rap_fully_apply rap es_eq_es') "unable to apply the type congruence rule to arguments"
         in
        ty0_eq_ty1, Normal ty1
        end


(* Normalize those arguments of [e0] which are considered to be heads and convert them along previously normalized arguments [args]. *)
and normalize_heads_term ~strong sgn nrm args args' args_eq_args' e0 =
 match is_alpha_equal_term_args sgn args args' args_eq_args' e0 with
  | Some (e0_eq_e1, e1) -> e0_eq_e1, Normal e1
  | None ->
  begin
  match Nucleus.invert_is_term sgn e0 with

  | Nucleus.Stump_TermConstructor (s, cargs) ->
     let heads = get_term_heads nrm (Ident s) in
     let rap = (Nucleus.form_constructor_rap sgn s) in
     let cargs_eq_cargs', Normal cargs', jdg1 = normalize_arguments ~strong sgn nrm heads rap args args' args_eq_args' cargs in
     let e1 =
       deopt (Nucleus.as_is_term jdg1) "application of the term constructor did not result in term judgement" in
     let e0_eq_e1 =
       let rap = deopt (Nucleus.congruence_is_term sgn e0 e1) "unable to construct a term congruence rule" in
       deopt (rap_fully_apply rap cargs_eq_cargs') "unable to apply the term congruence rule to arguments"
     in
    e0_eq_e1, Normal e1

  | Nucleus.Stump_TermMeta (mv, es) ->
     let heads = get_term_heads nrm (Nonce (Nucleus.meta_nonce mv)) in
     let rap = (Nucleus.form_meta_rap sgn mv) in
     let es = List.map (fun e -> Nucleus.(abstract_not_abstract (JudgementIsTerm e))) es in
     let es_eq_es', Normal es', jdg1 = normalize_arguments ~strong sgn nrm heads rap args args' args_eq_args' es in
     let e1 =
       deopt (Nucleus.as_is_term jdg1) "application of the type matavariable did not result in term judgement"
     in
     let e0_eq_e1 =
       let rap = deopt (Nucleus.congruence_is_term sgn e0 e1) "unable to construct a term congruence rule" in
       deopt (rap_fully_apply rap es_eq_es') "unable to apply the term congruence rule to arguments"
     in
      e0_eq_e1, Normal e1

  | Nucleus.Stump_TermAtom _ ->
     Nucleus.(reflexivity_term sgn e0), Normal e0

  | Nucleus.Stump_TermConvert (e1', t) (* == e1 : t *) ->
     let e1'_eq_e2, _ = normalize_heads_term ~strong sgn nrm args args' args_eq_args' e1' in (* e1' == e2 : t' *)
     (* e0 == e1 : t and e1' == e2 : t' ===> e0 == e2 : t *)
     let e0_eq_e2 = Nucleus.transitivity_term Nucleus.(reflexivity_term sgn e0) e1'_eq_e2 in
     let Nucleus.Stump_EqTerm (_, _, e2, _) = Nucleus.invert_eq_term sgn e0_eq_e2 in
     (* e1' == e2 : t *)
     e0_eq_e2, Normal e2
    end

(** Normalize arguments [args] and convert them along previously normalized arguments [conv_args]. Then apply rule application [rap]. *)
and normalize_arguments ~strong sgn nrm heads rap conv_args conv_args' conv_args_eq_conv_args' args =
  let rec fold k args args' args_eq_args' rap args_rest =
    match rap, args_rest with

    | Nucleus.RapDone jdg, [] ->
      args_eq_args', Normal args', jdg

    | Nucleus.RapMore _, [] -> raise (Normalization_fail "applying rule to too few arguments")

    | Nucleus.RapDone _, _ :: _ -> raise (Normalization_fail "applying rule to too many arguments")

    | Nucleus.RapMore (bdry_rule, f), arg :: args_rest ->
      if strong || IntSet.mem k heads
      then
       let arg_eq_arg', Normal arg' = normalize_argument ~strong sgn nrm conv_args conv_args' conv_args_eq_conv_args' args args' args_eq_args' arg bdry_rule in
       fold (k+1) (args @ [arg]) (args' @ [arg']) (args_eq_args' @ [arg_eq_arg']) (rap_apply rap [arg']) args_rest
      else
        let arg_eq_arg', arg' = convert_argument sgn conv_args conv_args' conv_args_eq_conv_args' args args' args_eq_args' arg bdry_rule in
        fold (k+1) (args @ [arg]) (args' @ [arg']) (args_eq_args' @ [arg_eq_arg']) (rap_apply rap [arg']) args_rest
  in
  fold 0 [] [] [] rap args

and convert_argument sgn conv_args conv_args' conv_args_eq_conv_args' args args' args_eq_args' arg expected_boundary =
  match (Nucleus.invert_judgement_abstraction arg), (Nucleus.(invert_boundary_abstraction expected_boundary)) with

  | Nucleus.Stump_Abstract (atm, arg),  Nucleus.Stump_Abstract (atm_bdry, bdry) ->
     let atm_ty, atm_name = Nucleus.(type_of_atom atm, atom_name atm) in
     let ty_eq_ty', atm_ty' =
         convert_is_type sgn (conv_args @ args) (conv_args' @ args') (conv_args_eq_conv_args' @ args_eq_args') atm_ty in
     if not Nucleus.(alpha_equal_type atm_ty' (type_of_atom atm_bdry)) then raise (Normalization_fail "bound variable normalizes to a wrong type")
     else
     let atm' = Nucleus.(fresh_atom atm_name atm_ty') in
     let atm_conv = deopt Nucleus.(convert_term sgn (form_is_term_atom atm') (symmetry_type ty_eq_ty')) "cannot convert atom" in
     let atm_conv_bdry = deopt Nucleus.(convert_term sgn (form_is_term_atom atm) ty_eq_ty') "cannot convert atom" in
     let bdry = Nucleus.(abstract_boundary atm_bdry bdry) in
     let bdry = Nucleus.(apply_boundary_abstraction sgn bdry atm_conv_bdry) in
     let arg_eq_arg', arg'= convert_argument sgn conv_args conv_args' conv_args_eq_conv_args' args args' args_eq_args' arg bdry in
     let arg' = Nucleus.abstract_judgement atm arg'
     and arg_eq_arg' = Nucleus.abstract_judgement atm arg_eq_arg' in
     let arg' = Nucleus.(apply_judgement_abstraction sgn arg' atm_conv) in
     let arg' = Nucleus.abstract_judgement atm' arg' in
     arg_eq_arg', arg'

  | Nucleus.(Stump_NotAbstract (JudgementIsType t)), Nucleus.(Stump_NotAbstract (BoundaryIsType ())) ->
     let t_eq_t', t' = convert_is_type sgn (conv_args @ args) (conv_args' @ args') (conv_args_eq_conv_args' @ args_eq_args') t in
     Nucleus.(abstract_not_abstract (JudgementEqType t_eq_t')),
     Nucleus.(abstract_not_abstract (JudgementIsType t'))

  | Nucleus.(Stump_NotAbstract (JudgementIsTerm e)), Nucleus.(Stump_NotAbstract (BoundaryIsTerm bdry)) ->
    let e_eq_e', e' = convert_is_term sgn (conv_args @ args)   (conv_args' @ args') (conv_args_eq_conv_args' @   args_eq_args') e in
    let ty0 =  Nucleus.(type_of_term sgn e') in
      if Nucleus.(alpha_equal_type bdry ty0) then
      Nucleus.(abstract_not_abstract (JudgementEqTerm  e_eq_e')),
      Nucleus.(abstract_not_abstract (JudgementIsTerm e'))
      else
      begin
      match Nucleus.(invert_eq_term sgn e_eq_e') with
        | Nucleus.(Stump_EqTerm (_, _, e1, ty1)) ->
          if Nucleus.(alpha_equal_type bdry ty1)
          then
          Nucleus.(abstract_not_abstract (JudgementEqTerm  e_eq_e')),
          Nucleus.(abstract_not_abstract (JudgementIsTerm e1))
        else

      let ty0_eq_ty1, ty1 =
        let ty0_eq_ty1, ty1 = convert_is_type sgn (conv_args @ args) (conv_args' @ args') (conv_args_eq_conv_args' @ args_eq_args') ty0 in
        if not Nucleus.(alpha_equal_type bdry ty1) then
        raise (Normalization_fail "the term cannot be converted to correct boundary")
        else
        (ty0_eq_ty1, ty1)
      in
      let e' = deopt Nucleus.(convert_term sgn e' ty0_eq_ty1) "cannot convert normalized term to converted type" in
      Nucleus.(abstract_not_abstract (JudgementEqTerm  e_eq_e')),
      Nucleus.(abstract_not_abstract (JudgementIsTerm e'))
      end


  | Nucleus.(Stump_NotAbstract (JudgementEqType _ | JudgementEqTerm _)), _ ->
      raise (Normalization_fail "cannot normalize equality judgements")

  | Nucleus.(Stump_NotAbstract ((JudgementIsType _ | JudgementIsTerm _))), Nucleus.Stump_Abstract _
  | Nucleus.(Stump_Abstract _), Nucleus.(Stump_NotAbstract _) ->
      raise (Normalization_fail "expected abstraction, got unabstracted judgement")

  | Nucleus.(Stump_NotAbstract (JudgementIsType _),
    Stump_NotAbstract (BoundaryIsTerm _|BoundaryEqType _|BoundaryEqTerm _))
  | Nucleus.(Stump_NotAbstract (JudgementIsTerm _),
    Stump_NotAbstract (BoundaryIsType _|BoundaryEqType _|BoundaryEqTerm _)) ->
    raise (Normalization_fail "judgement and boundary mismatch")

and convert_is_type sgn args args' args_eq_args' t =
  match is_alpha_equal_type_args sgn args args' args_eq_args' t with
  | Some (ty0_eq_ty1, ty1) -> ty0_eq_ty1, ty1
  | None ->
    match Nucleus.invert_is_type sgn t with
      | Nucleus.(Stump_TypeConstructor (s, constr_args)) ->
        let rap = Nucleus.form_constructor_rap sgn s in
        let constr_args_eq_constr_args', constr_args', jdg1 =
            convert_arguments sgn rap args args' args_eq_args' constr_args in
        let t' =
          deopt (Nucleus.as_is_type jdg1) "application of the constructor did not result in type judgement" in
        let t_eq_t' =
          let rap = deopt (Nucleus.congruence_is_type sgn t t') "unable to construct a type congruence rule" in
          deopt (rap_fully_apply rap constr_args_eq_constr_args') "unable to apply the type congruence rule to arguments"
        in
        t_eq_t', t'


      | Nucleus.(Stump_TypeMeta (mv, es)) ->
        let es = List.map (fun e -> Nucleus.(abstract_not_abstract (JudgementIsTerm e))) es in
        let rap = (Nucleus.form_meta_rap sgn mv) in
        let es_eq_es', es', jdg1 = convert_arguments sgn rap args args' args_eq_args' es in
        let t' =
          deopt (Nucleus.as_is_type jdg1) "application of the type matavariable did not result in type judgement"
        in
        let t_eq_t' =
          let rap = deopt (Nucleus.congruence_is_type sgn t t')  "unable to construct a type congruence rule" in
          deopt (rap_fully_apply rap es_eq_es') "unable to apply the type congruence rule to arguments"
        in
       t_eq_t', t'


and convert_is_term sgn args args' args_eq_args' e =
  match is_alpha_equal_term_args sgn args args' args_eq_args' e with
  | Some (e_eq_e', e') -> e_eq_e', e'
  | None ->
        match Nucleus.invert_is_term sgn e with
          | Nucleus.(Stump_TermConstructor (s, constr_args)) ->
            let rap = Nucleus.form_constructor_rap sgn s in
            let constr_args_eq_constr_args', constr_args', jdg1 =
                convert_arguments sgn rap args args' args_eq_args' constr_args in
            let e' =
              deopt (Nucleus.as_is_term jdg1) "application of the constructor did not result in term judgement" in
            let e_eq_e' =
              let rap = deopt (Nucleus.congruence_is_term sgn e e') "unable to construct a term congruence rule" in
              deopt (rap_fully_apply rap constr_args_eq_constr_args') "unable to apply the term congruence rule to arguments"
            in
            e_eq_e', e'


          | Nucleus.(Stump_TermMeta (mv, es)) ->
            let es = List.map (fun expr -> Nucleus.(abstract_not_abstract (JudgementIsTerm expr))) es in
            let rap = Nucleus.form_meta_rap sgn mv in
            let es_eq_es', es', jdg1 = convert_arguments sgn rap args args' args_eq_args' es in
            let e' =
              deopt (Nucleus.as_is_term jdg1) "application of the term matavariable did not result in term judgement"
            in
            let e_eq_e' =
              let rap = deopt (Nucleus.congruence_is_term sgn e e')  "unable to construct a term congruence rule" in
              deopt (rap_fully_apply rap es_eq_es') "unable to apply the term congruence rule to arguments"
            in
            e_eq_e', e'

          | Nucleus.(Stump_TermAtom atm) ->
            Nucleus.(reflexivity_term sgn e), e

          | Nucleus.(Stump_TermConvert (e, eq)) ->
            let eq', e' = convert_is_term sgn args args' args_eq_args' e in
            let e' = deopt Nucleus.(convert_term sgn e' eq) "cannot convert the term" in
            (* XXX: this may fail, since eq may not be between the correct types*)
            eq', e'


and convert_arguments sgn rap args args' args_eq_args' constr_args =
  let rec fold constr_args constr_args' constr_args_eq_constr_args' rap constr_args_rest=
    match rap, constr_args_rest with
    | Nucleus.RapDone jdg, [] -> constr_args_eq_constr_args', constr_args', jdg

    | Nucleus.RapMore _, [] -> raise (Normalization_fail "applying rule to too few arguments")

    | Nucleus.RapDone _, _ :: _ -> raise (Normalization_fail "applying rule to too many arguments")

    | Nucleus.RapMore (bdry_rule, f), constr_arg :: constr_args_rest ->
      let constr_arg_eq_constr_arg', constr_arg' =
        convert_argument sgn args args' args_eq_args' constr_args constr_args' constr_args_eq_constr_args' constr_arg bdry_rule in
        fold (constr_args @ [constr_arg]) (constr_args' @ [constr_arg']) (constr_args_eq_constr_args' @ [constr_arg_eq_constr_arg']) (rap_apply rap [constr_arg']) constr_args_rest
  in
  fold [] [] [] rap constr_args


and normalize_argument ~strong sgn nrm conv_args conv_args' conv_args_eq_conv_args' args args' args_eq_args' arg expected_boundary =
  match (Nucleus.invert_judgement_abstraction arg), (Nucleus.(invert_boundary_abstraction expected_boundary)) with

  | Nucleus.Stump_Abstract (atm, arg), Nucleus.Stump_Abstract (atm_bdry, bdry) ->
     let atm_ty, atm_name = Nucleus.(type_of_atom atm, atom_name atm) in
     let ty_eq_ty', Normal atm_ty' =
         normalize_type ~strong sgn nrm (conv_args @ args) (conv_args' @ args') (conv_args_eq_conv_args' @ args_eq_args') atm_ty in
     if not Nucleus.(alpha_equal_type atm_ty' (type_of_atom atm_bdry)) then raise (Normalization_fail "bound variable normalizes to a wrong type")
     else
     let atm' = Nucleus.(fresh_atom atm_name atm_ty') in
     let atm_conv = deopt Nucleus.(convert_term sgn (form_is_term_atom atm') (symmetry_type ty_eq_ty')) "cannot convert atom" in
     let atm_conv_bdry = deopt Nucleus.(convert_term sgn (form_is_term_atom atm) ty_eq_ty') "cannot convert atom" in
     let bdry = Nucleus.(abstract_boundary atm_bdry bdry) in
     let bdry = Nucleus.(apply_boundary_abstraction sgn bdry atm_conv_bdry) in
     let arg_eq_arg', Normal arg'= normalize_argument ~strong sgn nrm conv_args conv_args' conv_args_eq_conv_args' args args' args_eq_args' arg bdry in
     let arg' = Nucleus.abstract_judgement atm arg'
     and arg_eq_arg' = Nucleus.abstract_judgement atm arg_eq_arg' in
     let arg' = Nucleus.(apply_judgement_abstraction sgn arg' atm_conv) in
     let arg' = Nucleus.abstract_judgement atm' arg' in
     arg_eq_arg', Normal arg'

  | Nucleus.(Stump_NotAbstract (JudgementIsType t)), Nucleus.(Stump_NotAbstract (BoundaryIsType ())) ->
      let t_eq_t', Normal t' = normalize_type ~strong sgn nrm (conv_args @ args) (conv_args' @ args') (conv_args_eq_conv_args' @ args_eq_args') t in
      Nucleus.(abstract_not_abstract (JudgementEqType t_eq_t')),
      Normal (Nucleus.(abstract_not_abstract (JudgementIsType t')))

  | Nucleus.(Stump_NotAbstract (JudgementIsTerm e)), Nucleus.(Stump_NotAbstract (BoundaryIsTerm bdry)) ->
      let e_eq_e', Normal e' = normalize_term ~strong sgn nrm (conv_args @ args) (conv_args' @ args') (conv_args_eq_conv_args' @ args_eq_args') e in
      let ty0 =  Nucleus.(type_of_term sgn e') in
      if Nucleus.(alpha_equal_type bdry ty0) then
      Nucleus.(abstract_not_abstract (JudgementEqTerm  e_eq_e')),
      Normal (Nucleus.(abstract_not_abstract (JudgementIsTerm e')))
      else
      begin
      match Nucleus.(invert_eq_term sgn e_eq_e') with
        | Nucleus.(Stump_EqTerm (_, _, e1, ty1)) ->
          if Nucleus.(alpha_equal_type bdry ty1)
          then
          Nucleus.(abstract_not_abstract (JudgementEqTerm  e_eq_e')),
        Normal (Nucleus.(abstract_not_abstract (JudgementIsTerm e1)))
        else

      let ty0_eq_ty1, ty1 =
        let ty0_eq_ty1, Normal ty1 = normalize_type ~strong sgn nrm (conv_args @ args) (conv_args' @ args') (conv_args_eq_conv_args' @ args_eq_args') ty0 in
        if not Nucleus.(alpha_equal_type bdry ty1) then
        raise (Normalization_fail "the term cannot be converted to correct boundary")
        else
        (ty0_eq_ty1, ty1)
      in
      let e' = deopt Nucleus.(convert_term sgn e' ty0_eq_ty1) "cannot convert normalized term to converted type" in
      Nucleus.(abstract_not_abstract (JudgementEqTerm  e_eq_e')),
      Normal (Nucleus.(abstract_not_abstract (JudgementIsTerm e')))
      end

  | Nucleus.(Stump_NotAbstract (JudgementEqType _ | JudgementEqTerm _)), _ ->
      raise (Normalization_fail "cannot normalize equality judgements")

  | Nucleus.(Stump_NotAbstract ((JudgementIsType _ | JudgementIsTerm _))), Nucleus.Stump_Abstract _
  | Nucleus.(Stump_Abstract _), Nucleus.(Stump_NotAbstract _) ->
      raise (Normalization_fail "expected abstraction, got unabstracted judgement")

  | Nucleus.(Stump_NotAbstract (JudgementIsType _),
    Stump_NotAbstract (BoundaryIsTerm _|BoundaryEqType _|BoundaryEqTerm _))
  | Nucleus.(Stump_NotAbstract (JudgementIsTerm _),
    Stump_NotAbstract (BoundaryIsType _|BoundaryEqType _|BoundaryEqTerm _)) ->
    raise (Normalization_fail "judgement and boundary mismatch")
