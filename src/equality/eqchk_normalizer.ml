(** Normalization *)

open Eqchk_common

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
and normalize_type ~strong sgn nrm ty0 =
  let rec fold ty0_eq_ty1 ty1 =
    let ty1_eq_ty2, Normal ty2 = normalize_heads_type ~strong sgn nrm ty1 in
    let ty0_eq_ty2 = Nucleus.transitivity_type ty0_eq_ty1 ty1_eq_ty2 in

    match apply_type_beta nrm.type_computations sgn ty2 with

    | None -> ty0_eq_ty2, Normal ty2

    | Some ty2_eq_ty3 ->
       let (Nucleus.Stump_EqType (_, _, ty3)) = Nucleus.invert_eq_type ty2_eq_ty3 in
       let ty0_eq_ty3 = Nucleus.transitivity_type ty0_eq_ty2 ty2_eq_ty3 in
       fold ty0_eq_ty3 ty3
  in
  fold (Nucleus.reflexivity_type ty0) ty0


and normalize_term ~strong sgn nrm e0 =
  let rec fold e0_eq_e1 e1 =
    let e1_eq_e2, Normal e2 = normalize_heads_term ~strong sgn nrm e1 in
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


(* Normalize those arguments of [ty0] which are considered to be normalizing. *)
and normalize_heads_type ~strong sgn nrm ty0 =
  match Nucleus.invert_is_type sgn ty0 with

    | Nucleus.Stump_TypeConstructor (s, cargs) ->
      let heads = get_type_heads nrm (Ident s) in
      let cargs_eq_cargs', Normal cargs' = normalize_arguments ~strong sgn nrm heads cargs in
      let ty0_eq_ty1, ty1 = Nucleus.rewrite_is_type sgn ty0 cargs_eq_cargs' in
      ty0_eq_ty1, Normal ty1

    | Nucleus.Stump_TypeMeta (mv, es) ->
      let heads = get_type_heads nrm (Nonce (Nucleus.meta_nonce mv)) in
      let es = List.map (fun e -> Nucleus.(abstract_not_abstract (JudgementIsTerm e))) es in
      let es_eq_es', Normal es' = normalize_arguments ~strong sgn nrm heads es in
      let ty0_eq_ty1, ty1 = Nucleus.rewrite_is_type sgn ty0 es_eq_es' in
      ty0_eq_ty1, Normal ty1


(* Normalize those arguments of [e0] which are considered to be normalizing. *)
and normalize_heads_term ~strong sgn nrm e0 =
  match Nucleus.invert_is_term sgn e0 with

  | Nucleus.Stump_TermConstructor (s, cargs) ->
     let heads = get_term_heads nrm (Ident s) in
     let cargs_eq_cargs', Normal cargs' = normalize_arguments ~strong sgn nrm heads cargs in
     let e0_eq_e1, e1 = Nucleus.rewrite_is_term sgn e0 cargs_eq_cargs' in
    e0_eq_e1, Normal e1

  | Nucleus.Stump_TermMeta (mv, es) ->
     let heads = get_term_heads nrm (Nonce (Nucleus.meta_nonce mv)) in
     let es = List.map (fun e -> Nucleus.(abstract_not_abstract (JudgementIsTerm e))) es in
     let es_eq_es', Normal es' = normalize_arguments ~strong sgn nrm heads es in
     let e0_eq_e1, e1 = Nucleus.rewrite_is_term sgn e0 es_eq_es' in
    e0_eq_e1, Normal e1

  | Nucleus.Stump_TermAtom _ ->
     Nucleus.(reflexivity_term sgn e0), Normal e0

  | Nucleus.Stump_TermConvert (e0', t) (* == e0 : t *) ->
     let e0'_eq_e1, Normal e1 = normalize_heads_term ~strong sgn nrm e0' in (* e0' == e1 : t' *)
     (* Format.printf "normalizing term %t with normalized heads %t@." (Nucleus.print_is_term ~penv e0) (Nucleus.print_eq_term ~penv e0'_eq_e1); *)
     (* e0 == e0 : t and e0' == e1 : t' ===> e0 == e1 : t *)
     let e0_eq_e1 = Nucleus.transitivity_term (Nucleus.reflexivity_term sgn e0) e0'_eq_e1 in
     (* let e1 = Nucleus.form_is_term_convert sgn e1 t in *)
     let Nucleus.Stump_EqTerm (_, _, e1, _) = Nucleus.invert_eq_term sgn e0_eq_e1 in
     (* e0' == e1 : t *)
     e0_eq_e1, Normal e1

(** Normalize arguments [args] and convert them along previously normalized arguments [conv_args]. Then apply rule application [rap]. *)
and normalize_arguments ~strong sgn nrm heads args =
  let rec fold k args' args_eq_args' args_rest =
    match args_rest with

    | [] ->
      List.rev args_eq_args', Normal (List.rev args')

    | arg :: args_rest ->
      if strong || IntSet.mem k heads
      then
       let arg_eq_arg', Normal arg' = normalize_argument ~strong sgn nrm arg in
       fold (k+1) (arg' :: args') (arg_eq_arg' :: args_eq_args') args_rest
      else
        let arg_eq_arg' = deopt (Nucleus.reflexivity_judgement_abstraction sgn arg) "unexpected equality judgement" in
        fold (k+1) (arg :: args') (arg_eq_arg' :: args_eq_args') args_rest
  in
  fold 0 [] [] args


and normalize_argument ~strong sgn nrm arg =
  match (Nucleus.invert_judgement_abstraction arg) with

  | Nucleus.Stump_Abstract (atm, arg) ->
     let arg_eq_arg', Normal arg'= normalize_argument ~strong sgn nrm arg in
     let arg' = Nucleus.abstract_judgement atm arg'
     and arg_eq_arg' = Nucleus.abstract_judgement atm arg_eq_arg' in
     arg_eq_arg', Normal arg'

  | Nucleus.(Stump_NotAbstract (JudgementIsType t)) ->
      let t_eq_t', Normal t' = normalize_type ~strong sgn nrm t in
      Nucleus.(abstract_not_abstract (JudgementEqType t_eq_t')),
      Normal (Nucleus.(abstract_not_abstract (JudgementIsType t')))

  | Nucleus.(Stump_NotAbstract (JudgementIsTerm e)) ->
      let e_eq_e', Normal e' = normalize_term ~strong sgn nrm e in
      Nucleus.(abstract_not_abstract (JudgementEqTerm  e_eq_e')),
      Normal (Nucleus.(abstract_not_abstract (JudgementIsTerm e')))

  | Nucleus.(Stump_NotAbstract (JudgementEqType _ | JudgementEqTerm _)) ->
      raise (Normalization_fail "cannot normalize equality judgements")
