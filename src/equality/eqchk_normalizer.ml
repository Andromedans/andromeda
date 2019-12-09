(** Normalization *)

open Eqchk_common

(** The types of beta rules. *)

type type_normalizer =
  { type_computations : (Patt.is_type * Nucleus.eq_type Nucleus.rule) list SymbolMap.t ;
    type_heads : IntSet.t SymbolMap.t
  }

type term_normalizer =
  { term_computations : (Patt.is_term * Nucleus.eq_term Nucleus.rule) list SymbolMap.t ;
    term_heads : IntSet.t SymbolMap.t
  }

let empty_type_normalizer =
  { type_computations = SymbolMap.empty ;
    type_heads = SymbolMap.empty }

let empty_term_normalizer =
  { term_computations = SymbolMap.empty ;
    term_heads = SymbolMap.empty }

let find_type_computations sym {type_computations;_} =
  SymbolMap.find_opt sym type_computations

let find_term_computations sym {term_computations;_} =
  SymbolMap.find_opt sym term_computations


(** Functions [make_XYZ] convert a derivation to a rewrite rule, or raise
    the exception, or raise the exception [Invalid_rule] when the derivation
    has the wrong form. *)

let make_type_computation sgn drv =
  let rec fold k  = function

    | Nucleus_types.(Conclusion eq)  ->
       let (Nucleus_types.EqType (_asmp, t1, _t2)) = Nucleus.expose_eq_type eq in
       begin match Eqchk_pattern.make_is_type sgn k t1 with

       | Some patt ->
          let s = Eqchk_common.head_symbol_type t1 in
          (s, patt)

       | None -> Eqchk_common.invalid_rule ()
       end

    | Nucleus_types.Premise (n, bdry, drv) ->
       if Eqchk_common.is_object_premise bdry then
         fold (k+1) drv
       else
         Eqchk_common.invalid_rule ()
  in
  let drv =
    match Nucleus.as_eq_type_rule drv with
    | Some drv -> drv
    | None -> Eqchk_common.invalid_rule ()
  in
  let (s, patt) = fold 0 (Nucleus.expose_rule drv) in
  s, (patt, drv)


let make_term_computation sgn drv =
  let rec fold k = function

    | Nucleus_types.(Conclusion eq) ->
       let (Nucleus_types.EqTerm (_asmp, e1, _e2, _t)) = Nucleus.expose_eq_term eq in
       begin match Eqchk_pattern.make_is_term sgn k e1 with

       | Some patt ->
          let s = Eqchk_common.head_symbol_term e1 in
          (s, patt)

       | None -> Eqchk_common.invalid_rule ()
       end

    | Nucleus_types.Premise (n, bdry, drv) ->
       if Eqchk_common.is_object_premise bdry then
         fold (k+1) drv
       else
         Eqchk_common.invalid_rule ()
  in
  let drv =
    match Nucleus.as_eq_term_rule drv with
    | Some drv -> drv
    | None -> Eqchk_common.invalid_rule ()
  in
  let (s, patt) = fold 0 (Nucleus.expose_rule drv) in
  s, (patt, drv)


let add_type_computation sgn normalizer drv =
  let sym, bt = make_type_computation sgn drv in
  let rls =
    match find_type_computations sym normalizer with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  { normalizer with type_computations = SymbolMap.add sym rls normalizer.type_computations }


let add_term_computation sgn normalizer drv =
  let sym, bt = make_term_computation sgn drv in
  let rls =
    match find_term_computations sym normalizer with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  { normalizer with term_computations = SymbolMap.add sym rls normalizer.term_computations }

(** Functions that apply rewrite rules *)

(** Find a type computation rule and apply it to [t]. *)
let rec apply_type_beta betas sgn t =
  let s = Eqchk_common.head_symbol_type (Nucleus.expose_is_type t) in
  match Eqchk_common.SymbolMap.find_opt s betas with

  | None -> None

  | Some lst ->
     let rec fold = function
       | [] -> None

       | (patt, rl) :: lst ->
          begin match Eqchk_pattern.match_is_type sgn t patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_type_rap sgn rl in
             begin match Eqchk_common.rap_apply_args rap args with
             | Some (Nucleus.RapDone t_eq_t') -> Some t_eq_t'
             | None -> fold lst
             | Some (Nucleus.RapMore _) -> assert false
             end
          end
     in
     fold lst


(** Find a term computation rule and apply it to [e]. *)
and apply_term_beta betas sgn e =
  let s = Eqchk_common.head_symbol_term (Nucleus.expose_is_term e) in
  match Eqchk_common.SymbolMap.find_opt s betas with

  | None -> None

  | Some lst ->
     let rec fold = function
       | [] -> None

       | (patt, rl) :: lst ->
          (* XXX match_is_type should normalize parts of t as necessary *)
          begin match Eqchk_pattern.match_is_term sgn e patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_term_rap sgn rl in
             begin match Eqchk_common.rap_apply_args rap args with
             | Some (Nucleus.RapDone e_eq_e') -> Some e_eq_e'
             | None -> fold lst
             | Some (Nucleus.RapMore _) -> assert false
             end
          end
     in
     fold lst

(** Normalize a type *)
and normalize_type nrm sgn ty =
  let rec fold ty_eq_ty' ty' =

    match apply_type_beta nrm.type_computations sgn ty' with

    | None -> ty_eq_ty', Eqchk_common.Normal ty'

    | Some ty'_eq_ty'' ->
       let (Nucleus.Stump_EqType (_, _, ty'')) = Nucleus.invert_eq_type ty'_eq_ty'' in
       let ty_eq_ty'' = Nucleus.transitivity_type ty_eq_ty' ty'_eq_ty'' in
       (* XXX normalize heads somewhere *)
       fold ty_eq_ty'' ty''
  in
  fold (Nucleus.reflexivity_type ty) ty


and normalize_term nrm sgn e =
  let rec fold e_eq_e' e' =

    match apply_term_beta nrm.term_computations sgn e' with

    | None -> e_eq_e', Eqchk_common.Normal e'

    | Some e'_eq_e'' ->
       let (Nucleus.Stump_EqTerm (_, _, e'', _)) = Nucleus.invert_eq_term sgn e'_eq_e'' in
       (* XXX normalize heads somewhere *)
       (* XXX this will fail because e_eq_e' and e'_eq_e'' may happen at different types *)
       (* XXX figure out how to convert e'_eq_e'' using Nucleus.convert_eq_term *)
       let e_eq_e'' = Nucleus.transitivity_term e_eq_e' e'_eq_e'' in
       fold e_eq_e'' e''
  in
  fold (Nucleus.reflexivity_term sgn e) e

(* (\** The exported form of normalization for types *\) *)
(* let normalize_type nrm sgn t = *)
(*   let eq, Normal t = normalize_type' nrm sgn t in *)
(*   eq, t *)

(* (\** The exported form of normalization for terms *\) *)
(* let normalize_term nrm sgn e = *)
(*   let eq, Normal e = normalize_term' nrm sgn e in *)
(*   (\* XXX convert eq to be at the type of e *\) *)
(*   eq, e *)
