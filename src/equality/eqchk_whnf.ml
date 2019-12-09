(** Weak head-normal form normalization *)

open Eqchk_common

(** The types of beta rules. *)

type type_normalizer =
  { type_computations : (Patt.is_type * Nucleus.eq_type Nucleus.rule) SymbolMap.t ;
    type_heads : IntSet.t SymbolMap.t
  }

type term_normalizer =
  { term_computations : (Patt.is_type * Nucleus.eq_term Nucleus.rule) SymbolMap.t ;
    term_heads : IntSet.t SymbolMap.t
  }

let empty_type_normalizer =
  { type_computations = SymbolMap.empty ;
    type_heads = SymbolMap.empty }

let empty_term_normalizer =
  { term_computations = SymbolMap.empty ;
    term_heads = SymbolMap.empty }

(** Functions [make_XYZ] convert a derivation to a rewrite rule, or raise
    the exception, or raise the exception [Invalid_rule] when the derivation
    has the wrong form. *)

let make_type_computation sgn drv =
  let rec fold k  = function

    | Nucleus_types.(Conclusion eq)  ->
       let (Nucleus_types.EqType (_asmp, t1, _t2)) = Nucleus.expose_eq_type eq in
       begin match Rewrite.make_is_type sgn k t1 with

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
       begin match Rewrite.make_is_term sgn k e1 with

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
          begin match Rewrite.match_is_type sgn t patt with
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
          begin match Rewrite.match_is_term sgn e patt with
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


(** Weak head-normal form normalization *)
and whnf_type chk sgn ty =
  let rec fold ty_eq_ty' ty' =

    match apply_type_beta chk sgn ty' with

    | None -> ty_eq_ty', Eqchk_common.Whnf ty'

    | Some ty'_eq_ty'' ->
       let (Nucleus.Stump_EqType (_, _, ty'')) = Nucleus.invert_eq_type ty'_eq_ty'' in
       let ty_eq_ty'' = Nucleus.transitivity_type ty_eq_ty' ty'_eq_ty'' in
       fold ty_eq_ty'' ty''
  in
  fold (Nucleus.reflexivity_type ty) ty


and whnf_term chk sgn e =
  let rec fold e_eq_e' e' =

    match apply_term_beta chk sgn e' with

    | None -> e_eq_e', Eqchk_common.Whnf e'

    | Some e'_eq_e'' ->
       let (Nucleus.Stump_EqTerm (_, _, e'', _)) = Nucleus.invert_eq_term sgn e'_eq_e'' in
       (* XXX this will fail because e_eq_e' and e'_eq_e'' may happen at different types *)
       (* XXX figure out how to convert e'_eq_e'' using Nucleus.convert_eq_term *)
       let e_eq_e'' = Nucleus.transitivity_term e_eq_e' e'_eq_e'' in
       fold e_eq_e'' e''
  in
  fold (Nucleus.reflexivity_term sgn e) e
