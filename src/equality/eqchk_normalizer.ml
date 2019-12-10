(** Normalization *)

open Eqchk_common

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


(** Functions [make_XYZ] convert a derivation to a rewrite rule, or raise
    the exception, or raise the exception [Invalid_rule] when the derivation
    has the wrong form. *)

let make_type_computation sgn drv =
  let rec fold k  = function

    | Nucleus_types.(Conclusion eq)  ->
       let (Nucleus_types.EqType (_asmp, t1, _t2)) = Nucleus.expose_eq_type eq in
       begin match Eqchk_pattern.make_is_type sgn k t1 with

       | Some patt ->
          let s = head_symbol_type t1 in
          (s, patt)

       | None -> invalid_rule ()
       end

    | Nucleus_types.(Premise ({meta_boundary=bdry;_}, drv)) ->
       if is_object_premise bdry then
         fold (k+1) drv
       else
         invalid_rule ()
  in
  let drv =
    match Nucleus.as_eq_type_rule drv with
    | Some drv -> drv
    | None -> invalid_rule ()
  in
  let (s, patt) = fold 0 (Nucleus.expose_rule drv) in
  s, (patt, drv)


let make_term_computation sgn drv =
  let rec fold k = function

    | Nucleus_types.(Conclusion eq) ->
       let (Nucleus_types.EqTerm (_asmp, e1, _e2, _t)) = Nucleus.expose_eq_term eq in
       begin match Eqchk_pattern.make_is_term sgn k e1 with

       | Some patt ->
          let s = head_symbol_term e1 in
          (s, patt)

       | None -> invalid_rule ()
       end

    | Nucleus_types.(Premise ({meta_boundary=bdry;_}, drv)) ->
       if is_object_premise bdry then
         fold (k+1) drv
       else
         invalid_rule ()
  in
  let drv =
    match Nucleus.as_eq_term_rule drv with
    | Some drv -> drv
    | None -> invalid_rule ()
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

let set_type_heads nrm sym heads =
  let heads = IntSet.of_list heads in
  { nrm with type_heads = SymbolMap.add sym heads nrm.type_heads }

let set_term_heads normalizer sym heads =
  let heads = IntSet.of_list heads in
  { normalizer with term_heads = SymbolMap.add sym heads normalizer.term_heads }

(** Functions that apply rewrite rules *)

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
and normalize_type nrm sgn ty0 =
  let rec fold ty0_eq_ty1 ty1 =
    let ty1_eq_ty2, ty2 = normalize_heads_type nrm sgn ty1 in
    let ty0_eq_ty2 = Nucleus.transitivity_type ty0_eq_ty1 ty1_eq_ty2 in

    match apply_type_beta nrm.type_computations sgn ty2 with

    | None -> ty0_eq_ty2, Normal ty2

    | Some ty2_eq_ty3 ->
       let (Nucleus.Stump_EqType (_, _, ty3)) = Nucleus.invert_eq_type ty2_eq_ty3 in
       let ty0_eq_ty3 = Nucleus.transitivity_type ty0_eq_ty2 ty2_eq_ty3 in
       fold ty0_eq_ty3 ty3
  in
  fold (Nucleus.reflexivity_type ty0) ty0


and normalize_term nrm sgn e0 =
  let rec fold e0_eq_e1 e1 =
    let e1_eq_e2, e2 = normalize_heads_term nrm sgn e1 in
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


(* Normalize those arguments of [ty0] which are considered to be heads. *)
and normalize_heads_type nrm sgn ty0 =

  let get_heads sym =
    match SymbolMap.find_opt sym nrm.type_heads with
    | None -> IntSet.empty (* could short-circuit here *)
    | Some heads -> heads
  in

  match Nucleus.invert_is_type sgn ty0 with

  | Nucleus.Stump_TypeConstructor (s, args) ->
     let heads = get_heads (Ident s) in
     let args', eqs = normalize_arguments sgn nrm heads args in
     let ty1 =
       let jdg1 = deopt (rap_fully_apply (Nucleus.form_constructor_rap sgn s) args') in
       deopt (Nucleus.as_is_type jdg1) in
     let ty0_eq_ty1 =
       let rap = deopt (Nucleus.congruence_is_type sgn ty0 ty1) in
       deopt (rap_fully_apply rap eqs)
     in
     ty0_eq_ty1, ty1

  | Nucleus.Stump_TypeMeta (mv, es) ->
     let heads = get_heads (Nonce (Nucleus.meta_nonce mv)) in
     let es', es_eq_es' = normalize_is_terms sgn nrm heads es in
     let ty1 =
       let jdg1 = deopt (rap_fully_apply (Nucleus.form_meta_rap sgn mv) es') in
       deopt (Nucleus.as_is_type jdg1)
     in
     let ty0_eq_ty1 =
       let rap = deopt (Nucleus.congruence_is_type sgn ty0 ty1) in
       deopt (rap_fully_apply rap es_eq_es')
     in
     ty0_eq_ty1, ty1


(* Normalize those arguments of [e0] which are considered to be heads. *)
and normalize_heads_term nrm sgn e0 =
  (* let sym = head_symbol_term (Nucleus.expose_is_term e0) in *)
  (* let heads = *)
  (*   match SymbolMap.find_opt sym nrm.term_heads with *)
  (*   | None -> IntSet.empty *)
  (*   | Some heads -> heads *)
  (* in *)
  failwith "normalize_heads_term"

and normalize_arguments _ = failwith "normalize_arguents"

and normalize_is_terms _ = failwith "normalize_is_terms"

(* (\** The exported form of normalization for types *\) *)
(* let normalize_type nrm sgn t = *)
(*   let eq, Normal t = normalize_type' nrm sgn t in *)
(*   eq, t *)

(* (\** The exported form of normalization for terms *\) *)
(* let normalize_term nrm sgn e = *)
(*   let eq, Normal e = normalize_term' nrm sgn e in *)
(*   (\* XXX convert eq to be at the type of e *\) *)
(*   eq, e *)