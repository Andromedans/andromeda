open Nucleus_types

(* Instantiate a premise with meta-variables to obtain a boundary. *)
let instantiate_premise ~lvl metas prem =
  match prem with

  | BoundaryIsType () ->
     BoundaryIsType ()

  | BoundaryIsTerm t ->
     BoundaryIsTerm (Instantiate_meta.is_type ~lvl metas t)

  | BoundaryEqType (t1, t2) ->
     BoundaryEqType (Instantiate_meta.is_type ~lvl metas t1, Instantiate_meta.is_type ~lvl metas t2)

  | BoundaryEqTerm (e1, e2, t) ->
     BoundaryEqTerm (Instantiate_meta.is_term ~lvl metas e1,
                     Instantiate_meta.is_term ~lvl metas e2,
                     Instantiate_meta.is_type ~lvl metas t)

(* Check that the argument [arg] matches the premise [prem], given [metas] *)
let check_judgement ~lvl sgn metas arg prem =
  match arg, instantiate_premise ~lvl metas prem with

  | JudgementIsType abstr, BoundaryIsType bdry ->
     Check.is_type_boundary abstr bdry

  | JudgementIsTerm e, BoundaryIsTerm t ->
     Check.is_term_boundary sgn e t

  | JudgementEqType eq, BoundaryEqType bdry ->
     Check.eq_type_boundary eq bdry

  | JudgementEqTerm eq, BoundaryEqTerm bdry  ->
     Check.eq_term_boundary eq bdry

  | (JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _) , (BoundaryIsType _ as bdry)
  | (JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) , (BoundaryIsTerm _ as bdry)
  | (JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _) , (BoundaryEqType _ as bdry)
  | (JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _) , (BoundaryEqTerm _ as bdry) ->
     Error.raise (ArgumentExpected bdry)

let arg_of_argument = function
  | JudgementIsType t -> Mk.arg_is_type t
  | JudgementIsTerm e -> Mk.arg_is_term e
  | JudgementEqType eq -> Mk.arg_eq_type eq
  | JudgementEqTerm eq-> Mk.arg_eq_term eq

let match_argument sgn metas (s : boundary) (p : judgement) : judgement =
  failwith "form_rule match_argument shouldn't be needed"
  (* check_argument sgn metas s p ;
   * arg_of_argument p *)

let match_arguments sgn (premises : boundary list) (arguments : judgement list) =
  let rec fold args_out = function
    | [], [] ->
       (* The arguments must _not_ be reversed because we refer to them by meta-variable
          de Bruijn indices, and therefore the last argument must have index 0. *)
       args_out
    | [], _::_ -> Error.raise TooManyArguments
    | _::_, [] -> Error.raise TooFewArguments
    | premise :: premises, argument :: arguments ->
       let metas = args_out in (* args also serves as the list of collected metas *)
       let argument = match_argument sgn metas premise argument in
       fold (Indices.cons argument args_out) (premises, arguments)
  in
  fold (Indices.of_list []) (premises, arguments)

(** Judgement formation *)

(** Lookup the de Bruijn index of a meta-variable. *)
let lookup_meta_index x mvs =
  let rec search k = function
    | [] -> None
    | y :: mvs ->
       if Nonce.equal x y then
         Some k
       else
         search (k+1) mvs
  in
  search 0 mvs

(** The [mk_rule_XYZ] functions are auxiliary functions that should not be
    exposed. The external interface exposes the [form_rule_XYZ] functions defined
    below. *)

let rec mk_rule_is_type metas = function
  | TypeConstructor (c, args) ->
     let args = mk_rule_arguments metas args in
     TypeConstructor (c, args)

  | TypeMeta (MetaFree mv, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     begin match lookup_meta_index mv.meta_nonce metas with
     | Some k -> TypeMeta (MetaBound k, args)
     | None -> TypeMeta (MetaFree mv, args)
     end

  | TypeMeta (MetaBound _, _) ->
     assert false

and mk_rule_is_term metas = function
  | TermAtom _ ->
     (* XXX turn this into a proper runtime error *)
     failwith "a free atom cannot appear in a rule"

  | TermMeta (MetaFree mv, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     begin match lookup_meta_index mv.meta_nonce metas with
     | Some k -> TermMeta (MetaBound k, args)
     | None -> TermMeta (MetaFree mv, args)
     end

  | TermMeta (MetaBound _, _) ->
     assert false

  | TermConstructor (c, args) ->
     let args = mk_rule_arguments metas args in
     TermConstructor (c, args)

  | TermBoundVar k ->
     TermBoundVar k

  | TermConvert (e, asmp, t) ->
     let e = mk_rule_is_term metas e
     and asmp = mk_rule_assumptions metas asmp
     and t = mk_rule_is_type metas t
     in
     (* does not create a doubly nested [TermConvert] because original input does not either *)
     TermConvert (e, asmp, t)

and mk_rule_eq_type metas (EqType (asmp, t1, t2)) =
  let asmp = mk_rule_assumptions metas asmp
  and t1 = mk_rule_is_type metas t1
  and t2 = mk_rule_is_type metas t2 in
  EqType (asmp, t1, t2)

and mk_rule_eq_term metas (EqTerm (asmp, e1, e2, t)) =
  let asmp = mk_rule_assumptions metas asmp
  and e1 = mk_rule_is_term metas e1
  and e2 = mk_rule_is_term metas e2
  and t = mk_rule_is_type metas t in
  EqTerm (asmp, e1, e2, t)

and mk_rule_assumptions metas {free_var; free_meta; bound_var; bound_meta} =
  (* It must be the case that [bound_meta] is empty. *)
  assert (Bound_set.is_empty bound_meta) ;
  let rec fold free_meta bound_meta k = function
    | [] -> { free_var; free_meta; bound_var; bound_meta }
    | n :: metas ->
       if Nonce.map_mem n free_meta then
         let free_meta = Nonce.map_remove n free_meta in
         let bound_meta = Bound_set.add k bound_meta in
         fold free_meta bound_meta (k+1) metas
       else
         fold free_meta bound_meta (k+1) metas
  in
  fold free_meta bound_meta 0 metas

and mk_rule_judgement metas = function

  | JudgementIsType t -> JudgementIsType (mk_rule_is_type metas t)

  | JudgementIsTerm e -> JudgementIsTerm (mk_rule_is_term metas e)

  | JudgementEqType eq -> JudgementEqType (mk_rule_eq_type metas eq)

  | JudgementEqTerm eq -> JudgementEqTerm (mk_rule_eq_term metas eq)

and mk_rule_argument metas = function

  | Arg_NotAbstract jdg ->
     let jdg = mk_rule_judgement metas jdg in
     Arg_NotAbstract jdg

  | Arg_Abstract (x, arg) ->
     let arg = mk_rule_argument metas arg in
     Arg_Abstract (x, arg)

and mk_rule_arguments metas args =
  List.map (mk_rule_argument metas) args

and mk_rule_abstraction
  : 'a 'b 'c . (Nonce.t list -> 'a -> 'b) -> Nonce.t list -> 'a abstraction -> 'b abstraction
  = fun form_u metas -> function

    | NotAbstract u ->
       let u = form_u metas u in
       NotAbstract u

    | Abstract (x, t, abstr) ->
       let t = mk_rule_is_type metas t in
       let abstr = mk_rule_abstraction form_u metas abstr in
       Abstract (x, t, abstr)

let mk_rule_premise metas = function

  | BoundaryIsType () ->
     BoundaryIsType ()

  | BoundaryIsTerm t ->
     BoundaryIsTerm (mk_rule_is_type metas t)

  | BoundaryEqType (t1, t2) ->
     BoundaryEqType (mk_rule_is_type metas t1, mk_rule_is_type metas t2)

  | BoundaryEqTerm (e1, e2, t) ->
     BoundaryEqTerm (mk_rule_is_term metas e1, mk_rule_is_term metas e2, mk_rule_is_type metas t)

let fold_prems prems form_concl =
  let rec fold metas = function
    | [] -> Conclusion (form_concl metas)

    | (mv, prem) :: prems ->
       let prem = mk_rule_abstraction mk_rule_premise metas prem in
       let rl = fold (mv :: metas) prems in
       Premise (mv, prem, rl)
  in
  fold [] prems

let form_rule prems concl =
  fold_prems prems
  begin fun metas ->
    match concl with
    | BoundaryIsType () ->
       BoundaryIsType ()

    | BoundaryIsTerm t ->
       BoundaryIsTerm (mk_rule_is_type metas t)

    | BoundaryEqType (t1, t2) ->
       let t1 = mk_rule_is_type metas t1
       and t2 = mk_rule_is_type metas t2 in
       BoundaryEqType (t1, t2)

    | BoundaryEqTerm (e1, e2, t) ->
       let e1 = mk_rule_is_term metas e1
       and e2 = mk_rule_is_term metas e2
       and t = mk_rule_is_type metas t in
       BoundaryEqTerm (e1, e2, t)
  end


let form_derivation prems concl =
  fold_prems prems
  begin fun metas ->
    match concl with
    | JudgementIsType t -> JudgementIsType (mk_rule_is_type metas t)

    | JudgementIsTerm e -> JudgementIsTerm (mk_rule_is_term metas e)

    | JudgementEqType eq -> JudgementEqType (mk_rule_eq_type metas eq)

    | JudgementEqTerm eq -> JudgementEqTerm (mk_rule_eq_term metas eq)
  end
