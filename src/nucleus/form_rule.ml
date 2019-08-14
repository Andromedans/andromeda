open Nucleus_types

(* Instantiate a premise with meta-variables to obtain a boundary. *)
let instantiate_premise ~lvl metas prem =
  match prem with

  | Rule.BoundaryIsType () ->
     BoundaryIsType ()

  | Rule.BoundaryIsTerm t ->
     BoundaryIsTerm (Instantiate_meta.is_type ~lvl metas t)

  | Rule.BoundaryEqType (t1, t2) ->
     BoundaryEqType (Instantiate_meta.is_type ~lvl metas t1, Instantiate_meta.is_type ~lvl metas t2)

  | Rule.BoundaryEqTerm (e1, e2, t) ->
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

let match_argument sgn metas (s : Rule.boundary) (p : judgement) : judgement =
  failwith "form_rule match_argument shouldn't be needed"
  (* check_argument sgn metas s p ;
   * arg_of_argument p *)

let match_arguments sgn (premises : Rule.boundary list) (arguments : judgement list) =
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
    | [] -> assert false
    | y :: mvs ->
       if Nonce.equal x y then
         k
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
     Rule.TypeConstructor (c, args)

  | TypeMeta ({meta_nonce=x;_}, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     let k = lookup_meta_index x metas in
     Rule.TypeMeta (k, args)

and mk_rule_is_term metas = function
  | TermAtom _ ->
     (* this will be gone when we eliminate atoms *)
     failwith "a free atom cannot appear in a rule"

  | TermMeta ({meta_nonce=x;_}, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     let k = lookup_meta_index x metas in
     Rule.TermMeta (k, args)

  | TermConstructor (c, args) ->
     let args = mk_rule_arguments metas args in
     Rule.TermConstructor (c, args)

  | TermBoundVar k ->
     Rule.TermBoundVar k

  | TermConvert (e, asmp, t) ->
     let {free; meta; bound} = asmp
     (* NB: We do not check that the types of the metas match because we assume that
        the type of a meta never changes. *)
     and metas_set = Nonce.set_of_list metas in
     let mem_metas_set mv _bnd = Nonce.set_mem mv metas_set in
     begin match Nonce.map_is_empty free
                 && Nonce.map_for_all mem_metas_set meta
                 && Bound_set.is_empty bound
     with
     | true -> mk_rule_is_term metas e
     | false -> Error.raise ExtraAssumptions
     end

and mk_rule_eq_type metas (EqType (asmp, t1, t2)) =
  let _ = mk_rule_assumptions metas asmp
  and t1 = mk_rule_is_type metas t1
  and t2 = mk_rule_is_type metas t2 in
  Rule.EqType (t1, t2)

and mk_rule_eq_term metas (EqTerm (asmp, e1, e2, t)) =
  let _ = mk_rule_assumptions metas asmp
  and e1 = mk_rule_is_term metas e1
  and e2 = mk_rule_is_term metas e2
  and t = mk_rule_is_type metas t in
  Rule.EqTerm (e1, e2, t)

and mk_rule_assumptions metas asmp =
  (* XXX should check that asmp is a subset of metas or some such? *)
  ()

and mk_rule_judgement metas = function

  | JudgementIsType t ->
     Rule.JudgementIsType (mk_rule_is_type metas t)

  | JudgementIsTerm e ->
     Rule.JudgementIsTerm (mk_rule_is_term metas e)

  | JudgementEqType eq ->
     Rule.JudgementEqType (mk_rule_eq_type metas eq)

  | JudgementEqTerm eq ->
     Rule.JudgementEqTerm (mk_rule_eq_term metas eq)

and mk_rule_argument metas = function

  | Arg_NotAbstract jdg ->
     let jdg = mk_rule_judgement metas jdg in
     Rule.Arg_NotAbstract jdg

  | Arg_Abstract (x, arg) ->
     let arg = mk_rule_argument metas arg in
     Rule.Arg_Abstract (x, arg)

and mk_rule_arguments metas args =
  List.map (mk_rule_argument metas) args

and mk_rule_abstraction
  : 'a 'b 'c . (Nonce.t list -> 'a -> 'b) -> Nonce.t list -> 'a abstraction -> 'b Rule.abstraction
  = fun form_u metas -> function

    | NotAbstract u ->
       let u = form_u metas u in
       Rule.NotAbstract u

    | Abstract (x, t, abstr) ->
       let t = mk_rule_is_type metas t in
       let abstr = mk_rule_abstraction form_u metas abstr in
       Rule.Abstract (x, t, abstr)

let mk_rule_premise metas = function

  | BoundaryIsType () ->
     Rule.BoundaryIsType ()

  | BoundaryIsTerm t ->
     Rule.BoundaryIsTerm (mk_rule_is_type metas t)

  | BoundaryEqType (t1, t2) ->
     Rule.BoundaryEqType (mk_rule_is_type metas t1, mk_rule_is_type metas t2)

  | BoundaryEqTerm (e1, e2, t) ->
     Rule.BoundaryEqTerm (mk_rule_is_term metas e1, mk_rule_is_term metas e2, mk_rule_is_type metas t)

let fold_prems prems form_concl =
  let rec fold metas = function
    | [] -> Rule.Conclusion (form_concl metas)

    | (mv, prem) :: prems ->
       let prem = mk_rule_abstraction mk_rule_premise metas prem in
       let rl = fold (mv :: metas) prems in
       Rule.Premise (prem, rl)
  in
  fold [] prems

let form_rule prems concl =
  fold_prems prems
  begin fun metas ->
    match concl with
    | BoundaryIsType () ->
       Rule.BoundaryIsType ()

    | BoundaryIsTerm t ->
       Rule.BoundaryIsTerm (mk_rule_is_type metas t)

    | BoundaryEqType (t1, t2) ->
       let t1 = mk_rule_is_type metas t1
       and t2 = mk_rule_is_type metas t2 in
       Rule.BoundaryEqType (t1, t2)

    | BoundaryEqTerm (e1, e2, t) ->
       let e1 = mk_rule_is_term metas e1
       and e2 = mk_rule_is_term metas e2
       and t = mk_rule_is_type metas t in
       Rule.BoundaryEqTerm (e1, e2, t)
  end


let form_derivation prems concl =
  fold_prems prems
  begin fun metas ->
    match concl with
    | JudgementIsType t ->
       Rule.JudgementIsType (mk_rule_is_type metas t)

    | JudgementIsTerm e ->
       Rule.JudgementIsTerm (mk_rule_is_term metas e)

    | JudgementEqType eq ->
       Rule.JudgementEqType (mk_rule_eq_type metas eq)

    | JudgementEqTerm eq ->
       Rule.JudgementEqTerm (mk_rule_eq_term metas eq)
  end
