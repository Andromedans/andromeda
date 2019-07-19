open Nucleus_types

(* Instantiate a premise with meta-variables to obtain an abstracted boundary. *)
let instantiate_premise metas prem =
  match prem with

  | Rule.PremiseIsType abstr ->
     let bdry = Instantiate_meta.abstraction (fun ~lvl _ () -> ()) ~lvl:0 metas abstr in
     BoundaryIsType bdry

  | Rule.PremiseIsTerm abstr ->
     let bdry = Instantiate_meta.abstraction Instantiate_meta.is_type ~lvl:0 metas abstr in
     BoundaryIsTerm bdry

  | Rule.PremiseEqType abstr ->
     let bdry =
       Instantiate_meta.abstraction
         (fun ~lvl metas (t1, t2) -> (Instantiate_meta.is_type ~lvl metas t1, Instantiate_meta.is_type ~lvl metas t2))
         ~lvl:0 metas abstr
     in
     BoundaryEqType bdry

  | Rule.PremiseEqTerm abstr ->
     let bdry =
       Instantiate_meta.abstraction
         (fun ~lvl metas (a, b, t) ->
           (Instantiate_meta.is_term ~lvl metas a,
            Instantiate_meta.is_term ~lvl metas b,
            Instantiate_meta.is_type ~lvl metas t))
         ~lvl:0 metas abstr in
     BoundaryEqTerm bdry

(* Check that the argument [arg] matches the premise [prem], given [metas] *)
let check_argument sgn metas arg prem =
  match arg, instantiate_premise metas prem with

  | JudgementIsType abstr, BoundaryIsType bdry ->
     Alpha_equal.check_is_type_boundary abstr bdry

  | JudgementIsTerm abstr, BoundaryIsTerm bdry  ->
     Alpha_equal.check_is_term_boundary sgn abstr bdry

  | JudgementEqType abstr, BoundaryEqType bdry ->
     Alpha_equal.check_eq_type_boundary abstr bdry

  | JudgementEqTerm abstr, BoundaryEqTerm bdry  ->
     Alpha_equal.check_eq_term_boundary abstr bdry

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

let match_argument sgn metas (s : Rule.premise) (p : judgement) : judgement =
  failwith "form_rule match_argument shouldn't be needed"
  (* check_argument sgn metas s p ;
   * arg_of_argument p *)

let match_arguments sgn (premises : Rule.premise list) (arguments : judgement list) =
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
     let args = mk_rule_args metas args in
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
     let args = mk_rule_args metas args in
     Rule.TermConstructor (c, args)

  | TermBound k ->
     Rule.TermBound k

  | TermConvert (e, asmp, t) ->
     let {free; is_type_meta; is_term_meta; eq_type_meta; eq_term_meta; bound} = asmp
     (* NB: We do not check that the types of the metas match because we assume that
        the type of a meta never changes. *)
     and metas_set = Nonce.set_of_list metas in
     let mem_metas_set mv _bnd = Nonce.set_mem mv metas_set in
     begin match Nonce.map_is_empty free
                 && Nonce.map_for_all mem_metas_set is_type_meta
                 && Nonce.map_for_all mem_metas_set is_term_meta
                 && Nonce.map_for_all mem_metas_set eq_type_meta
                 && Nonce.map_for_all mem_metas_set eq_term_meta
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
  Print.error "should check that asmp is a subset of metas or some such@." ;
  ()

and mk_rule_arg metas = function

  | JudgementIsType abstr ->
     let abstr = mk_rule_abstraction mk_rule_is_type metas abstr in
     Rule.JudgementIsType abstr

  | JudgementIsTerm abstr ->
     let abstr = mk_rule_abstraction mk_rule_is_term metas abstr in
     Rule.JudgementIsTerm abstr

  | JudgementEqType abstr ->
     let abstr = mk_rule_abstraction mk_rule_eq_type metas abstr in
     Rule.JudgementEqType abstr

  | JudgementEqTerm abstr ->
     let abstr = mk_rule_abstraction mk_rule_eq_term metas abstr in
     Rule.JudgementEqTerm abstr

and mk_rule_args metas args =
  List.map (mk_rule_arg metas) args

and mk_rule_abstraction
  : 'a 'b 'c . (Nonce.t list -> 'a -> 'b) -> Nonce.t list -> 'a abstraction -> 'b Rule.abstraction
  = fun form_u metas -> function

    | NotAbstract u ->
       let u = form_u metas u in
       Rule.NotAbstract u

    | Abstract ({atom_nonce=x; atom_type=t}, abstr) ->
       let t = mk_rule_is_type metas t in
       let abstr = mk_rule_abstraction form_u metas abstr in
       Rule.Abstract (Nonce.name x, t, abstr)

let mk_rule_premise metas = function

  | BoundaryIsType abstr ->
     let abstr = mk_rule_abstraction (fun _ () -> ()) metas abstr in
     Rule.PremiseIsType abstr

  | BoundaryIsTerm abstr ->
     let abstr =
       mk_rule_abstraction (fun metas t -> mk_rule_is_type metas t) metas abstr
     in
     Rule.PremiseIsTerm abstr

  | BoundaryEqType abstr ->
     let abstr =
       mk_rule_abstraction
         (fun metas (t1, t2) ->
            let t1 = mk_rule_is_type metas t1
            and t2 = mk_rule_is_type metas t2 in
            (t1, t2))
         metas abstr
     in
     Rule.PremiseEqType abstr

  | BoundaryEqTerm abstr ->
     let abstr =
       mk_rule_abstraction
         (fun metas (e1, e2, t) ->
            let e1 = mk_rule_is_term metas e1
            and e2 = mk_rule_is_term metas e2
            and t = mk_rule_is_type metas t in
            (e1, e2, t))
         metas abstr
     in
     Rule.PremiseEqTerm abstr

let mk_rule_premises form_u prems u =
  let rec fold metas prems_out = function
    | [] ->
       let u = form_u metas u in
       let prems_out = List.rev prems_out in
       prems_out, u

    | (mv, prem) :: prems ->
       let prem = mk_rule_premise metas prem in
       fold (mv :: metas) (prem :: prems_out) prems
  in
  fold [] [] prems

let form_rule_is_type prems =
  mk_rule_premises (fun _ () -> ()) prems ()

let form_rule_is_term prems t =
  mk_rule_premises mk_rule_is_type prems t

let form_rule_eq_type prems (t1, t2) =
  mk_rule_premises
    (fun metas (t1, t2) ->
       let t1 = mk_rule_is_type metas t1
       and t2 = mk_rule_is_type metas t2 in
       (t1, t2))
    prems
    (t1, t2)

let form_rule_eq_term prems (e1, e2, t) =
  mk_rule_premises
    (fun metas (e1, e2, t) ->
       let e1 = mk_rule_is_term metas e1
       and e2 = mk_rule_is_term metas e2
       and t = mk_rule_is_type metas t in
       (e1, e2, t))
    prems
    (e1, e2, t)
