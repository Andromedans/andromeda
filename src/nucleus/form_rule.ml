open Nucleus_types

(* Check that the argument [p] matches the premise [s]. *)
let check_argument sgn metas s p =
  match s, p with

  | Rule.PremiseIsType s_abstr, ArgumentIsType p_abstr ->
     let s_abstr = Instantiate_meta.abstraction (fun ~lvl _ () -> ()) ~lvl:0 metas s_abstr
     and p_abstr = Sanity.boundary_is_type_abstraction p_abstr in
     if not (Alpha_equal.abstraction (fun () () -> true) s_abstr p_abstr) then
       Error.raise InvalidArgument

  | Rule.PremiseIsTerm s_abstr, ArgumentIsTerm p_abstr ->
     let s = Instantiate_meta.abstraction Instantiate_meta.is_type ~lvl:0 metas s_abstr
     and t = Sanity.boundary_is_term_abstraction sgn p_abstr in
     begin
       match Alpha_equal.abstraction Alpha_equal.is_type t s with
       | false -> Error.raise InvalidArgument
       | true -> ()
     end

  | Rule.PremiseEqType s_abstr, ArgumentEqType p_abstr ->
     let s_abstr = Instantiate_meta.abstraction Instantiate_meta.eq_type ~lvl:0 metas s_abstr
     and p_abstr = Sanity.boundary_eq_type_abstraction p_abstr in
     if not (Alpha_equal.abstraction
               (fun (EqType (_, l1,r1)) (EqType (_, l2,r2)) ->
                  Alpha_equal.is_type l1 l2 && Alpha_equal.is_type r1 r2)
               s_abstr p_abstr)
     then
       Error.raise InvalidArgument

  | Rule.PremiseEqTerm s_abstr, ArgumentEqTerm p_abstr ->
     let s_abstr = Instantiate_meta.abstraction Instantiate_meta.eq_term ~lvl:0 metas s_abstr
     and p_abstr = Sanity.boundary_eq_term_abstraction p_abstr in
     if not (Alpha_equal.abstraction
               (fun (EqTerm (_, e1,e2,t)) (EqTerm (_, e1',e2',t')) ->
                  Alpha_equal.is_term e1 e1'
                  && Alpha_equal.is_term e2 e2'
                  && Alpha_equal.is_type t t')
               s_abstr p_abstr)
     then
       Error.raise InvalidArgument

  | Rule.PremiseIsType _, (ArgumentIsTerm _ | ArgumentEqType _ | ArgumentEqTerm _) -> Error.raise IsTypeExpected
  | Rule.PremiseIsTerm _, (ArgumentIsType _ | ArgumentEqType _ | ArgumentEqTerm _) -> Error.raise IsTermExpected
  | Rule.PremiseEqType _, (ArgumentIsType _ | ArgumentIsTerm _ | ArgumentEqTerm _) -> Error.raise EqTypeExpected
  | Rule.PremiseEqTerm _, (ArgumentIsType _ | ArgumentIsTerm _ | ArgumentEqType _) -> Error.raise EqTermExpected

let arg_of_argument = function
  | ArgumentIsType t -> Mk.arg_is_type t
  | ArgumentIsTerm e -> Mk.arg_is_term e
  | ArgumentEqType eq -> Mk.arg_eq_type eq
  | ArgumentEqTerm eq-> Mk.arg_eq_term eq

let match_argument sgn metas (s : Rule.premise) (p : argument) : argument =
  check_argument sgn metas s p ;
  arg_of_argument p

let match_arguments sgn (premises : Rule.premise list) (arguments : argument list) =
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
let lookup_meta_index mv mvs =
  let rec search k = function
    | [] -> assert false
    | mv' :: mvs ->
       if Name.eq_meta mv mv' then
         k
       else
         search (k+1) mvs
  in
  search 0 mvs

(** The [mk_rule_XYZ] functions are auxiliary functions that should not be
    exposed. The external interface exopses the [form_rule_XYZ] functions defined
    below. *)

let rec mk_rule_is_type metas = function
  | TypeConstructor (c, args) ->
     let args = mk_rule_args metas args in
     Rule.TypeConstructor (c, args)

  | TypeMeta (mv, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     let k = lookup_meta_index mv.meta_name metas in
     Rule.TypeMeta (k, args)

and mk_rule_is_term metas = function
  | TermAtom _ ->
     (* this will be gone when we eliminate atoms *)
     failwith "a free atom cannot appear in a rule"

  | TermMeta (mv, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     let k = lookup_meta_index mv.meta_name metas in
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
     and metas_set = Name.MetaSet.of_list metas in
     let mem_metas_set mv _bnd = Name.MetaSet.mem mv metas_set in
     begin match Name.AtomMap.is_empty free
                 && Name.MetaMap.for_all mem_metas_set is_type_meta
                 && Name.MetaMap.for_all mem_metas_set is_term_meta
                 && Name.MetaMap.for_all mem_metas_set eq_type_meta
                 && Name.MetaMap.for_all mem_metas_set eq_term_meta
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

  | ArgumentIsType abstr ->
     let abstr = mk_rule_abstraction mk_rule_is_type metas abstr in
     Rule.ArgumentIsType abstr

  | ArgumentIsTerm abstr ->
     let abstr = mk_rule_abstraction mk_rule_is_term metas abstr in
     Rule.ArgumentIsTerm abstr

  | ArgumentEqType abstr ->
     let abstr = mk_rule_abstraction mk_rule_eq_type metas abstr in
     Rule.ArgumentEqType abstr

  | ArgumentEqTerm abstr ->
     let abstr = mk_rule_abstraction mk_rule_eq_term metas abstr in
     Rule.ArgumentEqTerm abstr

and mk_rule_args metas args =
  List.map (mk_rule_arg metas) args

and mk_rule_abstraction
  : 'a 'b . (Name.meta list -> 'a -> 'b) -> Name.meta list -> 'a abstraction -> 'b Rule.abstraction
  = fun form_u metas -> function

    | NotAbstract u ->
       let u = form_u metas u in
       Rule.NotAbstract u

    | Abstract (x, t, abstr) ->
       let t = mk_rule_is_type metas t in
       let abstr = mk_rule_abstraction form_u metas abstr in
       Rule.Abstract (x, t, abstr)

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
            Rule.EqType (t1, t2))
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
            Rule.EqTerm (e1, e2, t))
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
