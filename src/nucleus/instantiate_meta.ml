open Nucleus_types

(** [fully_apply_abstraction_no_typechecks inst_u abstr args] fully applies an
    abstraction to the given arguments. The abstraction level of [abstr] is
    expected to match the length of [args]. No checks that the types of [args]
    match the types of the variables that [abstr] abstracts over are
    performed, because we expect that this function is only used in situations
    where such a verification has already happened. *)
let fully_apply_abstraction_no_typechecks inst_u abstr args =
  let rec fold es abstr args =
    match abstr, args with
    | NotAbstract u, [] -> inst_u es u
    | Abstract (_, abstr), e :: args -> fold (e :: es) abstr args
    | Abstract _, [] -> Error.raise TooFewArguments
    | NotAbstract _, _::_ -> Error.raise TooManyArguments
  in
  fold [] abstr args

let lookup_term_meta k metas =
  match Indices.nth metas k with
  | ArgumentIsTerm e_abstr -> e_abstr
  | ArgumentIsType _ | ArgumentEqType _ | ArgumentEqTerm _ -> Error.raise TermExpected

let lookup_type_meta k metas =
  match Indices.nth metas k with
  | ArgumentIsType t_abstr -> t_abstr
  | ArgumentIsTerm _ | ArgumentEqType _ | ArgumentEqTerm _ -> Error.raise TypeExpected

(** [instantiate ~lvl metas] instantiates  *)

let rec is_type ~lvl metas = function
  | Rule.TypeConstructor (c, args) ->
     let args = arguments ~lvl metas args
     in Mk.type_constructor c args

  | Rule.TypeMeta (k, es_schema) ->
     let t_abstr = lookup_type_meta k metas in
     let es = List.map (fun e_schema -> is_term ~lvl metas e_schema) es_schema in
     fully_apply_abstraction_no_typechecks (Instantiate_bound.is_type_fully ?lvl:None) t_abstr es

and is_term ~lvl metas = function
  | Rule.TermBound k -> Mk.bound k

  | Rule.TermConstructor (c, args) ->
     let args = arguments ~lvl metas args
     in Mk.term_constructor c args

  | Rule.TermMeta (k, es_schema) ->
     let e_abstr = lookup_term_meta k metas in
     let es = List.map (fun e_schema -> is_term ~lvl metas e_schema) es_schema in
     fully_apply_abstraction_no_typechecks (Instantiate_bound.is_term_fully ?lvl:None) e_abstr es

and eq_type ~lvl metas (Rule.EqType (t1, t2)) =
  let t1 = is_type ~lvl metas t1
  and t2 = is_type ~lvl metas t2 in
  Mk.eq_type Assumption.empty t1 t2

and eq_term ~lvl metas (Rule.EqTerm (e1, e2, t)) =
  let e1 = is_term ~lvl metas e1
  and e2 = is_term ~lvl metas e2
  and t = is_type ~lvl metas t in
  Mk.eq_term Assumption.empty e1 e2 t

and arguments ~lvl metas args =
  List.map (argument ~lvl metas) args

and argument ~lvl metas = function
  | Rule.ArgumentIsType abstr ->
     let abstr = abstraction is_type ~lvl metas abstr
     in Mk.arg_is_type abstr

  | Rule.ArgumentIsTerm abstr ->
     let abstr = abstraction is_term ~lvl metas abstr
     in Mk.arg_is_term abstr

  | Rule.ArgumentEqType abstr ->
     (* XXX could do this lazily so that it's discarded when it's an
            argument in a premise, and computed only when it's an argument in
            a constructor in the output of a rule *)
     let abstr = abstraction eq_type ~lvl metas abstr
     in Mk.arg_eq_type abstr

  | Rule.ArgumentEqTerm abstr ->
     let abstr = abstraction eq_term ~lvl metas abstr
     in Mk.arg_eq_term abstr

and abstraction
  : 'a 'b . (lvl:int -> indices -> 'a -> 'b) ->
    lvl:int -> indices -> 'a Rule.abstraction -> 'b abstraction
  = fun inst_u ~lvl metas -> function

    | Rule.NotAbstract u ->
       let u = inst_u ~lvl metas u
       in Mk.not_abstract u

    | Rule.Abstract (x, t, abstr) ->
       let t = is_type ~lvl metas t in
       let atm = {atom_nonce = Nonce.create x; atom_type = t}
       and abstr = abstraction inst_u ~lvl:(lvl+1) metas abstr
       in Mk.abstract atm abstr
