open Nucleus_types

(** [apply_argument arg args] fully applies an argument to the given
   arguments. The abstraction level of [arg] is expected to match the length of
   [args]. *)
let apply_argument arg args =
  let rec fold es arg args =
    match arg, args with
    | Arg_NotAbstract u, [] -> Instantiate_bound.judgement_fully es u
    | Arg_Abstract (_, arg), e :: args -> fold (e :: es) arg args
    | Arg_Abstract _, [] -> Error.raise TooFewArguments
    | Arg_NotAbstract _, _::_ -> Error.raise TooManyArguments
  in
  fold [] arg args

let lookup_meta k (metas : argument indices) = Indices.nth metas k

let rec is_type ~lvl metas = function
  | Rule.TypeConstructor (c, args) ->
     let args = arguments ~lvl metas args
     in Mk.type_constructor c args

  | Rule.TypeMeta (k, es_schema) ->
     let abstr = lookup_meta k metas in
     let es = List.map (fun e_schema -> is_term ~lvl metas e_schema) es_schema in
     begin match Judgement.as_is_type (apply_argument abstr es) with
     | Some t -> t
     | None -> Error.raise IsTypeExpected
     end

and is_term ~lvl (metas : argument list) = function
  | Rule.TermBound k -> Mk.bound k

  | Rule.TermConstructor (c, args) ->
     let args = arguments ~lvl metas args
     in Mk.term_constructor c args

  | Rule.TermMeta (k, es_schema) ->
     let abstr = lookup_meta k metas in
     let es = List.map (fun e_schema -> is_term ~lvl metas e_schema) es_schema in
     begin match Judgement.as_is_term (apply_argument abstr es) with
     | Some e -> e
     | None -> Error.raise IsTermExpected
     end

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
  | Rule.NotAbstract jdg ->
     Arg_NotAbstract (judgement ~lvl metas jdg)

  | Rule.Abstract (x, _, abstr) ->
     Arg_Abstract (x, argument ~lvl:(lvl+1) metas abstr)

and judgement ~lvl metas = function
  | Rule.JudgementIsType t ->
     Mk.arg_is_type (is_type ~lvl metas t)

  | Rule.JudgementIsTerm e ->
     Mk.arg_is_term (is_term ~lvl metas e)

  | Rule.JudgementEqType eq ->
     (* XXX could do this lazily so that it's discarded when it's an
        argument in a premise, and computed only when it's an argument in
        a constructor in the output of a rule *)
     Mk.arg_eq_type (eq_type ~lvl metas eq)

  | Rule.JudgementEqTerm eq ->
     Mk.arg_eq_term (eq_term ~lvl metas eq)

let rec abstraction inst_u ~lvl metas = function

    | Rule.NotAbstract u ->
       let u = inst_u ~lvl metas u
       in Mk.not_abstract u

    | Rule.Abstract (x, t, abstr) ->
       let t = is_type ~lvl metas t
       and abstr = abstraction inst_u ~lvl:(lvl+1) metas abstr
       in Mk.abstract x t abstr

(* let annotate_arguments argument prems args =
 *   let rec fold argument prems args =
 *     match argument, prems, args with
 *     | Arg_NotAbstract jdg, [], [] -> jdg
 *     | Arg_Abstract (x, argument), prem::prems, arg::args ->
 *
 *   in
 *   fold *)
