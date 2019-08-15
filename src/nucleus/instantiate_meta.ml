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
  | TypeConstructor (c, args) ->
     let args = arguments ~lvl metas args
     in Mk.type_constructor c args

  | TypeMeta (MetaBound k, es_schema) ->
     let abstr = lookup_meta k metas in
     let es = List.map (fun e_schema -> is_term ~lvl metas e_schema) es_schema in
     begin match Judgement.as_is_type (apply_argument abstr es) with
     | Some t -> t
     | None -> Error.raise IsTypeExpected
     end

  | TypeMeta (MetaFree _  as mv, es_schema) ->
     (** The type of a meta-variable cannot contain any bound meta-variables, as that would mean
         that we have an extension of a signature by a meta-variable, whose type depends on some
         further extension (that we abstracted over). *)
     let es = List.map (fun e_schema -> is_term ~lvl metas e_schema) es_schema in
     Mk.type_meta mv es

and is_term ~lvl (metas : argument list) = function
  | TermBoundVar k -> Mk.bound k

  | TermConstructor (c, args) ->
     let args = arguments ~lvl metas args
     in Mk.term_constructor c args

  | TermConvert (e, asmp, t) ->
     let e = is_term ~lvl metas e
     and asmp = assumptions ~lvl metas asmp
     and t = is_type ~lvl metas t in
     Mk.term_convert e asmp t

  | TermAtom _ as atm ->
     (** The type of an atom cannot contain bound meta-variables. *)
     atm

  | TermMeta (MetaBound k, es_schema) ->
     let abstr = lookup_meta k metas in
     let es = List.map (fun e_schema -> is_term ~lvl metas e_schema) es_schema in
     begin match Judgement.as_is_term (apply_argument abstr es) with
     | Some e -> e
     | None -> Error.raise IsTermExpected
     end

  | TermMeta (MetaFree _ as mv, es_schema) ->
     (** The type of a meta-variable cannot contain any bound meta-variables, as that would mean
         that we have an extension of a signature by a meta-variable, whose type depends on some
         further extension (that we abstracted over). *)
     let es = List.map (fun e_schema -> is_term ~lvl metas e_schema) es_schema in
     Mk.term_meta mv es

and eq_type ~lvl metas (EqType (asmp, t1, t2)) =
  let asmp = assumptions ~lvl metas asmp
  and t1 = is_type ~lvl metas t1
  and t2 = is_type ~lvl metas t2 in
  Mk.eq_type asmp t1 t2

and eq_term ~lvl metas (EqTerm (asmp, e1, e2, t)) =
  let asmp = assumptions ~lvl metas asmp
  and e1 = is_term ~lvl metas e1
  and e2 = is_term ~lvl metas e2
  and t = is_type ~lvl metas t in
  Mk.eq_term asmp e1 e2 t

and arguments ~lvl metas args =
  List.map (argument ~lvl metas) args

and argument ~lvl metas = function
  | Arg_NotAbstract jdg ->
     Arg_NotAbstract (judgement ~lvl metas jdg)

  | Arg_Abstract (x, abstr) ->
     Arg_Abstract (x, argument ~lvl:(lvl+1) metas abstr)

and judgement ~lvl metas = function
  | JudgementIsType t ->
     Mk.arg_is_type (is_type ~lvl metas t)

  | JudgementIsTerm e ->
     Mk.arg_is_term (is_term ~lvl metas e)

  | JudgementEqType eq ->
     (* XXX could do this lazily so that it's discarded when it's an
        argument in a premise, and computed only when it's an argument in
        a constructor in the output of a rule *)
     Mk.arg_eq_type (eq_type ~lvl metas eq)

  | JudgementEqTerm eq ->
     Mk.arg_eq_term (eq_term ~lvl metas eq)

and assumptions ~lvl metas {free_var; free_meta; bound_var; bound_meta} =
  (* It must be the case that [bound_meta] contains only indices smaller than [List.length metas]. *)
  assert (let n = List.length metas in Bound_set.for_all (fun k -> k < n) bound_meta) ;
  let asmp0 =
    List.fold_left
      (fun asmp0 meta -> Assumption.union asmp0 ((Collect_assumptions.argument ~lvl meta)))
      Assumption.empty
      metas
  in
  (* It must be the case that [asmp0] contains no bound metas. *)
  assert (Bound_set.is_empty asmp0.bound_meta) ;
  Assumption.union asmp0 {free_var; free_meta; bound_var; bound_meta=Bound_set.empty}

let rec abstraction inst_u ~lvl metas = function

    | NotAbstract u ->
       let u = inst_u ~lvl metas u
       in Mk.not_abstract u

    | Abstract (x, t, abstr) ->
       let t = is_type ~lvl metas t
       and abstr = abstraction inst_u ~lvl:(lvl+1) metas abstr
       in Mk.abstract x t abstr
