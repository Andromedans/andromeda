(** Types describing patterns that we can match against. These are simple and do not
    bother matching anything under an abstraction (as that is acutally quite tricky). *)

open Eqchk_common

exception Match_fail

module MetaMap =
  Map.Make
    (struct
      type t = int
      let compare = Stdlib.compare
    end)

let add_meta = MetaMap.add


let add_bound atm bounds = BoundMap.(add atm (cardinal bounds) bounds)
let find_bound = BoundMap.find_opt

(** The [collect_XYZ] functions provide low-level functionality for matching a judgement against
    a pattern. They collect the values of meta-variables, but do not check whether all meta-variables
    were matched. *)

let rec collect_is_type sgn metas bounds abstr = function

  | Patt.TypeAddMeta k ->
     add_meta k abstr metas

  | Patt.TypeNormal patt ->
     begin match Nucleus.(as_not_abstract abstr) with
     | None
     | Some Nucleus.(JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _) ->
        raise Match_fail
     | Some Nucleus.(JudgementIsType t) ->
        collect_is_normal_type sgn metas bounds t patt
     end

and collect_is_normal_type sgn metas bounds t = function

  | Patt.TypeConstructor (c, args) ->
     begin match Nucleus.invert_is_type sgn t with

     | Nucleus.Stump_TypeConstructor (c', args') ->
        if Ident.equal c c' then
          collect_arguments sgn metas bounds args' args
        else
          raise Match_fail

     | Nucleus.Stump_TypeMeta _ ->
        raise Match_fail
     end

  | Patt.TypeFreeMeta (n, es) ->
     begin match Nucleus.invert_is_type sgn t with
     | Nucleus.Stump_TypeMeta (mv, es') ->
        if Nonce.equal n (Nucleus.meta_nonce mv) then
          collect_is_terms sgn metas bounds es' es
        else
          raise Match_fail

     | Nucleus.Stump_TypeConstructor _ ->
        raise Match_fail
     end

and collect_is_term sgn metas bounds abstr = function

  | Patt.TermAddMeta k ->
     add_meta k abstr metas

  | Patt.TermNormal patt ->
     begin match Nucleus.as_not_abstract abstr with
     | None
     | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
        raise Match_fail

     | Some (Nucleus.JudgementIsTerm e) ->
        collect_normal_is_term sgn metas bounds e patt
     end

and collect_normal_is_term sgn metas bounds e = function

  | Patt.TermConstructor (c, args) ->
     let rec fold e =
       match Nucleus.invert_is_term sgn e with

       | Nucleus.Stump_TermConstructor (c', args') ->
          if Ident.equal c c' then
            collect_arguments sgn metas bounds args' args
          else
            raise Match_fail

       | Nucleus.Stump_TermConvert (e, _) ->
             fold e

       | Nucleus.(Stump_TermAtom _ | Stump_TermMeta _) ->
          raise Match_fail
     in
     fold e

  | Patt.TermAtom n ->
     let rec fold e =
       match Nucleus.invert_is_term sgn e with
       | Nucleus.Stump_TermAtom atm' ->
          if Nonce.equal n (Nucleus.atom_nonce atm') then
            metas
          else
            raise Match_fail
       | Nucleus.Stump_TermConvert (e, _) -> fold e
       | Nucleus.(Stump_TermConstructor _ | Stump_TermMeta _) ->
          raise Match_fail
     in
     fold e

  | Patt.TermFreeMeta (n, es) ->
     let rec fold e =
       begin match Nucleus.invert_is_term sgn e with
       | Nucleus.Stump_TermMeta (mv, es') ->
          if Nonce.equal n (Nucleus.meta_nonce mv) then
            collect_is_terms sgn metas bounds es' es
          else
            raise Match_fail

       | Nucleus.Stump_TermConvert (e, _) -> fold e
       | Nucleus.(Stump_TermConstructor _ | Stump_TermAtom _) ->
          raise Match_fail
     end
     in
     fold e

  | Patt.TermBound v ->
    let rec fold e =
    begin match Nucleus.invert_is_term sgn e with
    | Nucleus.Stump_TermAtom a ->
      begin match find_bound a bounds with
      | Some j -> if j == v then metas else raise Match_fail
      | None -> raise Match_fail
      end
    | Nucleus.(Stump_TermConvert (e, _)) -> fold e
    | Nucleus.(Stump_TermMeta _ | Stump_TermConstructor _) ->
      raise Match_fail
    end
    in
    fold e

and collect_is_terms sgn metas bounds es es' =
  match es, es' with

  | [], [] -> metas

  | e :: es, e' :: es' ->
     let e = Nucleus.(abstract_not_abstract (JudgementIsTerm e)) in
     let metas = collect_is_term sgn metas bounds e e' in
     collect_is_terms sgn metas bounds es es'

  | [], _::_ | _::_, [] ->
     raise Match_fail

and collect_arguments sgn metas bounds args_e args_r =
  match args_e, args_r with
  | [], [] -> metas

  | e :: args_e, r :: args_r ->
     let metas = collect_argument sgn metas bounds e r in
     collect_arguments sgn metas bounds args_e args_r

  | [], _::_ | _::_, [] ->
     raise Match_fail

and collect_argument sgn metas bounds jdg arg_abstr =
  let rec fold jdg abstr bounds =
    match Nucleus.invert_judgement_abstraction jdg, abstr with
    | Nucleus.Stump_Abstract (atm, jdg), Patt.Arg_Abstract (_, abstr) ->
      let bounds = add_bound atm bounds in
      fold jdg abstr bounds

    | Nucleus.Stump_Abstract _, Patt.Arg_NotAbstract patt_jdg ->
      (* Is the judgement eta-expanded metavariable? *)
      begin
        match patt_jdg with

        | Patt.ArgumentIsType r -> collect_is_type sgn metas bounds jdg r

        | Patt.ArgumentIsTerm r -> collect_is_term sgn metas bounds jdg r
      end


    | Nucleus.Stump_NotAbstract jdg , Patt.Arg_NotAbstract patt_jdg ->
      begin
        match patt_jdg with

        | Patt.ArgumentIsType r -> collect_is_type sgn metas bounds (Nucleus.abstract_not_abstract jdg) r

        | Patt.ArgumentIsTerm r -> collect_is_term sgn metas bounds (Nucleus.abstract_not_abstract jdg) r
      end

      | Nucleus.Stump_NotAbstract _, Patt.Arg_Abstract _ ->
        raise Match_fail
  in
  fold jdg arg_abstr bounds


(** Given a mapping of de Bruijn indices [n_eq, ..., n_eq + n_ob-1] to their values, convert
   them to a list. *)
let metas_to_list n_ob n_eq metas =
  let rec fold lst i =
    if i >= n_eq + n_ob then
      Some lst
    else
       match MetaMap.find_opt i metas with
       | None -> None
       | Some x -> fold (x :: lst) (i + 1)
  in
  fold [] n_eq

(** The [match_XYZ] functions match judgements against patterns, making sure
    to collect precisely meta-variables [n_eq, ..., n_ob + n_eq-1]. *)

(** Match type [t] against pattern [r] with meta-indices [n_eq, ..., n_ob + n_eq-1]. *)
let match_is_type sgn t (r, n_ob, n_eq) =
  try
    let t = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
    metas_to_list n_ob n_eq (collect_is_type sgn MetaMap.empty BoundMap.empty t r)
  with
    Match_fail -> None

(** Match term [e] against pattern [r] with meta-indices [0, ..., k-1]. *)
let match_is_term sgn e (r, n_ob, n_eq) =
  try
    let e = Nucleus.(abstract_not_abstract (JudgementIsTerm e)) in
    metas_to_list n_ob n_eq (collect_is_term sgn MetaMap.empty BoundMap.empty e r)
  with
    Match_fail -> None

exception Eta_expanded_meta_fail

(** Is the given judgement abstraction an eta-expanded meta-variable? *)
let rec extract_meta metas abstr =
  let rec fold k = function

    | Nucleus_types.Arg_Abstract (_, abstr) -> fold (k+1) abstr

    | Nucleus_types.Arg_NotAbstract jdg ->
       (* check that given arguments are bound variables j, j-1, ..., 0 *)
       let rec check_es j = function

         | [] -> if j <> 0 then raise Eta_expanded_meta_fail

         | Nucleus_types.TermBoundVar i :: es ->
            if i = j-1 then check_es (j-1) es else raise Eta_expanded_meta_fail

         | Nucleus_types.TermConvert (e, _, _) :: es -> check_es k (e :: es)

         | Nucleus_types.(TermAtom _ | TermMeta _ | TermConstructor _) :: _ ->
            raise Eta_expanded_meta_fail

       in
       begin match jdg with

       | Nucleus_types.JudgementIsTerm e ->
          begin match e with
          | Nucleus_types.(TermMeta (MetaBound m, es)) ->
             check_es k es ;
             if Bound_set.mem m metas then
               raise (EqchkError (Form_fail (NonLinearPattern m)))
             else
               let metas = Bound_set.add m metas in
               metas, Patt.(Arg_NotAbstract (ArgumentIsTerm (Patt.TermAddMeta m)))
          | Nucleus_types.TermConvert (e, _, _) -> extract_meta metas (Nucleus_types.(Arg_NotAbstract (JudgementIsTerm e)))

          | Nucleus_types.(TermMeta (MetaFree _, _) | TermBoundVar _ | TermAtom _ |
                           TermConstructor _) ->
             raise Eta_expanded_meta_fail

          end

       | Nucleus_types.JudgementIsType t ->
          begin match t with
          | Nucleus_types.(TypeMeta (MetaBound m, es)) ->
             check_es k es ;
             if Bound_set.mem m metas then
               raise (EqchkError (Form_fail (NonLinearPattern m)))
             else
               let metas = Bound_set.add m metas in
               metas, Patt.(Arg_NotAbstract (ArgumentIsType (Patt.TypeAddMeta m)))

          | Nucleus_types.(TypeMeta (MetaFree _, _) | TypeConstructor _) ->
             raise Eta_expanded_meta_fail
          end

       | Nucleus_types.(JudgementEqType _ | JudgementEqTerm _) ->
          raise Eta_expanded_meta_fail
       end
  in
  fold 0 abstr


(** The [form_XYZ] functions form a pattern from a given judgement. They return the set of
    bound meta-variables that were encountered and turned into pattern variables. *)

let rec form_is_type metas = function

  | Nucleus_types.TypeConstructor (c, args) ->
     let metas, args = form_arguments metas args in
     metas, Patt.(TypeNormal (TypeConstructor (c, args)))

  | Nucleus_types.(TypeMeta (MetaBound i, [])) ->
     if Bound_set.mem i metas then
       raise (EqchkError (Form_fail (NonLinearPattern i)))
     else
       let metas = Bound_set.add i metas in
       metas, Patt.TypeAddMeta i


  | Nucleus_types.(TypeMeta (MetaFree {meta_nonce=n;_}, es)) ->
     let rec fold metas es_out = function

       | [] ->
          let es_out = List.rev es_out in
          metas, Patt.(TypeNormal (TypeFreeMeta (n, es_out)))

       | e :: es ->
          let metas, e = form_is_term metas e in
          fold metas (e :: es_out) es
     in
     fold metas [] es

  | Nucleus_types.(TypeMeta (MetaBound k, _::_)) ->
     raise (EqchkError (Form_fail (MetaBoundTypeInPatt k)))


and form_is_term metas e =
  match e with
  | Nucleus_types.TermBoundVar v ->
     metas, Patt.(TermNormal (TermBound v))

  | Nucleus_types.(TermAtom {atom_nonce=n; _}) ->
     metas, Patt.(TermNormal (TermAtom n))

  | Nucleus_types.TermConstructor (c, args) ->
     let metas, args = form_arguments metas args in
     metas, Patt.(TermNormal (TermConstructor (c, args)))

  | Nucleus_types.(TermMeta (MetaBound i, [])) ->
     if Bound_set.mem i metas then
       raise (EqchkError (Form_fail (NonLinearPattern i)))
     else
       let metas = Bound_set.add i metas in
       metas, Patt.TermAddMeta i

  | Nucleus_types.(TermMeta (MetaFree {meta_nonce=n;_}, es)) ->
     let rec fold metas es_out = function

       | [] ->
          let es_out = List.rev es_out in
          metas, Patt.(TermNormal (TermFreeMeta (n, es_out)))

       | e :: es ->
          let metas, e = form_is_term metas e in
          fold metas (e :: es_out) es
     in
     fold metas [] es

  | Nucleus_types.TermConvert (e, _, _) ->
     form_is_term metas e

  | Nucleus_types.(TermMeta (MetaBound k, _::_)) ->
     raise (EqchkError (Form_fail (MetaBoundTermInPatt k)))


and form_arguments metas args =
  let rec fold metas args_out = function

    | [] ->
       let args_out = List.rev args_out in
       metas, args_out

    | arg :: args ->
       let metas, arg = form_argument metas arg in
       fold metas (arg :: args_out) args
  in
  fold metas [] args

and form_argument metas = function
  | Nucleus_types.Arg_NotAbstract jdg ->
     begin match jdg with
     | Nucleus_types.JudgementIsTerm e ->
        let metas, e = form_is_term metas e in
        metas, Patt.(Arg_NotAbstract (ArgumentIsTerm e))

     | Nucleus_types.JudgementIsType t ->
        let metas, t = form_is_type metas t in
        metas, Patt.(Arg_NotAbstract (ArgumentIsType t))

     | Nucleus_types.JudgementEqType ty ->
       (* For the time being we don't support equality arguments.
           It's not entirely clear how we should treat them. *)
        raise (EqchkError (Form_fail (EqualityTypeArgumentInPatt ty)))
     | Nucleus_types.JudgementEqTerm e ->
        (* For the time being we don't support equality arguments.
           It's not entirely clear how we should treat them. *)
           raise (EqchkError (Form_fail (EqualityTermArgumentInPatt e)))
     end

  | Nucleus_types.Arg_Abstract (atm, jdg) as abstr ->
      (* Is this an eta-expanded meta-variable? *)
      try
        extract_meta metas abstr
      with
        Eta_expanded_meta_fail ->
          raise (EqchkError (Form_fail (AbstractionInPattern abstr)))


(** Check that the given set of integers contains
    precisely the numbers mi, mi + 1, ..., ma-1 *)
let is_range s mi ma =
  let rec scan k =
    if k == mi then true else
      Bound_set.mem (k-1) s && scan (k-1)
  in
  Bound_set.cardinal s = (ma - mi) && scan ma

(** Construct a pattern [p] from type [t], and verify that the pattern captures exactly
   the bound meta-variables [n_eq, ..., n_ob + n_eq -1]. Return the pair [(p, n_ob, n_eq)]
   to be used as part of a beta or extensionality rule. *)
let make_is_type n_ob n_eq t =
   let metas, patt = form_is_type Bound_set.empty t in
   if is_range metas n_eq (n_eq + n_ob) then
     (patt, n_ob, n_eq)
   else
     raise (EqchkError (Form_fail (CaptureMetasNotCorrectType t)))

(** Construct a pattern [p] from term [e], and verify that the pattern captures exactly
   the bound meta-variables [n_eq, ..., n_ob + n_eq -1]. Return the pair [(p, n_ob, n_eq)]
   to be used as part of a beta or extensionality rule. *)
let make_is_term n_ob n_eq e =
   let metas, patt = form_is_term Bound_set.empty e in
   if is_range metas n_eq (n_ob + n_eq) then
     (patt, n_ob, n_eq)
   else
     raise (EqchkError (Form_fail (CaptureMetasNotCorrectTerm e)))