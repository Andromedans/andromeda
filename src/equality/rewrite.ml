(** Types describing patterns that we can match against. These are simple and do not
    bother matching anything under an abstraction (as that is acutally quite tricky). *)

type is_type' =
  | PattTypeAddMeta of int
  | PattTypeCheckMeta of int
  | PattTypeConstructor of Ident.t * argument list
  | PattTypeFreeMeta of Nonce.t * is_term' list

and is_term' =
  | PattTermAddMeta of int
  | PattTermCheckMeta of int
  | PattTermConstructor of Ident.t * argument list
  | PattTermFreeMeta of Nonce.t * is_term' list
  | PattTermAtom of Nonce.t

(* and eq_type' =
 *   | PattEqTypeAddMeta of int
 *   | PattEqTypeCheckMeta of int
 *   | PattEqTypeBoundary of is_type' * is_type'
 *
 * and eq_term' =
 *   | PattEqTermAddMeta of int
 *   | PattEqTermCheckMeta of int
 *   | PattEqTermBoundary of is_term' * is_term' * is_type' *)

and argument =
  | PattArgumentIsType of is_type'
  | PattArgumentIsTerm of is_term'
  (* | PattArgumentEqType of eq_type'
   * | PattArgumentEqTerm of eq_term' *)

(** the exported types also record how many meta-variables we're capturing. *)
type is_term = is_term' * int
type is_type = is_type' * int

exception Match_fail

module MetaMap =
  Map.Make
    (struct
      type t = int
      let compare = Stdlib.compare
    end)

let add_meta = MetaMap.add

(** Verifty that the [abstr] equals the abstraction that the bound meta-variable [k]
    was matched to previosuly. *)
let check_meta k abstr metas =
  let abstr' = MetaMap.find k metas in
  if not (Nucleus.alpha_equal_abstraction Nucleus.alpha_equal_judgement abstr abstr') then
    raise Match_fail


(** The [collect_XYZ] functions provide low-level functionality for matching a judgement against
    a pattern. They collect the values of meta-variables, but do not check whether all meta-variables
    were matched. *)

let rec collect_is_type sgn metas abstr = function

  | PattTypeAddMeta k ->
     add_meta k abstr metas

  | PattTypeCheckMeta k ->
     check_meta k abstr metas ;
     metas

  | PattTypeConstructor (c, args) ->
     begin match Nucleus.as_not_abstract abstr with
     | None
     | Some Nucleus.(JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _) ->
        raise Match_fail

     | Some (Nucleus.JudgementIsType t) ->
        begin match Nucleus.invert_is_type sgn t with

        | Nucleus.Stump_TypeConstructor (c', args') ->
           if Ident.equal c c' then
             collect_arguments sgn metas args' args
           else
             raise Match_fail

        | Nucleus.Stump_TypeMeta _ ->
           raise Match_fail
        end
     end

  | PattTypeFreeMeta (n, es) ->
     begin match Nucleus.as_not_abstract abstr with
     | None
     | Some Nucleus.(JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _) ->
        raise Match_fail

     | Some (Nucleus.JudgementIsType t) ->
        begin match Nucleus.invert_is_type sgn t with
          | Nucleus.Stump_TypeMeta (n', _, es') ->
             if Nonce.equal n n' then
               collect_is_terms sgn metas es' es
             else
               raise Match_fail

          | Nucleus.Stump_TypeConstructor _ ->
             raise Match_fail
        end
     end



and collect_is_term sgn metas abstr = function

  | PattTermAddMeta k ->
     add_meta k abstr metas

  | PattTermCheckMeta k ->
     check_meta k abstr metas ;
     metas

  | PattTermConstructor (c, args) ->
     begin match Nucleus.as_not_abstract abstr with
     | None -> raise Match_fail
     | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
        raise Match_fail

     | Some (Nucleus.JudgementIsTerm e) ->
        let rec fold e =
          match Nucleus.invert_is_term sgn e with

          | Nucleus.Stump_TermConstructor (c', args') ->
             if Ident.equal c c' then
               collect_arguments sgn metas args' args
             else
               raise Match_fail

          | Nucleus.Stump_TermConvert (e, _) ->
             fold e

       | Nucleus.(Stump_TermAtom _ | Stump_TermMeta _) ->
          raise Match_fail
        in
        fold e

     end

  | PattTermAtom n ->
     begin match Nucleus.as_not_abstract abstr with
       | None -> raise Match_fail
       | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
          raise Match_fail

       | Some (Nucleus.JudgementIsTerm e) ->
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
     end

  | PattTermFreeMeta (n, es) ->
     begin match Nucleus.as_not_abstract abstr with
     | None
     | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
        raise Match_fail

     | Some (Nucleus.JudgementIsTerm e) ->
        let rec fold e =
          match Nucleus.invert_is_term sgn e with
          | Nucleus.Stump_TermMeta (n', _, es') ->
             if Nonce.equal n n' then
               collect_is_terms sgn metas es' es
             else
               raise Match_fail

          | Nucleus.Stump_TermConvert (e, _) -> fold e
          | Nucleus.(Stump_TermConstructor _ | Stump_TermAtom _) ->
             raise Match_fail
        in
        fold e
     end


and collect_is_terms sgn metas es es' =
  match es, es' with

  | [], [] -> metas

  | e :: es, e' :: es' ->
     let e = Nucleus.(abstract_not_abstract (JudgementIsTerm e)) in
     let metas = collect_is_term sgn metas e e' in
     collect_is_terms sgn metas es es'

  | [], _::_ | _::_, [] ->
     raise Match_fail


(* and collect_eq_type sgn metas abstr = function
 *
 *   | PattEqTypeAddMeta k ->
 *      add_meta k abstr metas
 *
 *   | PattEqTypeCheckMeta k ->
 *      check_meta k abstr metas ;
 *      metas
 *
 *   | PattEqTypeBoundary (r1, r2) ->
 *      begin match Nucleus.as_not_abstract abstr with
 *
 *      | None -> raise Match_fail
 *
 *      | Some (Nucleus.JudgementEqType eq) ->
 *         let Nucleus.Stump_EqType (_asmp, t1, t2) = Nucleus.invert_eq_type eq in
 *         let abstr1 = Nucleus.(abstract_not_abstract (JudgementIsType t1))
 *         and abstr2 = Nucleus.(abstract_not_abstract (JudgementIsType t2)) in
 *         let metas = collect_is_type sgn metas abstr1 r1 in
 *         let metas = collect_is_type sgn metas abstr2 r2 in
 *         metas
 *
 *      | Some Nucleus.(JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _) ->
 *         raise Match_fail
 *      end
 *
 *
 * and collect_eq_term sgn metas abstr = function
 *
 *   | PattEqTermAddMeta k ->
 *      add_meta k abstr metas
 *
 *   | PattEqTermCheckMeta k ->
 *      check_meta k abstr metas ;
 *      metas
 *
 *   | PattEqTermBoundary (r1, r2, rt) ->
 *      begin match Nucleus.as_not_abstract abstr with
 *
 *      | None -> raise Match_fail
 *
 *      | Some (Nucleus.JudgementEqTerm eq) ->
 *         let Nucleus.Stump_EqTerm (_asmp, e1, e2, t) = Nucleus.invert_eq_term sgn eq in
 *         let abstr1 = Nucleus.(abstract_not_abstract (JudgementIsTerm e1))
 *         and abstr2 = Nucleus.(abstract_not_abstract (JudgementIsTerm e2))
 *         and abstrt = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
 *         let metas = collect_is_type sgn metas abstrt rt in
 *         let metas = collect_is_term sgn metas abstr1 r1 in
 *         let metas = collect_is_term sgn metas abstr2 r2 in
 *         metas
 *
 *      | Some Nucleus.(JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _) ->
 *         raise Match_fail
 *      end *)


and collect_arguments sgn metas args_e args_r =
  match args_e, args_r with
  | [], [] -> metas

  | e :: args_e, r :: args_r ->
     let metas = collect_argument sgn metas e r in
     collect_arguments sgn metas args_e args_r

  | [], _::_ | _::_, [] ->
     raise Match_fail


and collect_argument sgn metas jdg = function

  | PattArgumentIsType r -> collect_is_type sgn metas jdg r

  | PattArgumentIsTerm r -> collect_is_term sgn metas jdg r

  (* | PattArgumentEqType r -> collect_eq_type sgn metas jdg r
   *
   * | PattArgumentEqTerm r -> collect_eq_term sgn metas jdg r *)


(** Given a mapping of de Bruijn indices [0, ..., k-1] to their values, convert
   them to a list. *)
let metas_to_list k metas =
  let rec fold lst = function
    | 0 -> Some lst
    | i ->
       let i = i - 1 in
       begin match MetaMap.find_opt i metas with
       | None -> None
       | Some x -> fold (x :: lst) i
       end
  in
  fold [] k

(** The [match_XYZ] functions match judgements against patterns, making sure
    to collect precisely [k] meta-variables. *)

(** Match type [t] against pattern [r] with meta-indices [0, ..., k-1]. *)
let match_is_type sgn t (r, k) =
  try
    let t = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
    metas_to_list k (collect_is_type sgn MetaMap.empty t r)
  with
    Match_fail -> None

(** Match term [e] against pattern [r] with meta-indices [0, ..., k-1]. *)
let match_is_term sgn e (r, k) =
  try
    let e = Nucleus.(abstract_not_abstract (JudgementIsTerm e)) in
    metas_to_list k (collect_is_term sgn MetaMap.empty e r)
  with
    Match_fail -> None

exception Form_fail

(** Is the given judgement abstraction an eta-expanded meta-variable? *)
let extract_meta metas abstr =
  let rec fold k = function

    | Nucleus_types.Arg_Abstract (_, abstr) -> fold (k+1) abstr

    | Nucleus_types.Arg_NotAbstract jdg ->
       (* check that given arguments are bound variables j, j-1, ..., 0 *)
       let rec check_es j = function

         | [] -> if j <> 0 then raise Form_fail

         | Nucleus_types.TermBoundVar i :: es ->
            if i = j-1 then check_es (j-1) es else raise Form_fail

         | Nucleus_types.(TermAtom _ | TermMeta _ | TermConvert _ | TermConstructor _) :: _ ->
            raise Form_fail

       in
       begin match jdg with

       | Nucleus_types.JudgementIsTerm e ->
          begin match e with
          | Nucleus_types.(TermMeta (MetaBound k, es)) ->
             check_es k es ;
             if Bound_set.mem k metas then
               metas, PattArgumentIsTerm (PattTermCheckMeta k)
             else
               let metas = Bound_set.add k metas in
               metas, PattArgumentIsTerm (PattTermAddMeta k)

          | Nucleus_types.(TermMeta (MetaFree _, _) | TermBoundVar _ | TermAtom _ |
                           TermConstructor _ | TermConvert _) ->
             raise Form_fail

          end

       | Nucleus_types.JudgementIsType t ->
          begin match t with
          | Nucleus_types.(TypeMeta (MetaBound k, es)) ->
             check_es k es ;
             if Bound_set.mem k metas then
               metas, PattArgumentIsType (PattTypeCheckMeta k)
             else
               let metas = Bound_set.add k metas in
               metas, PattArgumentIsType (PattTypeAddMeta k)

          | Nucleus_types.(TypeMeta (MetaFree _, _) | TypeConstructor _) ->
             raise Form_fail
          end

       | Nucleus_types.(JudgementEqType _ | JudgementEqTerm _) ->
          raise Form_fail
       end
  in
  fold 0 abstr


(** The [form_XYZ] functions form a pattern from a given judgement. They return the set of
    bound meta-variables that were encountered and turned into pattern variables. *)

let rec form_is_term metas e =
  match e with
  | Nucleus_types.TermBoundVar _ ->
     assert false

  | Nucleus_types.(TermAtom {atom_nonce=n; _}) ->
     metas, PattTermAtom n

  | Nucleus_types.TermConstructor (c, args) ->
     let metas, args = form_arguments metas args in
     metas, PattTermConstructor (c, args)

  | Nucleus_types.(TermMeta (MetaBound i, [])) ->
     if Bound_set.mem i metas then
       metas, PattTermCheckMeta i
     else
       let metas = Bound_set.add i metas in
       metas, PattTermAddMeta i

  | Nucleus_types.(TermMeta (MetaFree mv, es)) ->
     let rec fold metas es_out = function

       | [] ->
          let es_out = List.rev es_out in
          metas, PattTermFreeMeta (mv.meta_nonce, es_out)

       | e :: es ->
          let metas, e = form_is_term metas e in
          fold metas (e :: es_out) es
     in
     fold metas [] es

  | Nucleus_types.(TermMeta (MetaBound _, _::_))
  | Nucleus_types.TermConvert _ ->
     raise Form_fail

and form_is_type metas = function

  | Nucleus_types.TypeConstructor (c, args) ->
     let metas, args = form_arguments metas args in
     metas, PattTypeConstructor (c, args)

  | Nucleus_types.(TypeMeta (MetaBound i, [])) ->
     if Bound_set.mem i metas then
       metas, PattTypeCheckMeta i
     else
       let metas = Bound_set.add i metas in
       metas, PattTypeAddMeta i

  | Nucleus_types.(TypeMeta (MetaFree mv, es)) ->
     let rec fold metas es_out = function

       | [] ->
          let es_out = List.rev es_out in
          metas, PattTypeFreeMeta (mv.meta_nonce, es_out)

       | e :: es ->
          let metas, e = form_is_term metas e in
          fold metas (e :: es_out) es
     in
     fold metas [] es

  | Nucleus_types.(TypeMeta (MetaBound _, _::_)) ->
     raise Form_fail

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
        metas, PattArgumentIsTerm e

     | Nucleus_types.JudgementIsType t ->
        let metas, t = form_is_type metas t in
        metas, PattArgumentIsType t

     | Nucleus_types.JudgementEqType _
     | Nucleus_types.JudgementEqTerm _ ->
        (* For the time being we don't support equality arguments.
           It's not entirely clear how we should treat them. *)
        raise Form_fail
     end

  | Nucleus_types.Arg_Abstract _ as abstr ->
     (* Is this an eta-expanded meta-variable? *)
     extract_meta metas abstr

(** Check that the given set of integers contains
    precisely the numbers 0, 1, ..., k-1 *)
let is_range s k =
  let rec scan = function
    | 0 -> true
    | k -> Bound_set.mem (k-1) s && scan (k-1)
  in
  Bound_set.cardinal s = k && scan k

(** Construct a pattern [p] from type [t], and verify that the pattern captures exactly
   the bound meta-variables [0, ..., k-1]. Return the pair [(p, k)] to be used as part of
   a beta or extensionality rule. *)
let make_is_type sgn k t =
  try
    let metas, patt = form_is_type Bound_set.empty t in
    if is_range metas k then
      Some (patt, k)
    else
      None
  with
  | Form_fail -> None

(** Construct a pattern [p] from term [e], and verify that the pattern captures exactly
   the bound meta-variables [0, ..., k-1]. Return the pair [(p, k)] to be used as part of
   a beta or extensionality rule. *)
let make_is_term sgn k e =
  try
    let metas, patt = form_is_term Bound_set.empty e in
    if is_range metas k then
      Some (patt, k)
    else
      None
  with
  | Form_fail -> None
