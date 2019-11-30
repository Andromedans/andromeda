(** We support user-provided beta-rules and extensionality-rules (these are
  inter-derivable with η-rules, but have a more convenient form)

  A term extensionality rule has the form

      rule R P₁ ... Pᵢ A (x : A) (y : A) Q₁ ... Qⱼ x ≡ y : A

  where:

  - the premises P₁ ... Pᵢ are type and term premises

  - the premises Q₁ ... Qⱼ are term equation premises

  - the head meta-variables of the premises P₁ ... Pᵢ appear in A,
    uninstantiated, so that the premises P₁ ... Pᵢ can be read off A.

  For example, the extensionality rule for functions is

      rule Π_ext (A type) ({x:A} B type) (f : Π A B) (g : Π A B)
                 ({x : A} app A B f x ≡ app A B g x as ξ)
                 f ≡ g : Π A B

  For example, the extensionality rule for the unit type is

      rule unit_ext (x : unit) (y : unit) x ≡ y : unit

  For example, the extensionality rule for dependent sums is

      rule Σ_ext (A type) ({x:A} B type) (p : Σ A B) (q : Σ A B)
                 (π₁ A B p ≡ π₁ A B q : A as ξ₁)
                 (π₂ A B p ≡ π₂ A B q : B{π₁ A B p} as ξ₂) p ≡ q
                 : Σ A B

  A term β-rule has the form

      rule R P₁ ... Pᵢ e₁ ≡ e₂ : A

  where:

  - the head meta-variable of each premise appears in e₁, uninstantiated
    (actually fully η-expanded), so that the premises can be read off e₁

  - e1 is an application of a symbol or a meta-variable (not a variable)

  For example, the β-rule for functions is:

     rule Π_β (A type) ({x:A} B type) (a : A) ({x:A} e : B{x})
              : app A B (λ A B e) a ≡ e{a} : B{a}

  For example, the β-rule for projections are:

     rule Σ_β₁ (A type) ({x : A} B type) (a : A) (b : B{a})
              : π₁ A B (pair A B a b) == a : A

  A type β-rule has the form

     rule R P₁ ... Pᵢ  A ≡ B

  where:

  - the premises P₁ ... Pᵢ are term and type premises (no equations)

  - the head meta-variable of each premise appears in A, uninstantiated, so that
    the premises can be read off e₁
*)

(** Types describing patterns that we can match against. These are simple and do not
    bother matching anything under an abstraction. *)

type is_type =
  | TypeAddMeta of int
  | TypeCheckMeta of int
  | TypeConstructor of Ident.t * argument list
  | TypeFreeMeta of Nonce.t * is_term list

and is_term =
  | TermAddMeta of int
  | TermCheckMeta of int
  | TermConstructor of Ident.t * argument list
  | TermFreeMeta of Nonce.t * is_term list
  | TermAtom of Nonce.t

and eq_type =
  | EqTypeAddMeta of int
  | EqTypeCheckMeta of int
  | EqTypeBoundary of is_type * is_type

and eq_term =
  | EqTermAddMeta of int
  | EqTermCheckMeta of int
  | EqTermBoundary of is_term * is_term * is_type

and argument =
  | ArgumentIsType of is_type
  | ArgumentIsTerm of is_term
  | ArgumentEqType of eq_type
  | ArgumentEqTerm of eq_term

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

(** Match an abstraction against a matcher, and collect the values of meta-variables when doing so. *)

let rec collect_is_type sgn metas abstr = function

  | TypeAddMeta k ->
     add_meta k abstr metas

  | TypeCheckMeta k ->
     check_meta k abstr metas ;
     metas

  | TypeConstructor (c, args) ->
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

  | TypeFreeMeta (n, es) ->
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

  | TermAddMeta k ->
     add_meta k abstr metas

  | TermCheckMeta k ->
     check_meta k abstr metas ;
     metas

  | TermConstructor (c, args) ->
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

  | TermAtom n ->
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

  | TermFreeMeta (n, es) ->
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

and collect_eq_type sgn metas abstr = function

  | EqTypeAddMeta k ->
     add_meta k abstr metas

  | EqTypeCheckMeta k ->
     check_meta k abstr metas ;
     metas

  | EqTypeBoundary (r1, r2) ->
     begin match Nucleus.as_not_abstract abstr with

     | None -> raise Match_fail

     | Some (Nucleus.JudgementEqType eq) ->
        let Nucleus.Stump_EqType (_asmp, t1, t2) = Nucleus.invert_eq_type eq in
        let abstr1 = Nucleus.(abstract_not_abstract (JudgementIsType t1))
        and abstr2 = Nucleus.(abstract_not_abstract (JudgementIsType t2)) in
        let metas = collect_is_type sgn metas abstr1 r1 in
        let metas = collect_is_type sgn metas abstr2 r2 in
        metas

     | Some Nucleus.(JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _) ->
        raise Match_fail
     end

and collect_eq_term sgn metas abstr = function

  | EqTermAddMeta k ->
     add_meta k abstr metas

  | EqTermCheckMeta k ->
     check_meta k abstr metas ;
     metas

  | EqTermBoundary (r1, r2, rt) ->
     begin match Nucleus.as_not_abstract abstr with

     | None -> raise Match_fail

     | Some (Nucleus.JudgementEqTerm eq) ->
        let Nucleus.Stump_EqTerm (_asmp, e1, e2, t) = Nucleus.invert_eq_term eq in
        let abstr1 = Nucleus.(abstract_not_abstract (JudgementIsTerm e1))
        and abstr2 = Nucleus.(abstract_not_abstract (JudgementIsTerm e2))
        and abstrt = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
        let metas = collect_is_type sgn metas abstrt rt in
        let metas = collect_is_term sgn metas abstr1 r1 in
        let metas = collect_is_term sgn metas abstr2 r2 in
        metas

     | Some Nucleus.(JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _) ->
        raise Match_fail
     end

and collect_arguments sgn metas args_e args_r =
  match args_e, args_r with
  | [], [] -> metas

  | e :: args_e, r :: args_r ->
     let metas = collect_argument sgn metas e r in
     collect_arguments sgn metas args_e args_r

  | [], _::_ | _::_, [] ->
     raise Match_fail

and collect_argument sgn metas jdg = function

  | ArgumentIsType r -> collect_is_type sgn metas jdg r

  | ArgumentIsTerm r -> collect_is_term sgn metas jdg r

  | ArgumentEqType r -> collect_eq_type sgn metas jdg r

  | ArgumentEqTerm r -> collect_eq_term sgn metas jdg r


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

(** Match term [e] against pattern [r] with meta-indices [0, ..., k-1]. *)
let match_is_term sgn e k r =
  try
    metas_to_list k (collect_is_term sgn MetaMap.empty e r)
  with
    Match_fail -> None

(** Match term [e] against pattern [r] with meta-indices [0, ..., k-1]. *)
let match_is_type sgn e k r =
  try
    metas_to_list k (collect_is_type sgn MetaMap.empty e r)
  with
    Match_fail -> None

exception Form_fail

(** Is the given judgement abstraction an eta-expanded meta-variable? *)
let extract_meta metas abstr =
  let rec fold k = function

    | Nucleus_types.Arg_Abstract (_, abstr) -> fold (k+1) abstr

    | Nucleus_types.Arg_NotAbstract jdg ->
       (* check tht given arguments are bound variables j, j-1, ..., 0 *)
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
          | Nucleus_types.TermMeta (MetaBound k, es) ->
             check_es k es ;
             if Bound_set.mem k metas then
               metas, ArgumentIsTerm (TermCheckMeta k)
             else
               let metas = Bound_set.add k metas in
               metas, ArgumentIsTerm (TermAddMeta k)

          | Nucleus_types.(TermMeta (MetaFree _, _) | TermBoundVar _ | TermAtom _ |
                           TermConstructor _ | TermConvert _) ->
             raise Form_fail

          end

       | Nucleus_types.JudgementIsType t ->
          begin match t with
          | Nucleus_types.TypeMeta (MetaBound k, es) ->
             check_es k es ;
             if Bound_set.mem k metas then
               metas, ArgumentIsType (TypeCheckMeta k)
             else
               let metas = Bound_set.add k metas in
               metas, ArgumentIsType (TypeAddMeta k)

          | Nucleus_types.(TypeMeta (MetaFree _, _) | TypeConstructor _) ->
             raise Form_fail
          end

       | Nucleus_types.(JudgementEqType _ | JudgementEqTerm _) ->
          raise Form_fail
       end
  in
  fold 0 abstr


(** Form a rewrite pattern from the given term [e], abstracting over the given
   bound meta-variables. *)
let rec form_is_term metas e =
  match e with
  | Nucleus_types.TermBoundVar _ ->
     assert false

  | Nucleus_types.TermAtom atm ->
     metas, TermAtom atm.atom_nonce

  | Nucleus_types.TermConstructor (c, args) ->
     let metas, args = form_arguments metas args in
     metas, TermConstructor (c, args)

  | Nucleus_types.TermMeta (MetaBound i, []) ->
     if Bound_set.mem i metas then
       metas, TermCheckMeta i
     else
       let metas = Bound_set.add i metas in
       metas, TermAddMeta i

  | Nucleus_types.TermMeta (MetaFree mv, es) ->
     let rec fold metas es_out = function

       | [] ->
          let es_out = List.rev es_out in
          metas, TermFreeMeta (mv.meta_nonce, es_out)

       | e :: es ->
          let metas, e = form_is_term metas e in
          fold metas (e :: es_out) es
     in
     fold metas [] es

  | Nucleus_types.TermMeta (MetaBound _, _::_)
  | Nucleus_types.TermConvert _ ->
     raise Form_fail

and form_is_type metas = function

  | Nucleus_types.TypeConstructor (c, args) ->
     let metas, args = form_arguments metas args in
     metas, TypeConstructor (c, args)

  | Nucleus_types.TypeMeta (MetaBound i, []) ->
     if Bound_set.mem i metas then
       metas, TypeCheckMeta i
     else
       let metas = Bound_set.add i metas in
       metas, TypeAddMeta i

  | Nucleus_types.TypeMeta (MetaFree mv, es) ->
     let rec fold metas es_out = function

       | [] ->
          let es_out = List.rev es_out in
          metas, TypeFreeMeta (mv.meta_nonce, es_out)

       | e :: es ->
          let metas, e = form_is_term metas e in
          fold metas (e :: es_out) es
     in
     fold metas [] es

  | Nucleus_types.TypeMeta (MetaBound _, _::_) ->
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
        metas, ArgumentIsTerm e

     | Nucleus_types.JudgementIsType t ->
        let metas, t = form_is_type metas t in
        metas, ArgumentIsType t

     | Nucleus_types.JudgementEqType _
     | Nucleus_types.JudgementEqTerm _ ->
        (* For the time being we don't support equality arguments.
           It's not entirely clear how we should treat them. *)
        raise Form_fail
     end

  | Nucleus_types.Arg_Abstract _ as abstr ->
     (** Check to see if this is an eta-expanded meta-variable. *)
     extract_meta metas abstr
