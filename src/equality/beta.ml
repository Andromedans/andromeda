(** A β-derivation has the form

    derive P₁ ... Pᵢ  -> e₁ ≡ e₂ : A

  where:

  - the head meta-variable of each premise appears in e₁, uninstantiated (actually
    fully η-expanded), so that the premises can be read off e₁

  For example, the β-rule for functions is:

     rule Π_β (A type) ({x:A} B type) (a : A) ({x:A} e : B{x}) :
       app A B (λ A B e) a ≡ e{a} : B{a}

  For example, the β-rule for projections are:

     rule Σ_β₁ (A type) ({x : A} B type) (a : A) (b : B{a}) :
       π₁ A B (pair A B a b) == a : A

  Funky rule:

     rule Funky (x : unit) x == tt : unit


*)

(** A type β-rule has the form

    rule R P₁ ... Pᵢ  A ≡ B

  where:

  - the premises P₁ ... Pᵢ are term and type premises (no equations)

  - the head meta-variable of each premise appears in A, uninstantiated, so that
    the premises can be read off e₁
*)

(** Types describing patterns that we can match against. These are simple and do not
    bother matching anything under an abstraction. *)

type is_type =
  | IsTypeAddMeta of int
  | IsTypeCheckMeta of int
  | IsTypeConstructor of Ident.t * argument list

and is_term =
  | IsTermAddMeta of int
  | IsTermCheckMeta of int
  | IsTermConstructor of Ident.t * argument list
  | IsTermAtom of Nucleus.is_atom

and argument =
  | ArgumentIsType of is_type
  | ArgumentIsTerm of is_term
  | ArgumentEqType
  | ArgumentEqTerm

exception Match_fail

module MetaMap =
  Map.Make
    (struct
      type t = int
      let compare = Pervasives.compare
    end)

let add_meta = MetaMap.add

let check_meta k abstr metas =
  let abstr' = MetaMap.find k metas in
  if not (Nucleus.alpha_equal_abstraction Nucleus.alpha_equal_judgement abstr abstr') then
    raise Match_fail

(** Match a TT term against a matcher, read off the meta-variables. *)

let rec collect_is_type sgn metas abstr = function

  | IsTypeAddMeta k ->
     add_meta k abstr metas

  | IsTypeCheckMeta k ->
     check_meta k abstr metas ;
     metas

  | IsTypeConstructor (c, args) ->
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

and collect_is_term sgn metas abstr = function

  | IsTermAddMeta k ->
     add_meta k abstr metas

  | IsTermCheckMeta k ->
     check_meta k abstr metas ;
     metas

  | IsTermConstructor (c, args) ->
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

  | IsTermAtom atm ->
     begin match Nucleus.as_not_abstract abstr with
       | None -> raise Match_fail
       | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
          raise Match_fail

       | Some (Nucleus.JudgementIsTerm e) ->
          let rec fold e =
            match Nucleus.invert_is_term sgn e with
            | Nucleus.Stump_TermAtom atm' ->
               if Nucleus.alpha_equal_atom atm atm' then
                 metas
               else
                 raise Match_fail
            | Nucleus.Stump_TermConvert (e, _) -> fold e
            | Nucleus.(Stump_TermConstructor _ | Stump_TermMeta _) ->
               raise Match_fail
          in
          fold e
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

  | ArgumentEqType -> metas

  | ArgumentEqTerm -> metas


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

(** Form a pattern from the given rule term [e], abstracting over the given
    meta-variables. *)
let rec form_is_term sgn metas e =
  match e with
  | Nucleus.Rule. atm -> IsTermAtom atm

  | Nucleus.Stump_TermConstructor (c, args) ->
     let args = form_arguments sgn metas args in
     IsTermConstructor (c, args)

  | Nucleus.Stump_TermMeta (i, []) ->
     if 0 <= i && i < k then
       IsTermAddMeta i
     else
       raise Form_fail

  | Nucleus.Stump_TermConvert (e, _) -> form_is_term sgn metas e

and form_arguments sgn metas = function
  | [] -> metas
  | arg :: args ->
     let metas = form_argument sgn meta arg in
     let metas = form_arguments sgn metas args in
     metas

and form_argument sgn metas arg = (??)
