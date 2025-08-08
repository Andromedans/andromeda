(** Shifting of bound meta-variables. *)

open Nucleus_types

let rec is_type k = function
  | TypeConstructor (c, args) ->
     let args = arguments k args in
     TypeConstructor (c, args)

  | TypeMeta (mv, args) ->
     let args = term_arguments k args
     and mv = meta k mv in
     TypeMeta (mv, args)

and is_term k = function

  | (TermBoundVar _ | TermAtom _) as e ->
     e (* no bound meta-variables here *)

  | TermMeta (mv, args) ->
     let args = term_arguments k args
     and mv = meta k mv in
     TermMeta (mv, args)

  | TermConstructor (c, args) ->
     let args = arguments k args in
     TermConstructor (c, args)

  | TermConvert (e, asmp, t) ->
     let e = is_term k e
     and asmp = Assumption.shift_meta k asmp
     and t = is_type k t in
     (* does not create a doubly nested [TermConvert] because original input does not either *)
     TermConvert (e, asmp, t)

(* metas can't refer to bound variables, so shifting does not affect them *)
and meta k = function
  | MetaFree _ as mv -> mv
  | MetaBound j -> MetaBound (j + k)

and eq_type k (EqType (asmp, t1, t2)) =
  let asmp = Assumption.shift_meta k asmp
  and t1 = is_type k t1
  and t2 = is_type k t2 in
  EqType (asmp, t1, t2)

and eq_term k (EqTerm (asmp, e1, e2, t)) =
  let asmp = Assumption.shift_meta k asmp
  and e1 = is_term k e1
  and e2 = is_term k e2
  and t = is_type k t in
  EqTerm (asmp, e1, e2, t)

and abstraction
  : 'a . (int -> 'a -> 'a) ->
         int -> 'a abstraction -> 'a abstraction
  = fun shift_u k -> function
  | NotAbstract u ->
     let u = shift_u k u
     in NotAbstract u

  | Abstract (x, t, abstr) ->
     let t = is_type k t
     and abstr = abstraction shift_u k abstr
     in Abstract (x, t, abstr)

and term_arguments k args =
  List.map (is_term k) args

and argument k = function
  | Arg_NotAbstract jdg -> Arg_NotAbstract (judgement k jdg)
  | Arg_Abstract (x, arg) -> Arg_Abstract (x, argument k arg)

and arguments k args =
  List.map (argument k) args

and judgement k = function
   | JudgementIsType t -> JudgementIsType (is_type k t)

   | JudgementIsTerm e -> JudgementIsTerm (is_term k e)

   | JudgementEqType eq -> JudgementEqType (eq_type k eq)

   | JudgementEqTerm eq -> JudgementEqTerm (eq_term k eq)
