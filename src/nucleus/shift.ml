(** Shifting of bound variables *)

open Nucleus_types

let rec is_type ~lvl k = function
  | TypeConstructor (c, args) ->
     let args = arguments ~lvl k args in
     TypeConstructor (c, args)

  | TypeMeta (mv, args) ->
     let args = term_arguments ~lvl k args
     and mv = ty_meta ~lvl k mv in
     TypeMeta (mv, args)

and is_term ~lvl k = function

  | TermBound j as e ->
     if j < lvl then
       e
     else
       TermBound (j + k)

  | TermAtom _ as e ->
     e (* no bound variables in atoms *)

  | TermMeta (mv, args) ->
     let args = term_arguments ~lvl k args
     and mv = term_meta ~lvl k mv in
     TermMeta (mv, args)

  | TermConstructor (c, args) ->
     let args = arguments ~lvl k args in
     TermConstructor (c, args)

  | TermConvert (e, asmp, t) ->
     let e = is_term ~lvl k e
     and asmp = Assumption.shift ~lvl k asmp
     and t = is_type ~lvl k t in
     TermConvert (e, asmp, t)

(* metas can't refer to bound variables, so shifting does not affect them *)
and ty_meta ~lvl k mv = mv

(* metas can't refer to bound variables, so shifting does not affect them *)
and term_meta ~lvl k mv = mv

and eq_type ~lvl k (EqType (asmp, t1, t2)) =
  let asmp = Assumption.shift ~lvl k asmp
  and t1 = is_type ~lvl k t1
  and t2 = is_type ~lvl k t2 in
  EqType (asmp, t1, t2)

and eq_term ~lvl k (EqTerm (asmp, e1, e2, t)) =
  let asmp = Assumption.shift ~lvl k asmp
  and e1 = is_term ~lvl k e1
  and e2 = is_term ~lvl k e2
  and t = is_type ~lvl k t in
  EqTerm (asmp, e1, e2, t)

and abstraction
  : 'a . (lvl:bound -> int -> 'a -> 'a) ->
         lvl:bound -> int -> 'a abstraction -> 'a abstraction
  = fun shift_u ~lvl k -> function
  | NotAbstract u ->
     let u = shift_u ~lvl k u
     in NotAbstract u

  | Abstract ({atom_nonce=x; atom_type=t}, abstr) ->
     let t = is_type ~lvl k t
     and abstr = abstraction shift_u ~lvl:(lvl+1) k abstr
     in Abstract ({atom_nonce=x; atom_type=t}, abstr)

and term_arguments ~lvl k args =
  List.map (is_term ~lvl k) args

and arguments ~lvl k args =
  List.map (abstraction argument ~lvl k) args

and argument ~lvl k = function
   | JudgementIsType t -> JudgementIsType (is_type ~lvl k t)

   | JudgementIsTerm e -> JudgementIsTerm (is_term ~lvl k e)

   | JudgementEqType eq -> JudgementEqType (eq_type ~lvl k eq)

   | JudgementEqTerm eq -> JudgementEqTerm (eq_term ~lvl k eq)
