(** Shifting of bound variables *)

open Jdg_typedefs

let rec term ~lvl k = function

  | TermAtom _ as e ->
     e (* no bound variables in atoms *)

  | TermBound j as e ->
     if j < lvl then
       e
     else
       TermBound (j + k)

  | TermConstructor (c, args) ->
     let args = arguments ~lvl k args in
     TermConstructor (c, args)

  | TermMeta (mv, args) ->
     let args = term_arguments ~lvl k args
     and mv = term_meta ~lvl k mv in
     TermMeta (mv, args)

  | TermConvert (e, asmp, t) ->
     let e = term ~lvl k e
     and asmp = Assumption.shift ~lvl k asmp
     and t = ty ~lvl k t in
     TermConvert (e, asmp, t)

(* metas can't refer to bound variables, so shifting does not affect them *)
and term_meta ~lvl k mv = mv

and ty ~lvl k = function
  | TypeConstructor (c, args) ->
     let args = arguments ~lvl k args in
     TypeConstructor (c, args)

  | TypeMeta (mv, args) ->
     let args = term_arguments ~lvl k args
     and mv = ty_meta ~lvl k mv in
     TypeMeta (mv, args)

(* metas can't refer to bound variables, so shifting does not affect them *)
and ty_meta ~lvl k mv = mv

and eq_type ~lvl k (EqType (asmp, t1, t2)) =
  let asmp = Assumption.shift ~lvl k asmp
  and t1 = ty ~lvl k t1
  and t2 = ty ~lvl k t2 in
  EqType (asmp, t1, t2)

and eq_term ~lvl k (EqTerm (asmp, e1, e2, t)) =
  let asmp = Assumption.shift ~lvl k asmp
  and e1 = term ~lvl k e1
  and e2 = term ~lvl k e2
  and t = ty ~lvl k t in
  EqTerm (asmp, e1, e2, t)

and term_arguments ~lvl k args =
  List.map (term ~lvl k) args

and arguments ~lvl k args =
  List.map (argument ~lvl k) args

and argument ~lvl k = function
   | ArgIsTerm abstr ->
      let abstr = abstraction term ~lvl k abstr in
      ArgIsTerm abstr

   | ArgIsType abstr ->
      let abstr = abstraction ty ~lvl k abstr in
      ArgIsType abstr

   | ArgEqType abstr ->
      let abstr = abstraction eq_type ~lvl k abstr in
      ArgEqType abstr

   | ArgEqTerm abstr ->
      let abstr = abstraction eq_term ~lvl k abstr in
      ArgEqTerm abstr

and abstraction
  : 'a . (lvl:bound -> int -> 'a -> 'a) ->
         lvl:bound -> int -> 'a abstraction -> 'a abstraction
  = fun shift_u ~lvl k -> function
  | NotAbstract u ->
     let u = shift_u ~lvl k u
     in NotAbstract u

  | Abstract (x, t, abstr) ->
     let t = ty ~lvl k t
     and abstr = abstraction shift_u ~lvl:(lvl+1) k abstr
     in Abstract (x, t, abstr)
