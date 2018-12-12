(** Shifting of bound variables *)

open Jdg_typedefs

let rec shift_term ~lvl k = function

  | TermAtom _ as e ->
     e (* no bound variables in atoms *)

  | TermBound j as e ->
     if j < lvl then
       e
     else
       TermBound (j + k)

  | TermConstructor (c, args) ->
     let args = shift_args ~lvl k args in
     TermConstructor (c, args)

  | TermMeta (mv, args) ->
     let args = shift_term_args ~lvl k args
     and mv = shift_term_meta ~lvl k mv in
     TermMeta (mv, args)

  | TermConvert (e, asmp, t) ->
     let e = shift_term ~lvl k e
     and asmp = Assumption.shift ~lvl k asmp
     and t = shift_type ~lvl k t in
     TermConvert (e, asmp, t)

(* metas can't refer to bound variables, so shifting does not affect them *)
and shift_term_meta ~lvl k mv =
  (* XXX delete me *)
  (* let {meta_name; meta_type} = mv in
   * let meta_type = shift_abstraction shift_type ~lvl k meta_type in
   * {meta_name; meta_type} *)
  mv

and shift_type ~lvl k = function
  | TypeConstructor (c, args) ->
     let args = shift_args ~lvl k args in
     TypeConstructor (c, args)

  | TypeMeta (mv, args) ->
     let args = shift_term_args ~lvl k args
     and mv = shift_type_meta ~lvl k mv in
     TypeMeta (mv, args)

(* metas can't refer to bound variables, so shifting does not affect them *)
and shift_type_meta ~lvl k mv =
  (* XXX delete me *)
  (* let {meta_name; meta_type} = mv in
   * let meta_type = shift_abstraction (fun ~lvl _k () -> ()) ~lvl k meta_type in
   * {meta_name; meta_type} *)
  mv

and shift_eq_type ~lvl k (EqType (asmp, t1, t2)) =
  let asmp = Assumption.shift ~lvl k asmp
  and t1 = shift_type ~lvl k t1
  and t2 = shift_type ~lvl k t2 in
  EqType (asmp, t1, t2)

and shift_eq_term ~lvl k (EqTerm (asmp, e1, e2, t)) =
  let asmp = Assumption.shift ~lvl k asmp
  and e1 = shift_term ~lvl k e1
  and e2 = shift_term ~lvl k e2
  and t = shift_type ~lvl k t in
  EqTerm (asmp, e1, e2, t)

and shift_term_args ~lvl k args =
  List.map (shift_term ~lvl k) args

and shift_args ~lvl k args =
  List.map (shift_arg ~lvl k) args

and shift_arg ~lvl k = function
   | ArgIsTerm abstr ->
      let abstr = shift_abstraction shift_term ~lvl k abstr in
      ArgIsTerm abstr

   | ArgIsType abstr ->
      let abstr = shift_abstraction shift_type ~lvl k abstr in
      ArgIsType abstr

   | ArgEqType abstr ->
      let abstr = shift_abstraction shift_eq_type ~lvl k abstr in
      ArgEqType abstr

   | ArgEqTerm abstr ->
      let abstr = shift_abstraction shift_eq_term ~lvl k abstr in
      ArgEqTerm abstr

and shift_abstraction
  : 'a . (lvl:bound -> int -> 'a -> 'a) ->
         lvl:bound -> int -> 'a abstraction -> 'a abstraction
  = fun shift_u ~lvl k -> function
  | NotAbstract u ->
     let u = shift_u ~lvl k u
     in NotAbstract u

  | Abstract (x, t, abstr) ->
     let t = shift_type ~lvl k t
     and abstr = shift_abstraction shift_u ~lvl:(lvl+1) k abstr
     in Abstract (x, t, abstr)

