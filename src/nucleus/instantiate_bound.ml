(** Instantiate *)

open Nucleus_types

(* [instantiate e0 ?lvl t] replaces the bound variable [lvl] in [t] by [e0].
   We assume that [lvl] is the highest de Bruijn index occuring in [t]. *)

let rec is_type e0 ?(lvl=0) = function
  | TypeMeta (mv, args) ->
     let mv = meta e0 ~lvl mv
     and args = term_arguments e0 ~lvl args in
     TypeMeta (mv, args)

  | TypeConstructor (c, args) ->
     let args = arguments e0 ~lvl args in
     TypeConstructor (c, args)

and is_term e0 ?(lvl=0) = function

    | TermBoundVar k as e ->
       if k < lvl then
         e
       else begin
         (* We should only ever instantiate the highest occurring bound variable. *)
         assert (k = lvl) ;
         Shift.is_term ~lvl:0 lvl e0
       end

    | TermAtom _ as e -> e (* there are no bound variables in an atom type *)

    | TermMeta (mv, args) ->
       let mv = meta e0 ~lvl mv
       and args = term_arguments e0 ~lvl args in
       TermMeta (mv, args)

    | TermConstructor (c, args) ->
       let args = arguments e0 ~lvl args in
       TermConstructor (c, args)

    | TermConvert (e, asmp, t) ->
       let e = is_term e0 ~lvl e
       and asmp = assumptions e0 ~lvl asmp
       and t = is_type e0 ~lvl t in
       TermConvert (e, asmp, t)

(* there are no bound variables in the type of a meta *)
and meta e0 ?(lvl=0) mv = mv

and eq_type e0 ?(lvl=0) (EqType (asmp, t1, t2)) =
  let asmp = assumptions e0 ~lvl asmp
  and t1 = is_type e0 ~lvl t1
  and t2 = is_type e0 ~lvl t2 in
  EqType (asmp, t1, t2)

and eq_term e0 ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  let asmp = assumptions e0 ~lvl asmp
  and e1 = is_term e0 ~lvl e1
  and e2 = is_term e0 ~lvl e2
  and t = is_type e0 ~lvl t in
  EqTerm (asmp, e1, e2, t)

and assumptions e0 ?(lvl=0) asmp =
  let asmp0 = Collect_assumptions.is_term ~lvl e0 in
  Assumption.instantiate_bound ~lvl asmp0 asmp

and abstraction
  : 'a .(is_term -> ?lvl:bound -> 'a -> 'a) ->
        is_term -> ?lvl:bound -> 'a abstraction -> 'a abstraction
  = fun inst_v e0 ?(lvl=0) ->
  function
  | NotAbstract v ->
     let v = inst_v e0 ~lvl v in
     NotAbstract v

  | Abstract (x, u, abstr) ->
     let u = is_type e0 ~lvl u
     and abstr = abstraction inst_v e0 ~lvl:(lvl+1) abstr
     in
     Abstract (x, u, abstr)

and argument e0 ~lvl = function
  | Arg_NotAbstract jdg -> Arg_NotAbstract (judgement e0 ~lvl jdg)
  | Arg_Abstract (x, arg) -> Arg_Abstract (x, argument e0 ~lvl:(lvl+1) arg)

and arguments e0 ~lvl args =
  List.map (argument e0 ~lvl) args

and term_arguments e0 ~lvl args =
  List.map (is_term e0 ~lvl) args

and judgement e0 ?(lvl=0) = function

    | JudgementIsType t ->
       JudgementIsType (is_type e0 ~lvl t)

    | JudgementIsTerm e ->
       JudgementIsTerm (is_term e0 ~lvl e)

    | JudgementEqType asmp ->
       JudgementEqType (eq_type e0 ~lvl asmp)

    | JudgementEqTerm asmp ->
       JudgementEqTerm (eq_term e0 ~lvl asmp)

let is_type_boundary _ ?(lvl=0) () = ()

let is_term_boundary e0 ?(lvl=0) t =
  is_type e0 ~lvl t

let eq_type_boundary e0 ?(lvl=0) (t1, t2) =
  let t1 = is_type e0 ~lvl t1
  and t2 = is_type e0 ~lvl t2 in
  (t1, t2)

let eq_term_boundary e0 ?(lvl=0) (e1, e2, t) =
  let e1 = is_term e0 ~lvl e1
  and e2 = is_term e0 ~lvl e2
  and t = is_type e0 ~lvl t in
  (e1, e2, t)

let boundary e0 ?(lvl=0) = function
  | BoundaryIsType () ->
     BoundaryIsType (is_type_boundary e0 ~lvl ())

  | BoundaryIsTerm t ->
     BoundaryIsTerm (is_term_boundary e0 ~lvl t)

  | BoundaryEqType (t1, t2) ->
     BoundaryEqType (eq_type_boundary e0 ~lvl (t1, t2))

  | BoundaryEqTerm (e1, e2, t) ->
     BoundaryEqTerm (eq_term_boundary e0 ~lvl (e1, e2, t))

(* [instantiate_fully ?lvl es t] replaces bound variables [k] for
   [lvl] <= [k] < [List.length es] with [List.nth (k - lvl) es] in [t]. Bound
   variables in [t] should thus be below [lvl + length es].

   For instance, if [lvl] = 0, the first [length es] bound variables in [t] get
   replaced by [es]. *)

let rec is_type_fully ?(lvl=0) es = function
  | TypeMeta (mv, args) ->
     let args = term_arguments_fully ~lvl es args in
     (* there are no bound variables in the type of a meta *)
     TypeMeta (mv, args)
  | TypeConstructor (c, args) ->
     let args = arguments_fully ~lvl es args in
     TypeConstructor (c, args)

and is_term_fully ?(lvl=0) es = function

  | (TermBoundVar k) as e ->
     if k < lvl
     then e
     else
       let e = try List.nth es (k - lvl)
         with Failure _ -> Error.raise InvalidInstantiation
       in
       Shift.is_term ~lvl:0 lvl e

  | TermAtom _ as e -> e (* there are no bound variables in an atom type *)

  | TermMeta (mv, args) ->
     let args = term_arguments_fully ~lvl es args in
     (* there are no bound variables in the type of a meta *)
     TermMeta (mv, args)

  | TermConstructor (c, args) ->
     let args = arguments_fully ~lvl es args in
     TermConstructor (c, args)

  | TermConvert (e, asmp, t) ->
     let e = is_term_fully ~lvl es e
     and asmp = assumptions_fully ~lvl es asmp
     and t = is_type_fully ~lvl es t
     in TermConvert (e, asmp, t)

and eq_type_fully ?(lvl=0) es (EqType (asmp, t1, t2)) =
  let asmp = assumptions_fully ~lvl es asmp
  and t1 = is_type_fully ~lvl es t1
  and t2 = is_type_fully ~lvl es t2
  in EqType (asmp, t1, t2)

and eq_term_fully ?(lvl=0) es (EqTerm (asmp, e1, e2, t)) =
  let asmp = assumptions_fully ~lvl es asmp
  and e1 = is_term_fully ~lvl es e1
  and e2 = is_term_fully ~lvl es e2
  and t = is_type_fully ~lvl es t
  in EqTerm (asmp, e1, e2, t)

and assumptions_fully ~lvl es asmp =
  let asmps = List.map (Collect_assumptions.is_term ~lvl) es in
  Assumption.fully_instantiate_bound asmps ~lvl asmp

and abstraction_fully
  : 'a . (?lvl:int -> is_term list -> 'a -> 'a) ->
         ?lvl:int -> is_term list -> 'a abstraction -> 'a abstraction
  = fun inst_u ?(lvl=0) es -> function

  | NotAbstract u ->
     let u = inst_u ~lvl es u in
     NotAbstract u

  | Abstract (x, t, abstr) ->
     let t = is_type_fully ~lvl es t
     and abstr = abstraction_fully inst_u ~lvl:(lvl+1) es abstr
     in Abstract (x, t, abstr)

and argument_fully ?(lvl=0) es = function
  | Arg_NotAbstract jdg -> Arg_NotAbstract (judgement_fully ~lvl es jdg)
  | Arg_Abstract (x, arg) -> Arg_Abstract (x, argument_fully ~lvl:(lvl+1) es arg)

and arguments_fully ?(lvl=0) es args =
  List.map (argument_fully ~lvl es) args

and term_arguments_fully ?(lvl=0) es args =
  List.map (is_term_fully ~lvl es) args

and judgement_fully ?(lvl=0) es = function
  | JudgementIsType t ->
     JudgementIsType (is_type_fully ~lvl es t)

  | JudgementIsTerm e ->
     JudgementIsTerm (is_term_fully ~lvl es e)

  | JudgementEqType eq ->
     JudgementEqType (eq_type_fully ~lvl es eq)

  | JudgementEqTerm eq ->
     JudgementEqTerm (eq_term_fully ~lvl es eq)

let is_type_boundary_fully _ ?(lvl=0) () = ()

let is_term_boundary_fully ?(lvl=0) es t =
  is_type_fully ~lvl es t

let eq_type_boundary_fully ?(lvl=0) es (t1, t2) =
  let t1 = is_type_fully ~lvl es t1
  and t2 = is_type_fully ~lvl es t2 in
  (t1, t2)

let eq_term_boundary_fully ?(lvl=0) es (e1, e2, t) =
  let e1 = is_term_fully ~lvl es e1
  and e2 = is_term_fully ~lvl es e2
  and t = is_type_fully ~lvl es t in
  (e1, e2, t)

let boundary_fully ?(lvl=0) es = function
  | BoundaryIsType () ->
     BoundaryIsType (is_type_boundary_fully ~lvl es ())

  | BoundaryIsTerm t ->
     BoundaryIsTerm (is_term_boundary_fully ~lvl es t)

  | BoundaryEqType (t1, t2) ->
     BoundaryEqType (eq_type_boundary_fully ~lvl es (t1, t2))

  | BoundaryEqTerm (e1, e2, t) ->
     BoundaryEqTerm (eq_term_boundary_fully ~lvl es (e1, e2, t))
