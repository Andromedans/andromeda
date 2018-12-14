(** Instantiate *)

open Jdg_typedefs

(* [instantiate e0 ?lvl t] replaces the bound variable [lvl] in [t] by [e0].
   We assume that [lvl] is the highest de Bruijn index occuring in [t]. *)

let rec abstraction
  : 'a .(is_term -> ?lvl:bound -> 'a -> 'a) ->
        is_term -> ?lvl:bound -> 'a abstraction -> 'a abstraction
  = fun inst_v e0 ?(lvl=0) ->
  function
  | NotAbstract v ->
     let v = inst_v e0 ~lvl v in
     NotAbstract v

  | Abstract (x, u, abstr) ->
     let u = ty e0 ~lvl u
     and abstr = abstraction inst_v e0 ~lvl:(lvl+1) abstr
     in
     Abstract (x, u, abstr)

and term e0 ?(lvl=0) = function

    | TermAtom _ as e -> e (* there are no bound variables in an atom type *)

    | TermConstructor (c, args) ->
       let args = arguments e0 ~lvl args in
       TermConstructor (c, args)

    | TermMeta (mv, args) ->
       (* there are no bound variables in the type of a meta *)
       let args = term_arguments e0 ~lvl args in
       TermMeta (mv, args)

    | TermConvert (e, asmp, t) ->
       let e = term e0 ~lvl e
       and asmp = assumptions e0 ~lvl asmp
       and t = ty e0 ~lvl t in
       TermConvert (e, asmp, t)

    | TermBound k as e ->
       if k < lvl then
         e
       else begin
         (* We should only ever instantiate the highest occurring bound variable. *)
         assert (k = lvl) ;
         TT_shift.term ~lvl:0 lvl e0
       end

and ty e0 ?(lvl=0) = function
  | TypeConstructor (c, args) ->
     let args = arguments e0 ~lvl args in
     TypeConstructor (c, args)

  | TypeMeta (mv, args) ->
     (* there are no bound variables in the type of a meta *)
     let args = term_arguments e0 ~lvl args in
     TypeMeta (mv, args)

and arguments e0 ~lvl args =
  List.map (argument e0 ~lvl) args

and term_arguments e0 ~lvl args =
  List.map (term e0 ~lvl) args

and argument e0 ?(lvl=0) = function

    | ArgumentIsType t ->
       let t = abstraction ty e0 ~lvl t in
       ArgumentIsType t

    | ArgumentIsTerm e ->
       let e = abstraction term e0 ~lvl e in
       ArgumentIsTerm e

    | ArgumentEqType asmp ->
       let asmp = abstraction eq_type e0 ~lvl asmp in
       ArgumentEqType asmp

    | ArgumentEqTerm asmp ->
       let asmp = abstraction eq_term e0 ~lvl asmp in
       ArgumentEqTerm asmp

and eq_type e0 ?(lvl=0) (EqType (asmp, t1, t2)) =
  let asmp = assumptions e0 ~lvl asmp
  and t1 = ty e0 ~lvl t1
  and t2 = ty e0 ~lvl t2 in
  EqType (asmp, t1, t2)

and eq_term e0 ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  let asmp = assumptions e0 ~lvl asmp
  and e1 = term e0 ~lvl e1
  and e2 = term e0 ~lvl e2
  and t = ty e0 ~lvl t in
  EqTerm (asmp, e1, e2, t)

and assumptions e0 ?(lvl=0) asmp =
  let asmp0 = TT_assumption.term ~lvl e0 in
  Assumption.instantiate ~lvl asmp0 asmp


(* [instantiate_fully ?lvl es t] replaces bound variables [k] for
   [lvl] <= [k] < [List.length es] with [List.nth (k - lvl) es] in [t]. Bound
   variables in [t] should thus be below [lvl + length es].

   For instance, if [lvl] = 0, the first [length es] bound variables in [t] get
   replaced by [es]. *)

let rec type_fully ?(lvl=0) es = function
  | TypeConstructor (c, args) ->
     let args = args_fully ~lvl es args in
     TypeConstructor (c, args)
  | TypeMeta (mv, args) ->
     let args = term_args_fully ~lvl es args in
     (* there are no bound variables in the type of a meta *)
     TypeMeta (mv, args)

and term_fully ?(lvl=0) es = function

  | TermAtom _ as e -> e (* there are no bound variables in an atom type *)

  | (TermBound k) as e ->
     if k < lvl then
       e
     else
       let e =
         begin try
           List.nth es (k - lvl)
         with
           Failure _ -> TT_error.raise InvalidInstantiation
         end
       in
       TT_shift.term ~lvl:0 lvl e

  | TermConstructor (c, args) ->
     let args = args_fully ~lvl es args in
     TermConstructor (c, args)

  | TermMeta (mv, args) ->
     let args = term_args_fully ~lvl es args in
     (* there are no bound variables in the type of a meta *)
     TermMeta (mv, args)

  | TermConvert (e, asmp, t) ->
     let e = term_fully ~lvl es e
     and asmp = assumptions_fully ~lvl es asmp
     and t = type_fully ~lvl es t
     in TermConvert (e, asmp, t)

and eq_type_fully ?(lvl=0) es (EqType (asmp, t1, t2)) =
  let asmp = assumptions_fully ~lvl es asmp
  and t1 = type_fully ~lvl es t1
  and t2 = type_fully ~lvl es t2
  in EqType (asmp, t1, t2)

and eq_term_fully ?(lvl=0) es (EqTerm (asmp, e1, e2, t)) =
  let asmp = assumptions_fully ~lvl es asmp
  and e1 = term_fully ~lvl es e1
  and e2 = term_fully ~lvl es e2
  and t = type_fully ~lvl es t
  in EqTerm (asmp, e1, e2, t)


and assumptions_fully ~lvl es asmp =
  let asmps = List.map (TT_assumption.term ~lvl) es in
  Assumption.fully_instantiate asmps ~lvl asmp

and args_fully ?(lvl=0) es args =
  List.map (arg_fully ~lvl es) args

and term_args_fully ?(lvl=0) es args =
  List.map (term_fully ~lvl es) args

and arg_fully ?(lvl=0) es = function
  | ArgumentIsType abstr ->
     let abstr = abstraction_fully type_fully ~lvl es abstr in
     ArgumentIsType abstr

  | ArgumentIsTerm abstr ->
     let abstr = abstraction_fully term_fully ~lvl es abstr in
     ArgumentIsTerm abstr

  | ArgumentEqType abstr ->
     let abstr = abstraction_fully eq_type_fully ~lvl es abstr in
     ArgumentEqType abstr

  | ArgumentEqTerm abstr ->
     let abstr = abstraction_fully eq_term_fully ~lvl es abstr in
     ArgumentEqTerm abstr

and abstraction_fully
  : 'a . (?lvl:int -> is_term list -> 'a -> 'a) ->
         ?lvl:int -> is_term list -> 'a abstraction -> 'a abstraction
  = fun inst_u ?(lvl=0) es -> function

  | NotAbstract u ->
     let u = inst_u ~lvl es u in
     NotAbstract u

  | Abstract (x, t, abstr) ->
     let t = type_fully ~lvl es t
     and abstr = abstraction_fully inst_u ~lvl:(lvl+1) es abstr
     in Abstract (x, t, abstr)
