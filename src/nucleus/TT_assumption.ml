(** Manipulation of assumptions. *)
open Jdg_typedefs

(** The assumptions of a term [e] are the atoms and bound variables appearing in [e]. *)
let rec term ?(lvl=0) = function

  | TermAtom {atom_name=x; atom_type=t} ->
     Assumption.add_free x t (ty ~lvl t)

  | TermBound k ->
     if k < lvl then
       Assumption.empty
     else
       Assumption.singleton_bound (k - lvl)

  | TermConstructor (_, args) ->
     arguments ~lvl args

  | TermMeta (mv, args) ->
     let mv = term_meta ~lvl mv
     and args = term_args ~lvl args in
     Assumption.union mv args

  | TermConvert (e, asmp', t) ->
     Assumption.union
       asmp'
       (Assumption.union (term ~lvl e) (ty ~lvl t))

and term_meta ~lvl {meta_name; meta_type} =
  let asmp = abstraction ty ~lvl meta_type in
  Assumption.add_is_term_meta meta_name meta_type asmp

and ty ?(lvl=0) = function
  | TypeConstructor (_, args) -> arguments ~lvl args
  | TypeMeta (mv, args) ->
     let args = term_args ~lvl args
     and mv = type_meta ~lvl mv in
     Assumption.union mv args

and type_meta ~lvl {meta_name; meta_type} =
  let asmp =
    abstraction (fun ?lvl () -> Assumption.empty) ~lvl meta_type
  in
  Assumption.add_is_type_meta meta_name meta_type asmp

and term_args ~lvl ts =
  List.fold_left
    (fun acc arg -> Assumption.union acc (term ~lvl arg))
    Assumption.empty
    ts

and arguments ~lvl args =
  let rec fold asmp = function
    | [] -> asmp
    | arg :: args -> Assumption.union (argument ~lvl arg) (fold asmp args)
  in
  fold Assumption.empty args

and eq_type ?(lvl=0) (EqType (asmp, t1, t2)) =
  Assumption.union
    (assumptions ~lvl asmp)
    (Assumption.union (ty ~lvl t1) (ty ~lvl t2))

and eq_term ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  Assumption.union
    (Assumption.union (assumptions ~lvl asmp) (ty ~lvl t))
    (Assumption.union (term ~lvl e1) (term ~lvl e2))

and argument ?(lvl=0) = function
  | ArgIsType abstr -> abstraction ty ~lvl abstr
  | ArgIsTerm abstr -> abstraction term ~lvl abstr
  | ArgEqType abstr -> abstraction eq_type ~lvl abstr
  | ArgEqTerm abstr -> abstraction eq_term ~lvl abstr

and assumptions ?(lvl=0) asmp = Assumption.at_level ~lvl asmp

and abstraction
  : 'a . (?lvl:bound -> 'a -> assumption) ->
        ?lvl:bound -> 'a abstraction -> assumption
 = fun asmp_v ?(lvl=0) -> function
  | NotAbstract v -> asmp_v ~lvl v
  | Abstract (x, u, abstr) ->
     Assumption.union
       (ty ~lvl u)
       (abstraction asmp_v ~lvl:(lvl+1) abstr)

let arguments = arguments ~lvl:0
