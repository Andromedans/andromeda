(****** Alpha equality ******)

open Jdg_typedefs

let equal_bound (i : bound) (j : bound) = (i = j)

let rec alpha_equal_term e1 e2 =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | TermAtom {atom_name=x;_}, TermAtom {atom_name=y;_} -> Name.eq_atom x y

    | TermBound i, TermBound j -> i = j

    | TermConstructor (c, args), TermConstructor (c', args') ->
       Name.eq_ident c c' && alpha_equal_args args args'

    | TermMeta (mv, args), TermMeta (mv', args') ->
       Name.eq_meta mv.meta_name mv'.meta_name && alpha_equal_term_args args args'

    | TermConvert (e1, _, _), TermConvert (e2, _, _) ->
       alpha_equal_term e1 e2

    | (TermAtom _ | TermBound _ | TermConstructor _  | TermMeta _  | TermConvert _), _ ->
      false
  end

and alpha_equal_type t1 t2 =
  match t1, t2 with

  | TypeConstructor (c, args), TypeConstructor (c', args') ->
     Name.eq_ident c c' && alpha_equal_args args args'

  | TypeMeta (mv, args), TypeMeta (mv', args') ->
     Name.eq_meta mv.meta_name mv'.meta_name && alpha_equal_term_args args args'

  | (TypeConstructor _ | TypeMeta _), _ -> false

and alpha_equal_term_args args args' =
  match args, args' with
  | [], [] -> true
  | arg::args, arg'::args' ->
     alpha_equal_term arg arg' && alpha_equal_term_args args args'
  | (_::_), []
  | [], (_::_) -> assert false

and alpha_equal_args args args' =
  match args, args' with

  | [], [] -> true

  | (ArgIsTerm e)::args, (ArgIsTerm e')::args' ->
     alpha_equal_abstraction alpha_equal_term e e' && alpha_equal_args args args'

  | (ArgIsType t)::args, (ArgIsType t')::args' ->
     alpha_equal_abstraction alpha_equal_type t t' && alpha_equal_args args args'

  | ArgEqType _ :: args, ArgEqType _ :: args' -> alpha_equal_args args args'

  | ArgEqTerm _ :: args, ArgEqTerm _ :: args' -> alpha_equal_args args args'

  | (ArgIsTerm _ | ArgIsType _ | ArgEqType _ | ArgEqTerm _)::_, _::_

  | (_::_), []

  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false

and alpha_equal_abstraction
  : 'a . ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool
  = fun equal_v e e' ->
  e == e' ||
  (* XXX try e = e' ? *)
  match e, e' with

  | Abstract (_, u, abstr), Abstract(_, u', abstr') ->
     alpha_equal_type u u' &&
     alpha_equal_abstraction equal_v abstr abstr'

  | NotAbstract v, NotAbstract v' -> equal_v v v'

  | (Abstract _ | NotAbstract _), _ -> false
