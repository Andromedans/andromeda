(****** Alpha equality ******)

open Jdg_typedefs

let equal_bound (i : bound) (j : bound) = (i = j)

let rec term e1 e2 =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | TermAtom {atom_name=x;_}, TermAtom {atom_name=y;_} -> Name.eq_atom x y

    | TermBound i, TermBound j -> i = j

    | TermConstructor (c, args), TermConstructor (c', args') ->
       Name.eq_ident c c' && arguments args args'

    | TermMeta (mv, args), TermMeta (mv', args') ->
       Name.eq_meta mv.meta_name mv'.meta_name && term_arguments args args'

    | TermConvert (e1, _, _), TermConvert (e2, _, _) ->
       term e1 e2

    | (TermAtom _ | TermBound _ | TermConstructor _  | TermMeta _  | TermConvert _), _ ->
      false
  end

and ty t1 t2 =
  match t1, t2 with

  | TypeConstructor (c, args), TypeConstructor (c', args') ->
     Name.eq_ident c c' && arguments args args'

  | TypeMeta (mv, args), TypeMeta (mv', args') ->
     Name.eq_meta mv.meta_name mv'.meta_name && term_arguments args args'

  | (TypeConstructor _ | TypeMeta _), _ -> false

and term_arguments args args' =
  match args, args' with
  | [], [] -> true
  | arg::args, arg'::args' ->
     term arg arg' && term_arguments args args'
  | (_::_), []
  | [], (_::_) -> assert false

and arguments args args' =
  match args, args' with

  | [], [] -> true

  | (ArgumentIsTerm e)::args, (ArgumentIsTerm e')::args' ->
     abstraction term e e' && arguments args args'

  | (ArgumentIsType t)::args, (ArgumentIsType t')::args' ->
     abstraction ty t t' && arguments args args'

  | ArgumentEqType _ :: args, ArgumentEqType _ :: args' -> arguments args args'

  | ArgumentEqTerm _ :: args, ArgumentEqTerm _ :: args' -> arguments args args'

  | (ArgumentIsTerm _ | ArgumentIsType _ | ArgumentEqType _ | ArgumentEqTerm _)::_, _::_

  | (_::_), []

  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false

and abstraction
  : 'a . ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool
  = fun equal_v e e' ->
  e == e' ||
  (* XXX try e = e' ? *)
  match e, e' with

  | Abstract (_, u, abstr), Abstract(_, u', abstr') ->
     ty u u' &&
     abstraction equal_v abstr abstr'

  | NotAbstract v, NotAbstract v' -> equal_v v v'

  | (Abstract _ | NotAbstract _), _ -> false
