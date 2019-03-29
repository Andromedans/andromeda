(****** Alpha equality ******)

open Nucleus_types

let equal_bound (i : bound) (j : bound) = (i = j)

let rec is_type t1 t2 =
  t1 == t2 ||
  match t1, t2 with

  | TypeMeta (mv, args), TypeMeta (mv', args') ->
     Nonce.equal mv.meta_nonce mv'.meta_nonce && term_arguments args args'

  | TypeConstructor (c, args), TypeConstructor (c', args') ->
     Ident.equal c c' && arguments args args'

  | (TypeConstructor _ | TypeMeta _), _ -> false

and is_term e1 e2 =
  e1 == e2 ||
  begin match e1, e2 with

  | TermBound i, TermBound j -> i = j

  | TermAtom {atom_nonce=x;_}, TermAtom {atom_nonce=y;_} -> Nonce.equal x y

  | TermMeta (mv, args), TermMeta (mv', args') ->
     Nonce.equal mv.meta_nonce mv'.meta_nonce && term_arguments args args'

  | TermConstructor (c, args), TermConstructor (c', args') ->
     Ident.equal c c' && arguments args args'

  | TermConvert (e1, _, _), TermConvert (e2, _, _) ->
     is_term e1 e2

  | (TermAtom _ | TermBound _ | TermConstructor _  | TermMeta _  | TermConvert _), _ ->
     false
  end

and abstraction
  : 'a . ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool
  = fun equal_v e e' ->
    e == e' ||
    (* XXX try e = e' ? *)
    match e, e' with

    | Abstract ({atom_type=u;_}, abstr), Abstract({atom_type=u';_}, abstr') ->
       is_type u u' &&
       abstraction equal_v abstr abstr'

    | NotAbstract v, NotAbstract v' -> equal_v v v'

    | (Abstract _ | NotAbstract _), _ -> false

and term_arguments args args' =
  args == args' ||
  match args, args' with
  | [], [] -> true
  | arg :: args, arg' :: args' ->
     is_term arg arg' && term_arguments args args'
  | (_::_), []
  | [], (_::_) -> assert false

and arguments args args' =
  args == args' ||
  match args, args' with

  | [], [] -> true

  | (ArgumentIsTerm e) :: args, (ArgumentIsTerm e') :: args' ->
     abstraction is_term e e' && arguments args args'

  | (ArgumentIsType t) :: args, (ArgumentIsType t') :: args' ->
     abstraction is_type t t' && arguments args args'

  | ArgumentEqType _ :: args, ArgumentEqType _ :: args' -> arguments args args'

  | ArgumentEqTerm _ :: args, ArgumentEqTerm _ :: args' -> arguments args args'

  | (ArgumentIsTerm _ | ArgumentIsType _ | ArgumentEqType _ | ArgumentEqTerm _)::_, _::_

  | (_::_), []

  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false
