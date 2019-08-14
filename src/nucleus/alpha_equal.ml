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

  | TermConvert (e1, _, _), TermConvert (e2, _, _) ->
     is_term e1 e2

  | TermConvert (e1, _, _), e2 ->
     is_term e1 e2

  | e1, TermConvert (e2, _, _) ->
     is_term e1 e2

  | TermBoundVar i, TermBoundVar j -> i = j

  | TermAtom {atom_nonce=x;_}, TermAtom {atom_nonce=y;_} -> Nonce.equal x y

  | TermMeta (mv, args), TermMeta (mv', args') ->
     Nonce.equal mv.meta_nonce mv'.meta_nonce && term_arguments args args'

  | TermConstructor (c, args), TermConstructor (c', args') ->
     Ident.equal c c' && arguments args args'

  | (TermAtom _ | TermBoundVar _ | TermConstructor _  | TermMeta _), _ ->
     false
  end

and abstraction
  : 'a 'a . ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool
  = fun equal_v e e' ->
    match e, e' with

    | Abstract (_, u, abstr), Abstract (_, u', abstr') ->
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

and argument arg arg' =
  match arg, arg' with
  | Arg_NotAbstract jdg, Arg_NotAbstract jdg' ->
     (* It would make sense to call [judgement] here, but that one compares
        boundaries of equations. Here we need to skip comparing those arguments
        that are equalities, as they do not figure in alpha equality at all
        (just like assumptions do not either). In addition, since the boundaries
        of equality arguments are detemined by the preceeding object arguments,
        we know comparison would succeed. *)
     begin match jdg, jdg' with
     | JudgementIsType t1, JudgementIsType t2 -> is_type t1 t2

     | JudgementIsTerm e1, JudgementIsTerm e2 -> is_term e1 e2

     | JudgementEqType _, JudgementEqType _
     | JudgementEqTerm _, JudgementEqTerm _ ->
        true

     | JudgementIsType _, (JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _)
     | JudgementIsTerm _, (JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _)
     | JudgementEqType _, (JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _)
     | JudgementEqTerm _, (JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _) ->
        false
     end

  | Arg_Abstract (_, arg), Arg_Abstract (_, arg') ->
     argument arg arg'

  | Arg_NotAbstract _, Arg_Abstract _
  | Arg_Abstract _, Arg_NotAbstract _ -> false

and arguments args args' =
  args == args' ||
  match args, args' with

  | [], [] -> true

  | arg :: args, arg' :: args' ->
     argument arg arg' && arguments args args'

  | (_::_), []

  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false

and judgement jdg1 jdg2 =
  match jdg1, jdg2 with
  | JudgementIsType t1, JudgementIsType t2 -> is_type t1 t2

  | JudgementIsTerm e1, JudgementIsTerm e2 -> is_term e1 e2

  | JudgementEqType (EqType (_asmp1, t1, u1)), JudgementEqType (EqType (_asmp2, t2, u2)) ->
     is_type t1 u2 && is_type u1 u2

  | JudgementEqTerm (EqTerm (_asmp1, a1, b1, t1)), JudgementEqTerm (EqTerm (_asmp2, a2, b2, t2)) ->
     is_type t1 t2 && is_term a1 a2 && is_term b1 b2

  | JudgementIsType _, (JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _)
  | JudgementIsTerm _, (JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _)
  | JudgementEqType _, (JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _)
  | JudgementEqTerm _, (JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _) ->
     false

let boundary jdg1 jdg2 =
  match jdg1, jdg2 with
  | BoundaryIsType (), BoundaryIsType () -> true

  | BoundaryIsTerm t1, BoundaryIsTerm t2 -> is_type t1 t2

  | BoundaryEqType (u1, t1), BoundaryEqType (u2, t2) ->
     is_type u1 u2 && is_type t1 t2

  | BoundaryEqTerm (a1, b1, t1), BoundaryEqTerm (a2, b2, t2) ->
     is_type t1 t2 && is_term a1 a2 && is_term b1 b2

  | BoundaryIsType _, (BoundaryIsTerm _ | BoundaryEqType _ | BoundaryEqTerm _)
  | BoundaryIsTerm _, (BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _)
  | BoundaryEqType _, (BoundaryIsType _ | BoundaryIsTerm _ | BoundaryEqTerm _)
  | BoundaryEqTerm _, (BoundaryIsType _ | BoundaryIsTerm _ | BoundaryEqType _) ->
     false

(* let abstraction eq_v e e' = e == e' || abstraction eq_v e e' *)
