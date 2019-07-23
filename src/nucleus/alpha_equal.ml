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

  | TermBound i, TermBound j -> i = j

  | TermAtom {atom_nonce=x;_}, TermAtom {atom_nonce=y;_} -> Nonce.equal x y

  | TermMeta (mv, args), TermMeta (mv', args') ->
     Nonce.equal mv.meta_nonce mv'.meta_nonce && term_arguments args args'

  | TermConstructor (c, args), TermConstructor (c', args') ->
     Ident.equal c c' && arguments args args'

  | (TermAtom _ | TermBound _ | TermConstructor _  | TermMeta _), _ ->
     false
  end

and abstraction
  : 'a 'b . ('a -> 'b -> bool) -> 'a abstraction -> 'b abstraction -> bool
  = fun equal_v e e' ->
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

  | (JudgementIsTerm e) :: args, (JudgementIsTerm e') :: args' ->
     abstraction is_term e e' && arguments args args'

  | (JudgementIsType t) :: args, (JudgementIsType t') :: args' ->
     abstraction is_type t t' && arguments args args'

  | JudgementEqType _ :: args, JudgementEqType _ :: args' -> arguments args args'

  | JudgementEqTerm _ :: args, JudgementEqTerm _ :: args' -> arguments args args'

  | (JudgementIsTerm _ | JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _)::_, _::_

  | (_::_), []

  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false

let judgement jdg1 jdg2 =
  match jdg1, jdg2 with
  | JudgementIsType t1, JudgementIsType t2 -> abstraction is_type t1 t2

  | JudgementIsTerm e1, JudgementIsTerm e2 -> abstraction is_term e1 e2

  (** Comparing equality types means comparing their "proof terms", not their boundaries! *)
  | JudgementEqType eq1, JudgementEqType eq2 -> abstraction (fun _ _ -> true) eq1 eq2
  | JudgementEqTerm eq1, JudgementEqTerm eq2 -> abstraction (fun _ _ -> true) eq1 eq2

  | JudgementIsType _, (JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _)
  | JudgementIsTerm _, (JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _)
  | JudgementEqType _, (JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _)
  | JudgementEqTerm _, (JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _) ->
     false

let boundary jdg1 jdg2 =
  match jdg1, jdg2 with
  | BoundaryIsType abstr1, BoundaryIsType abstr2 -> abstraction (fun () () -> true) abstr1 abstr2

  | BoundaryIsTerm t1, BoundaryIsTerm t2 -> abstraction is_type t1 t2

  | BoundaryEqType eq1, BoundaryEqType eq2 ->
     abstraction (fun (u1, t1) (u2, t2) -> is_type u1 u2 && is_type t1 t2) eq1 eq2

  | BoundaryEqTerm eq1, BoundaryEqTerm eq2 ->
     abstraction (fun (a1, b1, t1) (a2, b2, t2) -> is_type t1 t2 && is_term a1 a2 && is_term b1 b2) eq1 eq2

  | BoundaryIsType _, (BoundaryIsTerm _ | BoundaryEqType _ | BoundaryEqTerm _)
  | BoundaryIsTerm _, (BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _)
  | BoundaryEqType _, (BoundaryIsType _ | BoundaryIsTerm _ | BoundaryEqTerm _)
  | BoundaryEqTerm _, (BoundaryIsType _ | BoundaryIsTerm _ | BoundaryEqType _) ->
     false


let check_is_type_boundary abstr bdry =
  abstraction (fun _ _ -> true) abstr bdry

let check_is_term_boundary sgn abstr bdry =
  abstraction (fun e t -> is_type (Sanity.type_of_term sgn e) t) abstr bdry

let check_eq_type_boundary _ _ = failwith "check_eq_type_boundary"
let check_eq_term_boundary _ _ = failwith "check_eq_term_boundary"

let check_judgement_boundary sgn jdg bdry =
  match bdry with
    | BoundaryIsType bdry ->
       begin match jdg with
       | JudgementIsType jdg -> check_is_type_boundary jdg bdry
       | JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _ -> false
       end

    | BoundaryIsTerm bdry ->
       begin match jdg with
       | JudgementIsTerm jdg -> check_is_term_boundary sgn jdg bdry
       | JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _ -> false
       end

    | BoundaryEqType bdry ->
       begin match jdg with
       | JudgementEqType jdg -> check_eq_type_boundary jdg bdry
       | JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _ -> false
       end

    | BoundaryEqTerm bdry ->
       begin match jdg with
       | JudgementEqTerm jdg -> check_eq_term_boundary jdg bdry
       | JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _ -> false
       end


let abstraction eq_v e e' = e == e' || abstraction eq_v e e'
