open Nucleus_types

(* Does the bound variable [k] occur in an expression? *)
let rec is_type k = function
  | TypeConstructor (_, args) -> arguments k args
  | TypeMeta (_, args) -> term_arguments k args

and is_term k = function
  | TermAtom _ -> false
  | TermBound m -> k = m
  | TermMeta (_, args) -> term_arguments k args
  | TermConstructor (_, args) -> arguments k args
  | TermConvert (e, asmp, t) -> is_term k e || assumptions k asmp || is_type k t

and eq_type k (EqType (asmp, t1, t2)) =
  assumptions k asmp || is_type k t1 || is_type k t2

and eq_term k (EqTerm (asmp, e1, e2, t)) =
  assumptions k asmp || is_term k e1 || is_term k e2 || is_type k t

and assumptions k asmp =
  Assumption.mem_bound k asmp

and abstraction
  : 'a . (bound -> 'a -> bool) -> bound -> 'a abstraction -> bool
  = fun occurs_v k ->
  function
  | NotAbstract v -> occurs_v k v
  | Abstract ({atom_type=u;_}, abstr) ->
     is_type k u || abstraction occurs_v (k+1) abstr

and arguments k = function
  | [] -> false
  | arg :: args -> abstraction judgement k arg || arguments k args

and term_arguments k = function
  | [] -> false
  | arg :: args -> is_term k arg || term_arguments k args

and judgement k = function
  | JudgementIsType t  -> is_type k t
  | JudgementIsTerm e  -> is_term k e
  | JudgementEqType eq -> eq_type k eq
  | JudgementEqTerm eq -> eq_term k eq

let boundary k = function
  | BoundaryIsType ()  -> false
  | BoundaryIsTerm t  -> is_type k t
  | BoundaryEqType (t1, t2) -> is_type k t1 || is_type k t2
  | BoundaryEqTerm (e1, e2, t) -> is_type k t || is_term k e1  || is_term k e2
