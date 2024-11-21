open Nucleus_types

(* Does the bound variable [k] occur in an expression? *)
let rec is_type k = function
  | TypeConstructor (_, args) -> arguments k args
  | TypeMeta (_, args) -> term_arguments k args

and is_term k = function
  | TermAtom _ -> false
  | TermBoundVar m -> k = m
  | TermMeta (_, args) -> term_arguments k args
  | TermConstructor (_, args) -> arguments k args
  | TermConvert (e, asmp, t) -> is_term k e || assumptions k asmp || is_type k t

and eq_type k (EqType (asmp, t1, t2)) =
  assumptions k asmp || is_type k t1 || is_type k t2

and eq_term k (EqTerm (asmp, e1, e2, t)) =
  assumptions k asmp || is_term k e1 || is_term k e2 || is_type k t

and assumptions k asmp =
  Assumption.mem_bound_var k asmp

and abstraction
  : 'a . (bound -> 'a -> bool) -> bound -> 'a abstraction -> bool
  = fun occurs_v k ->
  function
  | NotAbstract v -> occurs_v k v
  | Abstract (_, u, abstr) ->
     is_type k u || abstraction occurs_v (k+1) abstr

and argument k = function
  | Arg_NotAbstract v -> judgement k v
  | Arg_Abstract (_, arg) -> argument (k+1) arg

and arguments k = function
  | [] -> false
  | arg :: args -> argument k arg || arguments k args

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

let judgement_with_boundary k (jdg, bdry) = 
  judgement k jdg || boundary k bdry