open Jdg_typedefs

(* Does the bound variable [k] occur in an expression? *)
let rec occurs_term k = function
  | TermAtom _ -> false
  | TermBound m -> k = m
  | TermMeta (_, args) -> occurs_term_args k args
  | TermConstructor (_, args) -> occurs_args k args
  | TermConvert (e, asmp, t) -> occurs_term k e || occurs_assumptions k asmp || occurs_type k t

and occurs_type k = function
  | TypeConstructor (_, args) -> occurs_args k args
  | TypeMeta (_, args) -> occurs_term_args k args

and occurs_args k = function
  | [] -> false
  | arg :: args -> occurs_arg k arg || occurs_args k args

and occurs_term_args k = function
  | [] -> false
  | arg :: args -> occurs_term k arg || occurs_term_args k args

and occurs_arg k = function
  | ArgIsType t  -> occurs_abstraction occurs_type k t
  | ArgIsTerm e  -> occurs_abstraction occurs_term k e
  | ArgEqType abstr -> occurs_abstraction occurs_eq_type k abstr
  | ArgEqTerm abstr -> occurs_abstraction occurs_eq_term k abstr

and occurs_eq_type k (EqType (asmp, t1, t2)) =
  occurs_assumptions k asmp || occurs_type k t1 || occurs_type k t2

and occurs_eq_term k (EqTerm (asmp, e1, e2, t)) =
  occurs_assumptions k asmp || occurs_term k e1 || occurs_term k e2 || occurs_type k t

and occurs_abstraction
  : 'a . (bound -> 'a -> bool) -> bound -> 'a abstraction -> bool
  = fun occurs_v k ->
  function
  | NotAbstract v -> occurs_v k v
  | Abstract (_, u, abstr) ->
     occurs_type k u || occurs_abstraction occurs_v (k+1) abstr

and occurs_assumptions k asmp =
  Assumption.mem_bound k asmp
