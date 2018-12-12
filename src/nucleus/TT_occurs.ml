open Jdg_typedefs

(* Does the bound variable [k] occur in an expression? *)
let rec term k = function
  | TermAtom _ -> false
  | TermBound m -> k = m
  | TermMeta (_, args) -> term_arguments k args
  | TermConstructor (_, args) -> arguments k args
  | TermConvert (e, asmp, t) -> term k e || assumptions k asmp || ty k t

and ty k = function
  | TypeConstructor (_, args) -> arguments k args
  | TypeMeta (_, args) -> term_arguments k args

and arguments k = function
  | [] -> false
  | arg :: args -> argument k arg || arguments k args

and term_arguments k = function
  | [] -> false
  | arg :: args -> term k arg || term_arguments k args

and argument k = function
  | ArgumentIsType t  -> abstraction ty k t
  | ArgumentIsTerm e  -> abstraction term k e
  | ArgumentEqType abstr -> abstraction eq_type k abstr
  | ArgumentEqTerm abstr -> abstraction eq_term k abstr

and eq_type k (EqType (asmp, t1, t2)) =
  assumptions k asmp || ty k t1 || ty k t2

and eq_term k (EqTerm (asmp, e1, e2, t)) =
  assumptions k asmp || term k e1 || term k e2 || ty k t

and abstraction
  : 'a . (bound -> 'a -> bool) -> bound -> 'a abstraction -> bool
  = fun occurs_v k ->
  function
  | NotAbstract v -> occurs_v k v
  | Abstract (_, u, abstr) ->
     ty k u || abstraction occurs_v (k+1) abstr

and assumptions k asmp =
  Assumption.mem_bound k asmp
