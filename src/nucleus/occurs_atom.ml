open Nucleus_types

(* Does the atom [x] occur in an expression? *)
let rec is_type x = function
  | TypeConstructor (_, args) -> arguments x args
  | TypeMeta (mv, args) -> meta x mv || term_arguments x args

and is_term x = function
  | TermAtom y -> Nonce.equal x y.atom_nonce
  | TermBoundVar _ -> false
  | TermMeta (mv, args) -> meta x mv || term_arguments x args
  | TermConstructor (_, args) -> arguments x args
  | TermConvert (e, asmp, t) -> is_term x e || assumptions x asmp || is_type x t

and eq_type x (EqType (asmp, t1, t2)) =
  assumptions x asmp || is_type x t1 || is_type x t2

and eq_term x (EqTerm (asmp, e1, e2, t)) =
  assumptions x asmp || is_term x e1 || is_term x e2 || is_type x t

and assumptions x asmp =
  Assumption.mem_free_var x asmp

and abstraction
  : 'a . (Nonce.t -> 'a -> bool) -> Nonce.t -> 'a abstraction -> bool
  = fun occurs_v x ->
  function
  | NotAbstract v -> occurs_v x v
  | Abstract (_, u, abstr) ->
     is_type x u || abstraction occurs_v x abstr

and meta x = function
  | MetaFree {meta_boundary; _} -> abstraction boundary x meta_boundary
  | MetaBound _ -> false


and argument x = function
  | Arg_NotAbstract v -> judgement x v
  | Arg_Abstract (_, arg) -> argument x arg

and arguments x = function
  | [] -> false
  | arg :: args -> argument x arg || arguments x args

and term_arguments x = function
  | [] -> false
  | arg :: args -> is_term x arg || term_arguments x args

and judgement x = function
  | JudgementIsType t  -> is_type x t
  | JudgementIsTerm e  -> is_term x e
  | JudgementEqType eq -> eq_type x eq
  | JudgementEqTerm eq -> eq_term x eq

and boundary x = function
  | BoundaryIsType ()  -> false
  | BoundaryIsTerm t  -> is_type x t
  | BoundaryEqType (t1, t2) -> is_type x t1 || is_type x t2
  | BoundaryEqTerm (e1, e2, t) -> is_type x t || is_term x e1  || is_term x e2
