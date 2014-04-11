let anonymous = "_"

(** Users refer to variables as strings *)
type name = string

(** At the input level we only have expressions, which can refer either to terms
    or types. This is so because we do not distinguish between types and their names.
    A desugaring phase figures out what is what. *)

type universe = Universe.t * Position.t

type 'a ty = 'a ty' * Position.t
and 'a ty' =
  | El of 'a term
  | Universe of universe (* Universe i *)
  | Unit (* unit *)
  | Prod of name * 'a ty * 'a ty (* forall (x : T) , U *)
  | Paths of 'a term * 'a term (* e1 = e2 *)
  | Id of 'a term * 'a term (* e1 == e2 *)

and 'a term = 'a term' * Position.t
and 'a term' =
  (* terms *)
  | Var of 'a (* x *)
  | Equation of 'a term * 'a term (* equation e1 in e2 *)
  | Rewrite of 'a term * 'a term (* rewrite e1 in e2 *)
  | Ascribe of 'a term * 'a ty (* e :: T *)
  | Lambda of name * 'a ty * 'a term (* fun (x : T) => e *)
  | App of 'a term * 'a term (* e1 e2 *)
  | UnitTerm (* () *)
  | Idpath of 'a term (* idpath e *)
  | J of (name * name * name * 'a ty) * (name * 'a term) * 'a term
    (* J ([x . y . p . U], [z . e1], e2) *)
  | Refl of 'a term (* refl T e *)
  | Coerce of universe * 'a term (* coerce i j e *)
  | NameUniverse of universe (* Universe i *)
  | NameUnit (* unit *)
  | NameProd of name * 'a term * 'a term (* forall (x : T) , U *)
  | NamePaths of 'a term * 'a term (* e1 = e2 *)
  | NameId of 'a term * 'a term (* e1 == e2 *)

type toplevel = toplevel' * Position.t
and toplevel' =
  | Help (* #help *)
  | Quit (* #quit *)
  | Context (* #context *)
  | Assume of name list * name ty (* assume x1 ... xn : t *)
  | Define of name * name term (* define x := e *)
