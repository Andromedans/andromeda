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


let paren tag strings = tag ^ "(" ^ String.concat "," strings ^ ")"

let rec string_of_ty string_of_var (ty,_) =
  let recurse    = string_of_term string_of_var  in
  let recurse_ty = string_of_ty string_of_var  in

  match ty with
  | El term -> paren "El" [recurse term]
  | Universe (u,_) -> paren "Universe" [Universe.to_string u]
  | Unit -> "Unit"
  | Prod(name, ty1, ty2) -> paren "Prod" [name; recurse_ty ty1; recurse_ty ty2]
  | Paths(term1, term2) -> paren "Paths" [recurse term1; recurse term2]
  | Id(term1, term2) -> paren "Id" [recurse term1; recurse term2]

and string_of_term string_of_var (term,_) =
  let recurse    = string_of_term string_of_var  in
  let recurse_ty = string_of_ty string_of_var  in

  match term with
  | Var v -> paren "Var" [string_of_var v]
  | Equation(term1, term2) -> paren "Equation" [recurse term1; recurse term2]
  | Rewrite(term1, term2) -> paren "Rewrite" [recurse term1; recurse term2]
  | Ascribe(term1, ty2) -> paren "Ascribe" [recurse term1; recurse_ty ty2]
  | Lambda(name,ty1,term2) -> paren "Lambda" [name; recurse_ty ty1; recurse term2]
  | App(term1, term2) -> paren "App" [recurse term1; recurse term2]
  | UnitTerm -> "UnitTerm"
  | Idpath term1 -> paren "Idpath" [recurse term1]
  | J((name1,name2,name3,ty4),(name5,term6),term7) ->
      paren "J" [paren "" [name1; name2; name3; recurse_ty ty4];
                 paren "" [name5; recurse term6];
                 recurse term7]
  | Refl term1 -> paren "Refl" [recurse term1]
  | Coerce((u1,_), term2) -> paren "Coerce" [Universe.to_string u1; recurse term2]
  | NameUniverse (u1,_) -> paren "NameUniverse" [Universe.to_string u1]
  | NameUnit -> "NameUnit"
  | NameProd(name1, term2, term3) ->
      paren "NameProd" [name1; recurse term2; recurse term3]
  | NamePaths(term1, term2) -> paren "NamePaths" [recurse term1; recurse term2]
  | NameId(term1, term2) -> paren "NameId" [recurse term1; recurse term2]

