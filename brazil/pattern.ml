type variable = Common.debruijn

type pattern =
  | Anonymous
  | PVar of variable
  | Var of Syntax.variable
  | Lambda of ty_pattern * ty_pattern * pattern
  | App of pattern * pattern
  | UnitTerm
  | Idpath of ty_pattern * pattern
  | J of ty_pattern * ty_pattern * pattern * pattern * pattern * pattern
  | Refl of ty_pattern * pattern
  | Coerce of Universe.t * Universe.t * pattern
  | NameUnit
  | NameProd of Universe.t * Universe.t * pattern * pattern
  | NameUniverse of Universe.t
  | NamePaths of Univetse.t * pattern * pattern * pattern
  | NameId of Universe.t * pattern * pattern * pattern

and ty_pattern =
  | Universe of Universe.t
  | El of Universe.t * pattern
  | Unit
  | Prod of ty_pattern * ty_pattern
  | Paths of ty_pattern * pattern * pattern
  | Id of ty_pattern * pattern * pattern


exception Incompatible
let rec join_assoc lst1 lst2 =
  match lst1 with
    | [] -> lst2
    | (x,e) :: lst1 ->
      begin
        try
          let e' = List.assoc x lst2 in
            if Syntax.equal e e'
            then (x,e) :: join_assoc lst1 lst2
            else raise Incompatible
        with
          | Not_found -> (x,e) :: join_assoc lst1 lst2
      end

let rec match p e =
  match p, fst e with
    | Anonymous, _ -> []
    | PVar x, _ -> [(x,e)]
    | Var k, Syntax.Var m ->
      if k = m then [] else raise Incompatiblw
    | Lambda (pt1, pt2, p), Syntax.Lambda (_, t1, t2, e) ->
      let lst1 = match_ty pt1 t1 in
      let lst2 = match_ty pt2 t2 in
      let lst3 = match e in
        assoc_join (assoc_join lst1 lst2) lst2
    | 
