(** Convert input syntax to abstract syntax.

    We convert variables do De Bruijn indices, although binders remember
    the variables names for later printing out. We also have to decouple
    terms from types by figuring out which expressions are types and which
    ones are names of types. We insert [El] as necessary.
*)

(** Find the De Bruijn index of a variable. *)
let lookup x =
  let rec search k = function
    | [] -> None
    | y :: ys ->
      if x = y then Some k else search (k+1) ys
  in
    search 0

let rec ty xs (t, loc) =
  let t = 
    begin match t with
      | Input.El e ->
        let e = term xs e in
          Input.El e

      | Input.Universe u -> Input.Universe u

      | Input.Unit -> Input.Unit

      | Input.Prod (x, t1, t2) ->
        let t1 = ty xs t1 in
        let t2 = ty (x :: xs) t2 in
          Input.Prod (x, t1, t2)
            
      | Input.Paths (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Input.Paths (e1, e2)

      | Input.Id (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Input.Id (e1, e2)
    end
  in
    (t, loc)

and term xs (e, loc) =
  let e =
    begin match e with

      | Input.Var x ->
        begin match lookup x xs with
          | Some k -> Input.Var k
          | None -> Error.typing ~loc "unknown identifier %s" x
        end

      | Input.Equation (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Input.Equation (e1, e2)

      | Input.Rewrite (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Input.Rewrite (e1, e2)

      | Input.Ascribe (e, t) ->
        let e = term xs e in
        let t = ty xs t in
          Input.Ascribe(e, t)

      | Input.Lambda (x, t, e) ->
        let t = ty xs t in
        let e = term (x :: xs) e in
          Input.Lambda (x, t, e)

      | Input.App (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Input.App (e1, e2)

      | Input.UnitTerm -> Input.UnitTerm

      | Input.Idpath e ->
        let e = term xs e in
          Input.Idpath e

      | Input.J ((x, y, p, u), (z, e1), e2) ->
        let u = ty (x :: y :: p :: xs) u in
        let e1 = term (z :: xs) e1 in
        let e2 = term xs e2 in
          Input.J ((x, y, p, u), (z, e1), e2)

      | Input.Refl e ->
        let e = term xs e in
          Input.Refl e

      | Input.NameUnit -> Input.NameUnit

      | Input.NameProd (x, e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term (x :: xs) e2 in
          Input.NameProd (x, e1, e2)

      | Input.NameUniverse u -> Input.NameUniverse u

      | Input.Coerce (u, e) ->
        let e = term xs e in
          Input.Coerce (u, e)

      | Input.NamePaths (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Input.NamePaths (e1, e2)

      | Input.NameId (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Input.NameId (e1, e2)
    end
  in
    (e, loc)
