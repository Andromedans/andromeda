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
      if x = y then k else search (k+1) ys
  in
    search 0

let rec ty xs (t, pos) =
  let t = 
    begin match t with
      | Input.Universe u -> Syntax.Universe u

      | Input.Unit -> Syntax.Unit

      | Input.Prod (x, t1, t2) ->
        let t1 = ty xs t1 in
        let t2 = ty (x :: xs) t2 in
          Syntax.Prod (x, t1, t2)
            
      | Input.Paths (t, e1, e2) ->
        let t = ty xs t in
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Syntax.Paths (t, e1, e2)

      | Input.Id (t, e1, e2) ->
        let t = ty xs t in
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Syntax.Id (t, e1, e2)

      (* We treat everything else as an element of a universe.
         In some cases we can tell this will be an error, but we let
         typechecking figure this out (as it has to in any case) *)
      | (Input.Var _
        | Input.Hint _ 
        | Input.Ascribe _ 
        | Input.App _
        | Input.Lambda _
        | Input.UnitTerm
        | Input.Idpath _
        | Input.J _
        | Input.Refl _
        | Input.G _
        | Input.Coerce _) ->
        let e = term xs (t, pos) in
          Syntax.El e
    end
  in
    (t, pos)

and term xs (e, pos) =
  let e =
    begin match e with

      | Input.Var x ->
        begin match lookup x xs with
          | Some k -> Syntax.Var k
          | None -> Error.typing ~pos "unknown identifier %s" x
        end

      | Input.Hint (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Syntax.Hint (e1, e2)

      | Input.Ascribe (e, t) ->
        let e = term xs e in
        let t = ty xs t in
          Syntax.Ascribe(e, t)

      | Input.Lambda (x, t, e) ->
        let t = ty xs t in
        let e = ty (x :: xs) e in
          Syntax.Lambda (x, t, e)

      | Input.App (e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
          Syntax.App (e1, e2)

      | Input.UnitTerm -> Syntax.UnitTerm

      | Input.Idpath e ->
        let e = term xs e in
          Syntax.Idpath e

      | Input.J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
        let t = ty xs t in
        let u = ty (x :: y :: p :: xs) u in
        let e1 = term (z :: xs) e1 in
        let e2 = term xs e2 in
        let e3 = term xs e3 in
        let e4 = term xs e4 in
          Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4)

      | Input.Refl e ->
        let e = term xs e in
          Syntax.Refl e

      | Input.G (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
        let t = ty xs t in
        let u = ty (x :: y :: p :: xs) u in
        let e1 = term (z :: xs) e1 in
        let e2 = term xs e2 in
        let e3 = term xs e3 in
        let e4 = term xs e4 in
          Syntax.G (t, (x, y, p, u), (z, e1), e2, e3, e4)

      | Input.Prod (x, e1, e2) ->
        let e1 = term xs e1 in
        let e2 = term (x :: xs) e2 in
          Syntax.NameProd (x, e1, e2)

      | Input.NameUniverse u -> Syntax.NameUniverse u

      | Input.Coerce (u, v, e) ->
        let e = term xs e in
          Syntax.Coerce (u, v, e)

      | Input.NamePaths (u, e1, e2, e3) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
        let e3 = term xs e3 in
          Syntax.NamePaths (u, e1, e2, e3)

      | Input.NameId (u, e1, e2, e3) ->
        let e1 = term xs e1 in
        let e2 = term xs e2 in
        let e3 = term xs e3 in
          Syntax.NameId (u, e1, e2, e3)
    end
  in
    (e, pos)
