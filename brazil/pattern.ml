(** Lazy pattern matching, to figure out which rewrite rules apply. *)

type ty =
  | Ty of Syntax.ty
  | El of Universe.t * term
  | Prod of ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term =
  | Term of Syntax.term
  | PVar of int
  | Lambda of ty * ty * term
  | App of (ty * ty) * term * term
  | Idpath of ty * term
  | J of ty * (ty) * (term) * term * term * term
  | Refl of ty * term
  | Coerce of Universe.t * Universe.t * term
  | NameProd of Universe.t * Universe.t * term * term
  | NamePaths of Universe.t * term * term * term
  | NameId of Universe.t * term * term * term

let of_ty' k l ((t', loc) as t) =
  match t' with

    | Syntax.Universe _ ->
      Ty t

    | Syntax.El (alpha, e) ->
      let e = of_term' k l e in
      begin match e with
        | Term e -> Ty (Syntax.El (alpha, e), loc)
        | _ -> El (alpha, e)
      end

    | Syntax.Unit ->
      Ty t

    | Syntax.Prod (x, t1, t2) ->
      let t1 = of_ty' k l t1
      and t2 = of_ty' k (l+1) t2
      in
        begin match t1, t2 with
          | Ty t1, Ty t2 -> Ty (Syntax.Prod (x, t1, t2), loc)
          | _ -> Prod (t1, t2)
        end

    | Syntax.Paths (t, e1, e2) ->
      let t = of_ty' k l t
      and e1 = of_term' k l e1
      and e2 = of_term' k l e2
      in
        begin match t, e1, e2 with
          | Ty t, Term e1, Term e2 -> Ty (Syntax.Paths (t, e1, e2), loc)
          | _ -> Paths (t, e1, e2)
        end

    | Syntax.Id (t, e1, e2) ->
      let t = of_ty' k l t
      and e1 = of_term' k l e1
      and e2 = of_term' k l e2
      in
        begin match t, e1, e2 with
          | Ty t, Term e1, Term e2 -> Ty (Syntax.Id (t, e1, e2), loc)
          | _ -> Id (t, e1, e2)
        end


and of_term' k l ((e', loc) as e) =
  match e' with

    | Syntax.Var j ->
      if j < l then Term (Syntax.Var j, loc) (* bound variable *)
      else if j < k + l then PVar (j - l) (* pattern variable *)
      else Term (Syntax.Var (j - k), loc) (* other variable *)

    | Syntax.Equation (_, _, e2) ->
      of_term' k l e

    | Syntax.Rewrite (_, _, e) ->
      of_term' k l e

    | Syntax.Ascribe (e, _) ->
      of_term' k l e

    | Syntax.Lambda (x, t1, t2, e) ->
      let t1 = of_ty' k l t1
      and t2 = of_ty' k (l+1) t2
      and e = of_term'' k l e
      in
        begin match t1, t2, e with
          | Ty t1, Ty t2, Term e -> Term (Syntax.Lambda (x, t1, t2, e), loc)
          | _ -> Lambda (t1, t2, e)
        end

    | Syntax.App ((x, t1, t2), e1, e2) ->
      let e1 = of_term' k l  e1
      and e2 = of_term' k l e2
      and t2 = of_term' k (l+1) t2
      and t1 = of_ty' k l t1
      in
        begin match t1, t2, e1, e2 with
          | Ty t1, Ty t2, Term e1, Term e2 ->
            Term (Syntax.App ((x, t1, t2), e1, e2), loc)
          | _ -> App ((t1, t2), e1, e2)
        end

    | Syntax.UnitTerm ->
      Term e

    | Syntax.Idpath (t, e) ->
      let t = of_ty' k l t
      and e = of_term' k l e
      in
        begin match t, e with
          | Ty t, Term e -> Term (Syntax.Idpath (t, e), loc)
          | _ -> Idpath (t, e)
        end

    | Syntax.J (t, (x,y,p,u), (z,e1), e2, e3, e4) ->
      let t = of_ty' k l t
      and u = of_ty' k (l+3) u
      and e1 = of_term' k (l+1) e1
      and e2 = of_term' k e2
      and e3 = of_term' k e3
      and e4 = of_term' k e4
      in
        begin match t, u, e1, e2, e3, e4 with
          | Ty t, Ty u, Term e1, Term e2, Term e3, Term e4 ->
            Term (Syntax.J (t, (x,y,p,u), (z,e1), e2, e3), loc)
          | _ -> J (t, u, e1, e2, e3, e4)
        end

    | Syntax.Refl (t, e) ->          
      let t = of_ty' k l t
      and e = of_term' k l e
      in
        begin match t, e with
          | Ty t, Term e -> Term (Syntax.Idpath (t, e), loc)
          | _ -> Idpath (t, e)
        end

    | Syntax.Coerce (alpha, beta, e) ->
      let e = of_term' k l e
      in
        begin match e with
          | Term e -> Term (Syntax.Coerce (alpha, beta, e), loc)
          | _ -> Coerce (alpha, beta, e)
        end

    | Syntax.NameUnit ->
      Term e

    | Syntax.NameProd (alpha, beta, x, e1, e2) ->
      let e1 = of_term' k l e1
      and e2 = of_term' k (l+1) e2
      in
        begin match e1, e2 with
          | Term e1, Term e2 -> Term (Syntax.NameProd (alpha, beta, e1, e2), loc)
          | _ -> NameProd (alpha, beta, e1, e2)
        end

    | Syntax.NameUniverse _ ->
      Term e

    | Syntax.NamePaths (alpha, e1, e2, e3) ->
      let e1 = of_term' k l e1
      and e2 = of_term' k l e2
      and e3 = of_term' k l e3
      in
        begin match e1, e2, e3 with
          | Term e1, Term e2, Term e3 -> Term (Syntax.NamePaths (alpha, e1, e2, e3), loc)
          | _ -> NamePaths (alpha, e1, e2, e3)
        end

    | Syntax.NameId (alpha, e1, e2, e3) ->
      let e1 = of_term' k l e1
      and e2 = of_term' k l e2
      and e3 = of_term' k l e3
      in
        begin match e1, e2, e3 with
          | Term e1, Term e2, Term e3 -> Term (Syntax.NameId (alpha, e1, e2, e3), loc)
          | _ -> NameId (alpha, e1, e2, e3)
        end

let of_term k e = of_term' k 0 e

let of_ty k t = of_ty' k 0 t
