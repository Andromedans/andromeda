(** Lazy pattern matching, to figure out which rewrite rules apply. *)

type name = string

type universe = Universe.t

type ty =
  | Ty of Syntax.ty
  | El of universe * term
  | Prod of name * ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term =
  | Term of Syntax.term
  | PVar of int
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | Idpath of ty * term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of ty * term
  | Coerce of universe * universe * term
  | NameProd of universe * universe * name * term * term
  | NamePaths of universe * term * term * term
  | NameId of universe * term * term * term

let rec of_ty' k l ((t', loc) as t) =
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
          | _ -> Prod (x, t1, t2)
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
      and e = of_term' k l e
      in
        begin match t1, t2, e with
          | Ty t1, Ty t2, Term e -> Term (Syntax.Lambda (x, t1, t2, e), loc)
          | _ -> Lambda (x, t1, t2, e)
        end

    | Syntax.App ((x, t1, t2), e1, e2) ->
      let e1 = of_term' k l  e1
      and e2 = of_term' k l e2
      and t2 = of_ty' k (l+1) t2
      and t1 = of_ty' k l t1
      in
        begin match t1, t2, e1, e2 with
          | Ty t1, Ty t2, Term e1, Term e2 ->
            Term (Syntax.App ((x, t1, t2), e1, e2), loc)
          | _ -> App ((x, t1, t2), e1, e2)
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
      and e2 = of_term' k l e2
      and e3 = of_term' k l e3
      and e4 = of_term' k l e4
      in
        begin match t, u, e1, e2, e3, e4 with
          | Ty t, Ty u, Term e1, Term e2, Term e3, Term e4 ->
            Term (Syntax.J (t, (x,y,p,u), (z,e1), e2, e3, e4), loc)
          | _ -> J (t, (x,y,p,u), (z,e1), e2, e3, e4)
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
          | Term e1, Term e2 -> Term (Syntax.NameProd (alpha, beta, x, e1, e2), loc)
          | _ -> NameProd (alpha, beta, x, e1, e2)
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

(** Substitute terms for pattern variables in the given pattern, coalescing resulting
    types and terms that are free of pattern variables. *)
let rec subst_ty inst k = function

  | Ty _ as t -> t

  | El (alpha, e) ->
    let e = subst_term inst k e in
      begin match e with
        | Term e -> Ty (Syntax.El (alpha, e), Position.nowhere)
        | _ -> El (alpha, e)
      end

  | Prod (x, t1, t2) ->
    let t1 = subst_ty inst k t1
    and t2 = subst_ty inst (k+1) t2
    in
      begin match t1, t2 with
        | Ty t1, Ty t2 -> Ty (Syntax.Prod (x, t1, t2), Position.nowhere)
        | _ -> Prod (x, t1, t2)
      end

  | Paths (t, e1, e2) ->
    let t = subst_ty inst k t
    and e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    in
      begin match t, e1, e2 with
        | Ty t, Term e1, Term e2 -> Ty (Syntax.Paths (t, e1, e2), Position.nowhere)
        | _ -> Paths (t, e1, e2)
      end

  | Id (t, e1, e2) ->
    let t = subst_ty inst k t
    and e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    in
      begin match t, e1, e2 with
        | Ty t, Term e1, Term e2 -> Ty (Syntax.Id (t, e1, e2), Position.nowhere)
        | _ -> Id (t, e1, e2)
      end

and subst_term inst k = function
  | Term _ as pe -> pe

  | (PVar i) as pe ->
    begin try
      let e = List.assoc i inst in
      let e = Syntax.shift k e in
        Term e
      with
        | Not_found -> pe
    end

  | Lambda (x, t1, t2, e) ->
    let t1 = subst_ty inst k t1
    and t2 = subst_ty inst (k+1) t2
    and e = subst_term inst (k+1) e
    in
      begin match t1, t2, e with
        | Ty t1, Ty t2, Term e -> Term (Syntax.Lambda (x, t1, t2, e), Position.nowhere)
        | _ -> Lambda (x, t1, t2, e)
      end

  | App ((x, t1, t2), e1, e2) ->
    let t1 = subst_ty inst k t1
    and t2 = subst_ty inst (k+1) t2
    and e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    in
      begin match t1, t2, e1, e2 with
        | Ty t1, Ty t2, Term e1, Term e2 ->
          Term (Syntax.App ((x, t1, t2), e1, e2), Position.nowhere)
        | _ -> App ((x, t1, t2), e1, e2)
      end

  | Idpath (t, e) ->
    let t = subst_ty inst k t
    and e = subst_term inst k e
    in
      begin match t, e with
        | Ty t, Term e -> Term (Syntax.Idpath (t, e), Position.nowhere)
        | _ -> Idpath (t, e)
      end

  | J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
    let t = subst_ty inst k t
    and u = subst_ty inst (k+3) u
    and e1 = subst_term inst (k+1) e1
    and e2 = subst_term inst k e2
    and e3 = subst_term inst k e3
    and e4 = subst_term inst k e4
    in
      begin match t, u, e1, e2, e3, e4 with
        | Ty t, Ty u, Term e1, Term e2, Term e3, Term e4 ->
          Term (Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4), Position.nowhere)
        | _ -> J (t, (x, y, p, u), (z, e1), e2, e3, e4)
      end

  | Refl (t, e) ->
    let t = subst_ty inst k t
    and e = subst_term inst k e
    in
      begin match t, e with
        | Ty t, Term e -> Term (Syntax.Refl (t, e), Position.nowhere)
        | _ -> Refl (t, e)
      end

  | Coerce (alpha, beta, e) ->
    let e = subst_term inst k e
    in
      begin match e with
        | Term e -> Term (Syntax.Coerce (alpha, beta, e), Position.nowhere)
        | _ -> Coerce (alpha, beta, e)
      end

  | NameProd (alpha, beta, x, e1, e2) ->
    let e1 = subst_term inst k e1
    and e2 = subst_term inst (k+1) e2
    in
      begin match e1, e2 with
        | Term e1, Term e2 ->
          Term (Syntax.NameProd (alpha, beta, x, e1, e2), Position.nowhere)
        | _ -> NameProd (alpha, beta, x, e1, e2)
      end

  | NamePaths (alpha, e1, e2, e3) ->
    let e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    and e3 = subst_term inst k e3
    in
      begin match e1, e2, e3 with
        | Term e1, Term e2, Term e3 ->
          Term (Syntax.NamePaths (alpha, e1, e2, e3), Position.nowhere)
        | _ -> NamePaths (alpha, e1, e2, e3)
      end

  | NameId (alpha, e1, e2, e3) ->
    let e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    and e3 = subst_term inst k e3
    in
      begin match e1, e2, e3 with
        | Term e1, Term e2, Term e3 ->
          Term (Syntax.NameId (alpha, e1, e2, e3), Position.nowhere)
        | _ -> NameId (alpha, e1, e2, e3)
      end

let rec shift_ty k l = function

  | Ty t -> Ty (Syntax.shift_ty ~bound:l k t)

  | El (alpha, e) ->
    let e = shift k l e in
      El (alpha, e)

  | Prod (x, t1, t2) ->
    let t1 = shift_ty k l t1
    and t2 = shift_ty k (l+1) t2
    in
      Prod (x, t1, t2)

  | Paths (t, e1, e2) ->
    let t = shift_ty k l t
    and e1 = shift k l e1
    and e2 = shift k l e2
    in
      Paths (t, e1, e2)

  | Id (t, e1, e2) ->
    let t = shift_ty k l t
    and e1 = shift k l e1
    and e2 = shift k l e2
    in
      Id (t, e1, e2)

and shift k l = function

  | Term e ->
    let e = Syntax.shift ~bound:l k e
    in
      Term e

  | PVar i ->
    PVar i

  | Lambda (x, t1, t2, e) ->
    let t1 = shift_ty k l t1
    and t2 = shift_ty k (l+1) t2
    and e = shift k l e
    in
      Lambda (x, t1, t2, e)

  | App ((x, t1, t2), e1, e2) ->
    let t1 = shift_ty k l t1
    and t2 = shift_ty k (l+1) t2
    and e1 = shift k l e1
    and e2 = shift k l e2
    in
      App ((x, t1, t2), e1, e2)

  | Idpath (t, e) ->
    let t = shift_ty k l t
    and e = shift k l e
    in
      Idpath (t, e)

  | J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
    let t = shift_ty k l t
    and u = shift_ty k (l+3) u
    and e1 = shift k (l+1) e1
    and e2 = shift k l e2
    and e3 = shift k l e3
    and e4 = shift k l e4
    in
      J (t, (x, y, p, u), (z, e1), e2, e3, e4)

  | Refl (t, e) ->
    let t = shift_ty k l t
    and e = shift k l e
    in
      Refl (t, e)

  | Coerce (alpha, beta, e) ->
    let e = shift k l e
    in
      Coerce (alpha, beta, e)

  | NameProd (alpha, beta, x, e1, e2) ->
    let e1 = shift k l e1
    and e2 = shift k (l+1) e2
    in
      NameProd (alpha, beta, x, e1, e2)

  | NamePaths (alpha, e1, e2, e3) ->
    let e1 = shift k l e1
    and e2 = shift k l e2
    and e3 = shift k l e3
    in
      NamePaths (alpha, e1, e2, e3)

  | NameId (alpha, e1, e2, e3) ->
    let e1 = shift k l e1
    and e2 = shift k l e2
    and e3 = shift k l e3
    in
      NameId (alpha, e1, e2, e3)


(**********)
(* Spines *)
(**********)

type ('y,'r) spine = head * ((name * 'y * 'y) * 'r) list

and head =
  | HVar of int   (* Brazil variable, not a pattern variable! *)
  | HNameProd of Universe.t * Universe.t
  | HNamePaths of Universe.t
  | HNameId of Universe.t
  | HCoerce of Universe.t * Universe.t
  | HRefl of Syntax.ty
  | HIdpath of Syntax.ty
  | HUnitTerm

let eq_head head1 head2 =
  match head1, head2 with
  | HVar n, HVar n' -> n = n'

  | HNameProd(alpha, beta), HNameProd(alpha',beta')
  | HCoerce(alpha, beta), HCoerce(alpha',beta') ->
      alpha = alpha' && beta = beta'

  | HNamePaths alpha, HNamePaths alpha'
  | HNameId alpha, HNameId alpha' ->
      alpha = alpha'

  | HRefl t, HRefl t'
  | HIdpath t, HIdpath t' -> Syntax.equal_ty t t'

  | HUnitTerm, HUnitTerm -> true

  | (HVar _ | HNameProd _ | HNamePaths _ | HNameId _
      | HCoerce _ | HRefl _ | HIdpath _
      | HUnitTerm ), _ -> false




let rec spine_of_syntax doTy doTerm ((term', _) as term) =
  let recur = spine_of_syntax doTy doTerm in
  match term' with
  | Syntax.Var v ->
      HVar v, []

  | Syntax.App ((x,t1,t2), e1, e2) ->
        let (h, args) = recur e1  in
        h, (args @ [(x,doTy t1,doTy t2), doTerm e2])

  | Syntax.Coerce(alpha, beta, e) ->
      HCoerce (alpha, beta),
      [("_", doTy (Syntax.mkUniverse alpha), doTy (Syntax.mkUniverse beta)), doTerm e]

  | Syntax.UnitTerm ->
      HUnitTerm, []

  | Syntax.NameId(alpha, e1, e2, e3) ->
      HNameId alpha,
      [("nameid-arg", doTy(Syntax.mkUniverse alpha),
        doTy(Syntax.make_arrow
             (Syntax.mkEl alpha (Syntax.mkVar 0))
             (Syntax.make_arrow
                (Syntax.mkEl alpha (Syntax.mkVar 0))
          (Syntax.mkUniverse alpha)))), doTerm e1;
       ("_", doTy (Syntax.mkEl alpha (Syntax.mkVar 0)),
             doTy (Syntax.make_arrow
                  (Syntax.mkEl alpha (Syntax.mkVar 1))
                  (Syntax.mkUniverse alpha))), doTerm e2;
       ("_", doTy (Syntax.mkEl alpha (Syntax.mkVar 1)),
                doTy (Syntax.mkUniverse alpha)), doTerm e3;
      ]

  | _ -> Error.unimplemented "need to finish spine_of_syntax %t"
                (Print.term []  term)


let rec spine_of_term = function
  | Term e -> spine_of_syntax (fun t -> Ty t) (fun e -> Term e) e

  | PVar i -> Error.unimplemented "Top-level pattern variable cannot be a spine"

  | Lambda _ -> Error.unimplemented "Top-level lambda cannot be a spine"

  | App ((x,t1,t2), p1, p2) ->
        let (h, args) = spine_of_term p1  in
        h, (args @ [(x,t1,t2), p2])

  | Idpath(Ty t, p) ->
      HIdpath t,
      [("idpath-arg", Ty t,
            Paths (Ty(Syntax.weaken_ty 0 t), Term (Syntax.mkVar 0), Term (Syntax.mkVar 0))),
       p]

  | Idpath _ ->
      Error.unimplemented "Top-level Idpath cannot have a pattern type"

  | J _ -> Error.unimplemented "Top-level J cannot be a spine"

  | Refl(Ty t, p) ->
      HRefl t,
      [("refl-arg", Ty t,
            Id (Ty(Syntax.weaken_ty 0 t), Term (Syntax.mkVar 0), Term (Syntax.mkVar 0))),
       p]

  | Refl _ ->
      Error.unimplemented "Top-level Refl cannot have a pattern type"

  | Coerce(alpha, beta, p) ->
      HCoerce (alpha, beta),
      [("_", Ty (Syntax.mkUniverse alpha), Ty(Syntax.mkUniverse beta)), p]

  | NameId(alpha, p1, p2, p3) ->
      HNameId alpha,
      [("nameid-arg", Ty(Syntax.mkUniverse alpha),
        Ty(Syntax.make_arrow
             (Syntax.mkEl alpha (Syntax.mkVar 0))
             (Syntax.make_arrow
                (Syntax.mkEl alpha (Syntax.mkVar 0))
          (Syntax.mkUniverse alpha)))), p1;
       ("_", Ty (Syntax.mkEl alpha (Syntax.mkVar 0)),
             Ty (Syntax.make_arrow
                  (Syntax.mkEl alpha (Syntax.mkVar 1))
                  (Syntax.mkUniverse alpha))), p2;
       ("_", Ty (Syntax.mkEl alpha (Syntax.mkVar 1)),
                Ty (Syntax.mkUniverse alpha)), p3;
      ]

  | _ -> Error.unimplemented "Need to finish names in spine_of_term"


let spine_of_brazil  = spine_of_syntax (fun t -> t) (fun e -> e)

let subst_pattern_args inst k =
  List.map
    (fun ((x,t1,t2),e) ->
      ((x, subst_ty inst k t1,
           subst_ty inst (k+1) t2),
           subst_term inst k e))

