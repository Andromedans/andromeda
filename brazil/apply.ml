(* Try to instantiate a Pi type so that it matches a given type. *)

(* Count the depth of Pi's. *)
let rec pi_depth (t, _) =
  match t with
  | Syntax.Universe _ -> 0
  | Syntax.El _ -> 0
  | Syntax.Unit -> 0
  | Syntax.Prod (_, _, t) -> 1 + pi_depth t
  | Syntax.Paths _ -> 0
  | Syntax.Id _ -> 0

(* Strip the given number of Pi's from a term. *)
let rec strip k t =
  match k with
  | 0 -> t
  | k ->
    begin match fst t with
    | Syntax.Prod (_, _, t) -> strip (k-1) t
    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | 
      Syntax.Paths _ | Syntax.Id _ -> assert false
    end

exception Mismatch

let check b = if not b then raise Mismatch 

let rec match_ty k inst lvl (tprod, _) (t, _) =
  match tprod, t with

  | (Syntax.Universe alpha, Syntax.Universe beta) ->
    check (Universe.eq alpha beta) ;
    inst

  | Syntax.El (alpha, e1), Syntax.El (beta, e2) ->
    check (Universe.eq alpha beta) ;
    match_term k inst lvl e1 e2

  | Syntax.Unit, Syntax.Unit -> inst

  | Syntax.Prod (_, t1, t2), Syntax.Prod (_, t1', t2') ->
     let inst = match_ty k inst lvl t1 t1' in
       match_ty k inst (lvl+1) t2 t2'

  | Syntax.Paths (t, e1, e2), Syntax.Paths (t', e1', e2') ->
     let inst = match_ty k inst lvl t t' in
     let inst = match_term k inst lvl e1 e1' in
       match_term k inst lvl e2 e2'

  | Syntax.Id (t, e1, e2), Syntax.Id (t', e1', e2') ->
     let inst = match_ty k inst lvl t t' in
     let inst = match_term k inst lvl e1 e1' in
       match_term k inst lvl e2 e2'

  | (Syntax.Prod _ | Syntax.Universe _ | Syntax.El _ |
     Syntax.Unit | Syntax.Paths _| Syntax.Id _), _ ->
    raise Mismatch

and match_term k inst lvl e_pttrn e =
  match fst e_pttrn, fst e with
    (* NB: the order of cases matters. *)

    | Syntax.Advice (_, _, e1), _ -> match_term k inst lvl e1 e
    | _, Syntax.Advice (_, _, e2) -> match_term k inst lvl e_pttrn e2

    | Syntax.Equation (_, _, e1), _ -> match_term k inst lvl e1 e
    | _, Syntax.Equation (_, _, e2) -> match_term k inst lvl e_pttrn e2

    | Syntax.Rewrite (_, _, e1), _ -> match_term k inst lvl e1 e
    | _, Syntax.Rewrite (_, _, e2) -> match_term k inst lvl e_pttrn e2

    | (Syntax.Var i, _) when (0 <= i - lvl && i - lvl < k) ->
      begin
        let i = i - lvl in
        let rec lookup x = function
          | [] -> None
          | (x',y)::lst -> if x = x' then Some y else lookup x lst
        in
        let e = Syntax.shift ~exn:Mismatch (-lvl) e in
          match lookup i inst with
          | Some e' -> if Syntax.equal e' e then inst else raise Mismatch
          | None -> (i, e) :: inst
      end

    | Syntax.Var i, Syntax.Var j -> check (i = j) ; inst

    | Syntax.Ascribe (e, t), Syntax.Ascribe (e', t') ->
      let inst = match_term k inst lvl e e' in
        match_ty k inst lvl t t'

    | Syntax.Lambda (_, t, u, e), Syntax.Lambda (_, t', u', e') ->
      let inst = match_ty k inst lvl t t' in
      let inst = match_ty k inst (lvl+1) u u' in
        match_term k inst (lvl+1) e e'

    | Syntax.App ((_, t1, t2), e1, e2), Syntax.App ((_, t1', t2'), e1', e2') ->
      let inst = match_ty k inst lvl t1 t1' in
      let inst = match_ty (k+1) inst lvl t2 t2' in
      let inst = match_term k inst lvl e1 e1' in
        match_term k inst lvl e2 e2'

    | Syntax.UnitTerm, Syntax.UnitTerm -> inst

    | Syntax.Idpath (t, e), Syntax.Idpath (t', e') ->
      let inst = match_ty k inst lvl t t' in
        match_term k inst lvl e e'

    | (Syntax.J (t, (_, _, _, u), (_, e1), e2, e3, e4),
       Syntax.J (t', (_, _, _, u'), (_, e1'), e2', e3', e4')) ->
      let inst = match_ty k inst lvl t t' in
      let inst = match_ty (k+3) inst lvl u u' in
      let inst = match_term (k+1) inst lvl e1 e1' in
      let inst = match_term k inst lvl e2 e2' in
      let inst = match_term k inst lvl e3 e3' in
        match_term k inst lvl e4 e4'

    | Syntax.Refl (t, e), Syntax.Refl (t', e') ->
      let inst = match_ty k inst lvl t t' in
        match_term k inst lvl e e'

    | Syntax.Coerce (alpha, beta, e), Syntax.Coerce (alpha', beta', e') ->
      check (Universe.eq alpha alpha' ) ;
      check (Universe.eq beta beta' ) ;
      match_term k inst lvl e e'

    | Syntax.NameUnit, Syntax.NameUnit -> inst

    | Syntax.NameProd (alpha, beta, _, e1, e2),
      Syntax.NameProd (alpha', beta', _, e1', e2') ->
      check (Universe.eq alpha alpha') ;
      check (Universe.eq beta beta') ;
      let inst = match_term k inst lvl e1 e1 in
        match_term k inst (lvl+1) e2 e2'

    | Syntax.NameUniverse alpha, Syntax.NameUniverse beta -> 
      check (Universe.eq alpha beta) ; inst

    | Syntax.NamePaths (alpha, e1, e2, e3), Syntax.NameId (beta, e1', e2', e3') ->
      check (Universe.eq alpha beta) ;
      let inst = match_term k inst lvl e1 e1' in
      let inst = match_term k inst lvl e2 e2' in
        match_term k inst lvl e3 e3'

    | Syntax.NameId (alpha, e1, e2, e3), Syntax.NameId (beta, e1', e2', e3') ->
      check (Universe.eq alpha beta) ;
      let inst = match_term k inst lvl e1 e1' in
      let inst = match_term k inst lvl e2 e2' in
        match_term k inst lvl e3 e3'

    | (Syntax.Var _ | Syntax.Ascribe _ | Syntax.Lambda _ | Syntax.App _ | Syntax.UnitTerm | 
       Syntax.Idpath _ | Syntax.J _ | Syntax.Refl _ | Syntax.Coerce _ | Syntax.NameUnit |
       Syntax.NameProd _ | Syntax.NameUniverse _ | Syntax.NamePaths _ | Syntax.NameId _ ), _ ->
      raise Mismatch
     
let apply tprod t =
  let tprod = Norm.norm_ty tprod in
  let t = Norm.norm_ty t in
  (* Compute the number of variables that need to be instantiated. *)
  let k = pi_depth tprod - pi_depth t in
    if k < 0 then None
    else
      let t = Syntax.shift_ty k t in
      let tprod = strip k tprod in
        try
          (* compute an instance *)
          let inst = match_ty k [] 0 tprod t in
           (* compute the list of terms than should be applied *)
          let rec compute j =
            if j >= k then []
            else (List.assoc j inst) :: compute (j + 1)
          in
            Some (compute 0)
        with
        | Mismatch -> None
