(** Prepare a type so that it can be stored as a hint. *)
let prepare t =
  (* Strip outer Pi's from a type, report how many were stripped and what was left. *)
  let decompose t =
    let rec strip k t =
      match fst t with
    | Syntax.Prod (_, _, t) -> strip (k + 1) t
    | (Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Paths _ | Syntax.Id _) ->
      (k, t)
    in
      strip 0 t
  in
  let t = Norm.ty t in
  let k, t = decompose t in
    match fst t with
      | Syntax.Id (t, e1, e2) -> Some (k, t, e1, e2)
      | (Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Paths _ | Syntax.Prod _) ->
        None

(** Auxiliary stuff *)
exception Mismatch of string

let check b msg = if not b then raise (Mismatch msg)

let to_instantiation k lst =
  let rec scan j =
    if j >= k then []
    else
      try
        (List.assoc j lst) :: scan (j + 1)
      with
        | Not_found -> raise (Mismatch "partial instantiation")
  in
    scan 0

(* Instantiate variables [0] through [k-1], current instantiation is [inst],
   [lvl] is current depth of nesting in binders. 

   NB: We are matchin [tprod] against [t], where [tprod] is shifted by [k]
   with respect to [t]! Be extra-careful when comparing indices.
*)
let rec match_ty k inst lvl (tprod, _) (t, _) =
  match tprod, t with
      
    | (Syntax.Universe alpha, Syntax.Universe beta) ->
      check (Universe.eq alpha beta) "Universe index compare";
      inst
        
    | Syntax.El (alpha, e1), Syntax.El (beta, e2) ->
      check (Universe.eq alpha beta) "El index compare";
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
      raise (Mismatch "match_ty k: different heads")
        
and match_term k inst lvl e_pttrn e =
  match fst e_pttrn, fst e with
      (* NB: the order of cases matters. *)

    | Syntax.Equation (_, _, e1), _ -> match_term k inst lvl e1 e
    | _, Syntax.Equation (_, _, e2) -> match_term k inst lvl e_pttrn e2
      
    | Syntax.Rewrite (_, _, e1), _ -> match_term k inst lvl e1 e
    | _, Syntax.Rewrite (_, _, e2) -> match_term k inst lvl e_pttrn e2
      
    | (Syntax.Var i, _) when (0 <= i - lvl && i - lvl < k) ->
      begin
        Print.debug "match_term k: trying to match variable %d (k = %d, lvl = %d)" i k lvl ;
        let i = i - lvl in
        let rec lookup x = function
          | [] -> None
          | (x',y)::lst -> if x = x' then Some y else lookup x lst
        in
        let e = Syntax.shift ~exn:(Mismatch "negative shift") (-lvl) e in
          match lookup i inst with
            | Some e' -> if Syntax.equal e' e then inst else raise (Mismatch "variable already set")
            | None -> 
              Print.debug "match_term k: instantiated variable %d" i ;
              (i, e) :: inst
      end

    | Syntax.Var i, Syntax.Var j ->
      check (i = j + k) "Var DeBruijn compare";
      inst

    | Syntax.Ascribe (e, t), Syntax.Ascribe (e', t') ->
      let inst = match_term k inst lvl e e' in
        match_ty k inst lvl t t'

    | Syntax.Lambda (_, t, u, e), Syntax.Lambda (_, t', u', e') ->
      let inst = match_ty k inst lvl t t' in
      let inst = match_ty k inst (lvl+1) u u' in
        match_term k inst (lvl+1) e e'

    | Syntax.App ((_, t1, t2), e1, e2), Syntax.App ((_, t1', t2'), e1', e2') ->
      let inst = match_ty k inst lvl t1 t1' in
      let inst = match_ty k inst (lvl+1) t2 t2' in
      let inst = match_term k inst lvl e1 e1' in
        match_term k inst lvl e2 e2'

    | Syntax.UnitTerm, Syntax.UnitTerm -> inst

    | Syntax.Idpath (t, e), Syntax.Idpath (t', e') ->
      let inst = match_ty k inst lvl t t' in
        match_term k inst lvl e e'

    | (Syntax.J (t, (_, _, _, u), (_, e1), e2, e3, e4),
       Syntax.J (t', (_, _, _, u'), (_, e1'), e2', e3', e4')) ->
      let inst = match_ty k inst lvl t t' in
      let inst = match_ty k inst (lvl+3) u u' in
      let inst = match_term k inst (lvl+1) e1 e1' in
      let inst = match_term k inst lvl e2 e2' in
      let inst = match_term k inst lvl e3 e3' in
        match_term k inst lvl e4 e4'

    | Syntax.Refl (t, e), Syntax.Refl (t', e') ->
      let inst = match_ty k inst lvl t t' in
        match_term k inst lvl e e'

    | Syntax.Coerce (alpha, beta, e), Syntax.Coerce (alpha', beta', e') ->
      check (Universe.eq alpha alpha') "Coerce alpha compare" ;
      check (Universe.eq beta beta') "Coerece beta compare" ; 
      match_term k inst lvl e e'

    | Syntax.NameUnit, Syntax.NameUnit -> inst

    | Syntax.NameProd (alpha, beta, _, e1, e2),
      Syntax.NameProd (alpha', beta', _, e1', e2') ->
      check (Universe.eq alpha alpha') "NameProd alpha compare";
        check (Universe.eq beta beta') "NameProd beta compare";
        let inst = match_term k inst lvl e1 e1 in
          match_term k inst (lvl+1) e2 e2'

    | Syntax.NameUniverse alpha, Syntax.NameUniverse beta -> 
      check (Universe.eq alpha beta) "NameUniverse index compare";
      inst

    | Syntax.NamePaths (alpha, e1, e2, e3), Syntax.NameId (beta, e1', e2', e3') ->
      check (Universe.eq alpha beta) "NamePaths index compare";
      let inst = match_term k inst lvl e1 e1' in
      let inst = match_term k inst lvl e2 e2' in
        match_term k inst lvl e3 e3'

    | Syntax.NameId (alpha, e1, e2, e3), Syntax.NameId (beta, e1', e2', e3') ->
      check (Universe.eq alpha beta) "NameId index compare";
      let inst = match_term k inst lvl e1 e1' in
      let inst = match_term k inst lvl e2 e2' in
        match_term k inst lvl e3 e3'

    | (Syntax.Var _ | Syntax.Ascribe _ | Syntax.Lambda _ | Syntax.App _ | Syntax.UnitTerm | 
        Syntax.Idpath _ | Syntax.J _ | Syntax.Refl _ | Syntax.Coerce _ | Syntax.NameUnit |
            Syntax.NameProd _ | Syntax.NameUniverse _ | Syntax.NamePaths _ | Syntax.NameId _ ), _ ->
      raise (Mismatch "match: different heads")

(** Instantiate a hint against an equation. *)
let instantiate (k, t, e1, e2) t' e1' e2' =
  try
    let inst = match_ty k [] 0 t t' in
    let inst = match_term k inst 0 e1 e1' in
    let inst = match_term k inst 0 e2 e2' in
      for j = 0 to k - 1 do
        check (List.mem_assoc j inst) "missing instantiation"
      done ;
      true
  with
    | Mismatch msg ->
      Print.debug "hint mistmatch: %s" msg ;
      false

let rewrite (k, t, e1, e2) t' e1' =
  try
    let inst = match_ty k [] 0 t t' in
    let inst = match_term k inst 0 e1 e1' in
    let e2' = Syntax.strengthen e2 (to_instantiation k inst) in
      Some e2'      
  with
    | Mismatch msg ->
      Print.debug "hint mistmatch: %s" msg ;
      None

