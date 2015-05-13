type term =
  | PVar of Name.bound
  | Spine of term * (term * Tt.ty, Tt.ty) abstraction
  | Eq (ty, term, term)
  | Refl (ty, term)
  | Term of Tt.term * Tt.ty

and ty = Ty of term

type t = (Tt.ty, term) abstraction

(** Convert a term to a pattern. *)
let rec of_term pvars ((e',loc) as e) t =
  (** Attempt to remove x from a list. *)
  let rec remove_bound x = function
    | [] -> None
    | y :: ys ->
      if Name.eq x y
      then Some ys
      else (match remove_bound x ys with None -> None | Some ys -> Some (y :: ys))
  in
  let original = pvars, Term (e,t) in

  match e' with

  | Tt.Type | Tt.Name _ | Tt.Lambda _ | Tt.Prod _ -> original

  | Tt.Bound k ->
    begin match remove_bound k pvars with
      | None -> original
      | Some pvars -> pvars, PVar k
    end

  | Tt.Spine (e, (xets, u)) ->
    let rec fold pvars = function
      | [] -> pvars, true, []
      | (x,(e,t)) :: xets ->
        let t = (let (Tt.Ty (t, loc) = t in Ty (Term t, loc)) in
        let pvars, e = of_term pvars e t in
        let pvars, all_terms, xets = fold pvars xets in
        let all_terms = (match e with Term _ -> all_terms | _ -> false) in
        let xets = (x, (e, t)) :: xets in
           pvars, all_terms, xets
    in
    let pvars, e = of_term pvars e (Tt.mk_prod ~loc (List.map snd (fst xsts)) (snd xets)) in
    let pvars, all_terms, xets = fold pvars xets in
    begin match all_terms, e with
      | true, Term _ -> original
      | _, _ -> pvars, (Spine (e, (xets, u)))
    end

  | Tt.Eq (t, e1, e2) ->
    let pvars, t = of_ty pvars t in
    let pvars, e1 = of_term pvars e1 t in
    let pvars, e2 = of_term pvars e2 t in
    begin match t, e1, e2 with
      | Ty (Term _), Term _, Term _ -> original
      | _, _, _ -> pvars, (Eq (t, e1, e2), loc)
    end

  | Tt.Refl (t, e) ->
    let pvars, t = of_ty pvars t in
    let pvars, e = of_term pvars e t in
    begin match t, e with
      | Ty (Term _), Term _ -> original
      | _, _ -> pvars, (Refl (t, e), loc)
    end

and of_ty pvars (Tt.Ty t) = of_term pvars t Tt.typ


exception NoMatch

(** Match pattern [p] and expression [e] of type [t]. *)
let pmatch ctx (xts, p) e t =

  let rec collect p e t =
  match p with
    | PVar k -> [(k, (e, t)], []
    | Spine (pe, pxets) ->
      let loc = snd e in
      begin match Equal.as_spine ctx e with
        | Some (e, xets) ->
          let pvars_e, checks_e = collect pe e
          and pvars_xets, checks_xets = collect_spine ~loc pxets xets
          in pvars_e @ pvars_xets, checks_e @ checks_xets
        | None -> raise NoMatch
      end
    | Eq (pt, pe1, pe2) ->
      begin match Equal.as_eq ctx e with
        | Some (t, e1, e2) ->
          let pvars_t, checks_t = collect_ty pt t
          and pvars_e1, checks_e1 = collect pe1 e1
          and pvars_e2, checks_e2 = collect pe2 e2
          in pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2
        | None -> raise NoMatch
      end
    | Refl (pt, pe) ->
      begin match Equal.as_refl ctx e with
        | Some (t, e) ->
          let pvars_t, checks_t = collect_ty pt t
          and pvars_e, checks_e = collect pe e
          in pvars_t @ pvars_e, checks_t @ checks_e
        | None -> raise NoMatch
      end
    | Term (e',t') -> [], [(t, t', Ty.typ); (e',e,t)]

  and collect_ty (Ty p) (Tt.Ty e) = collect p e

  and collect_spine ~loc (pxets, u') (xets, u) =
    let rec fold xts' xts pxets xets =
      match pxets, xets with
      | [], [] ->
        let xts' = List.rev xts'
        and xts  = List.rev xts in
        let check_u = [(Tt.mk_prod ~loc xts' u', Tt.mk_prod ~loc xts u)]
        in [], check_u
      | (x',(pe,t'))::pxets, (x,(e,t))::xets ->
        let pvars_e, checks_e = collect pe e
        and pvars_xets, checks_xets = fold ((x',t)::xts') ((x,t)::xts) pxets xets
        in pvars_e @ pvars_xets, checks_e @ checks_xets
      | ([],_::_) | (_::_,[]) ->
        (** XXX be inteligent about differently nested but equally long spines *)
        raise NoMatch
    in
      fold [] [] pxets xets

  in

  let bind_pvars ctx k pvars xts =
    begin match pvars, xts with
      | [], [] -> ctx
      | (i,e)::pvars, (x,t)::xts ->
        if i = k
        then Context.add_bound x (e,t) ctx
        else raise NoMatch
    end



  let pvars, checks = collect p e in
  let pvars = List.sort (fun (i,_) (j,_) -> Pervasives.compare i j) pvars in
  let ctx = List.fold_left () (0, xts) ctx

