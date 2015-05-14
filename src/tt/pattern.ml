(** The type of term patterns. *)
type term =
  | PVar of Syntax.bound
  | Spine of term * (term * Tt.ty, Tt.ty) Tt.abstraction
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of Tt.term * Tt.ty

(** The type of type patterns. *)
and ty = PTy of term

(** A pattern is given as an abstraction of a term pattern *)
type t = (Tt.ty, term) Tt.abstraction

(** A check is a postponed equality check. *)
type check =
  | CheckEqual of Tt.term * Tt.term * Tt.ty
  | CheckEqualTy of Tt.ty * Tt.ty


(** Attempt to remove x from a list. *)
let rec remove_bound x = function
  | [] -> None
  | y :: ys ->
    if x = y
    then Some ys
    else (match remove_bound x ys with None -> None | Some ys -> Some (y :: ys))

(** Convert a term [e] of type [t] to a pattern with respect to the
    given bound variables [pvars]. *)
let rec of_term pvars ((e',loc) as e) t =

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
      | (x, (e, t)) :: xets ->
        let pvars, e = of_term pvars e t in
        let pvars, all_terms, xets = fold pvars xets in
        let all_terms = (match e with Term _ -> all_terms | _ -> false) in
        let xets = (x, (e, t)) :: xets in
        pvars, all_terms, xets
    in

    let xts = List.map (fun (x, (_, t)) -> x, t) xets in
    let pvars, e = of_term pvars e (Tt.ty (Tt.mk_prod ~loc xts u)) in
    let pvars, all_terms, xets = fold pvars xets in
    begin match all_terms, e with
      | true, Term _ -> original
      | _, _ -> pvars, (Spine (e, (xets, u)))
    end

  | Tt.Eq (t, e1, e2) ->
    let pvars, t' = of_ty pvars t in
    let pvars, e1 = of_term pvars e1 t in
    let pvars, e2 = of_term pvars e2 t in
    begin match t', e1, e2 with
      | PTy (Term _), Term _, Term _ -> original
      | PTy _, _, _ -> pvars, (Eq (t', e1, e2))
    end

  | Tt.Refl (t, e) ->
    let pvars, t' = of_ty pvars t in
    let pvars, e = of_term pvars e t in
    begin match t', e with
      | PTy (Term _), Term _ -> original
      | _, _ -> pvars, (Refl (t', e))
    end

and of_ty pvars (Tt.Ty t) : Syntax.bound list * ty =
  let s, t = of_term pvars t Tt.typ in s, (PTy t)

let make (xts, (e, t)) =
  let _, pvars = List.fold_left (fun (k, pvars) _ -> (k+1), k :: pvars) (0, []) xts in
  let pvars, p = of_term pvars e t in
    pvars, (xts, p)


exception NoMatch

(** Match pattern [p] and expression [e] which has a type.
    The type may or may not be given. *)
let pmatch ctx (xts, p) ?t e =

  let rec collect p ?t e =
    match p with
    (* [PVar]s need to be tagged with a type because*)
    | PVar k ->
    (* The type [t'] is the type given to the variable [k] in the binders [xts] and may be different from
       the type, say [t''], as a subterm in [p]. However, since [PVar] cannot appear under any binders,
       [t'] and [t''] are provably equal in the context of [xts]. Thus, we can compare the given type [t] to any one of them. *)
      begin match t with
      | Some t -> [(k, (e, t'))], [CheckEqualTy (t', t)]
      | None -> raise NoMatch
      end
    | Spine (pe, (pxets, u')) ->
      let loc = snd e in
      begin match Equal.as_spine ctx e with
        | Some (e, (xets, u)) ->
          let xts = List.map (fun (x, (_, t)) -> x, t) xets in
          let pvars_e, checks_e = collect pe e (Tt.ty (Tt.mk_prod ~loc xts u))
          and pvars_xets, checks_xets = collect_spine ~loc (pxets, u') (xets, u) in
          pvars_e @ pvars_xets, checks_e @ checks_xets
        | None -> raise NoMatch
      end
    | Eq (pt, pe1, pe2) ->
      begin match Equal.as_eq ctx e with
        | Some (t, e1, e2) ->
          let pvars_t, checks_t = collect_ty pt t
          and pvars_e1, checks_e1 = collect pe1 e1 t
          and pvars_e2, checks_e2 = collect pe2 e2 t
          in pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2
        | None -> raise NoMatch
      end
    | Refl (pt, pe) ->
      begin match Equal.as_refl ctx e with
        | Some (t, e) ->
          let pvars_t, checks_t = collect_ty pt t
          and pvars_e, checks_e = collect pe e t
          in pvars_t @ pvars_e, checks_t @ checks_e
        | None -> raise NoMatch
      end
    | Term (e',t') -> [], [CheckEqualTy (t, t'); CheckEqual (e', e, t)]

  and collect_ty (PTy p) (Tt.Ty e) = collect p e Tt.typ

  and collect_spine ~loc (pxets, u') (xets, u) =
    let rec fold xts' xts es pxets xets =
      match pxets, xets with
      | [], [] ->
        let xts' = List.rev xts'
        and xts  = List.rev xts in
        let check_u = [CheckEqualTy (Tt.mk_prod_ty ~loc xts' u', Tt.mk_prod_ty ~loc xts u)]
        in [], check_u
      | (x',(pe,t'))::pxets, (x,(e,t))::xets ->
        let pvars_e, checks_e = collect pe e (Tt.instantiate_ty es 0 t)
        and pvars_xets, checks_xets = fold ((x',t)::xts') ((x,t)::xts) (e::es) pxets xets
        in pvars_e @ pvars_xets, checks_e @ checks_xets
      | ([],_::_) | (_::_,[]) ->
        (** XXX be inteligent about differently nested but equally long spines *)
        raise NoMatch
    in
    fold [] [] [] pxets xets

  in

  let rec bind_pvars ctx k pvars xts =
    begin match pvars, xts with
      | [], [] -> ctx
      | (i,(e,t))::pvars, (x,t')::xts ->
        if i <> k then raise NoMatch else
        begin
          let ctx = Context.add_bound x (e,t) ctx in
          bind_pvars ctx (k+1) pvars xts
        end
      | ([],_::_) | (_::_,[]) -> raise NoMatch
    end
  in

  try
    let pvars, checks = collect p e t in
    let pvars = List.sort (fun (i,_) (j,_) -> Pervasives.compare i j) pvars in
    let ctx = bind_pvars ctx 0 pvars xts in
    List.iter
      (function
        | CheckEqual (e1, e2, t) -> if not (Equal.equal ctx e1 e2 t) then raise NoMatch
        | CheckEqualTy (t1, t2) -> if not (Equal.equal_ty ctx t1 t2) then raise NoMatch)
      checks ;
    Some ctx
  with NoMatch -> None
