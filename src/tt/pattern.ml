(** The type of term patterns. *)
type term =
  | PVar of Syntax.bound
  | Spine of term * (term * Tt.ty, Tt.ty) Tt.abstraction
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of Tt.term * Tt.ty

(** The type of type patterns. *)
and ty = Ty of term

(** A pattern is given as an abstraction of a term pattern *)
type t = (Tt.ty, term) Tt.abstraction

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
      | Ty (Term _), Term _, Term _ -> original
      | Ty _, _, _ -> pvars, (Eq (t', e1, e2))
    end

  | Tt.Refl (t, e) ->
    let pvars, t' = of_ty pvars t in
    let pvars, e = of_term pvars e t in
    begin match t', e with
      | Ty (Term _), Term _ -> original
      | _, _ -> pvars, (Refl (t', e))
    end

and of_ty pvars (Tt.Ty t) : Syntax.bound list * ty =
  let s, t = of_term pvars t Tt.typ in s, (Ty t)

let make (xts, (e, t)) =
  let _, pvars = List.fold_left (fun (k, pvars) _ -> (k+1), k :: pvars) (0, []) xts in
  let pvars, p = of_term pvars e t in
    pvars, (xts, p)
