
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

type beta_hint = (Tt.ty, term * Tt.term) Tt.abstraction

type eta_hint = unit

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
  let pvars, t = of_term pvars t Tt.typ in
  pvars, (Ty t)

let rec print_term ?max_level (xs : Name.t list) e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
    match e with
      | Term (e, t) -> Tt.print_term ?max_level xs e ppf

      | PVar k ->
        begin
          try
            print ~at_level:0 "?%t" (Name.print (List.nth xs k))
          with
          | Not_found | Failure "nth" ->
              (** XXX this should never get printed *)
              print ~at_level:0 "?DEBRUIJN[%d]" k
        end

      | Spine (e, a) -> print ~at_level:1 "%t" (print_spine xs e a)

      | Eq (t, e1, e2) ->
        print ~at_level:2 "@[<hv 2>%t@ ==%t %t@]"
          (print_term ~max_level:1 xs e1)
          (print_ty xs t)
          (print_term ~max_level:1 xs e2)

      | Refl (t, e) ->
        print ~at_level:1 "refl%t %t"
          (print_ty xs t)
          (print_term ~max_level:0 xs e)

and print_ty ?max_level xs (Ty t) ppf = print_term ?max_level xs t ppf

and print_spine xs e (yets, u) ppf =
  let rec print_args ys yets ppf =
    match yets with
    | [] -> Print.print ppf ""
    | (y,(e,_)) :: yets ->
      let y = Name.refresh ys y in
      Print.print ppf "@ %t%t"
        (print_term ~max_level:0 ys e)
        (print_args (y::ys) yets)
  in
    Print.print ppf "@[<hov 2>%t%t@]"
      (print_term ~max_level:0 xs e)
      (print_args xs yets)

let print_beta_hint ?max_level xs (yts, (p, e)) ppf =
  let print_beta_body xs ppf =
    Print.print ppf "@ =>@ @[<hov 2>%t ~~>@ %t@]"
      (print_term xs p)
      (Tt.print_term xs e)
  in
  Print.print ?max_level ppf "@[%t@]" (Name.print_binders Tt.print_ty print_beta_body xs yts)

let print_pattern ?max_level xs (xts, p) ppf =
  Print.print ?max_level ppf "@[%t@]"
    (Name.print_binders
       Tt.print_ty
       (fun xs ppf -> Print.print ppf "@ =>@ @[<hov 2>%t@]" (print_term xs p))
       xs xts)

let make (xts, (e, t)) =
  let _, pvars = List.fold_left (fun (k, pvars) _ -> (k+1), k :: pvars) (0, []) xts in
  let pvars, p = of_term pvars e t in
  let e = Tt.mk_lambda ~loc:Location.unknown xts e t in
    Print.debug "Created pattern %t from abstraction %t"
      (print_pattern [] (xts, p))
      (Tt.print_term [] e) ;
    pvars, p

let make_beta_hint ~loc (xts, (t, e1, e2)) =
  let pvars, p = make (xts, (e1, t)) in
    match pvars with
      | [] -> (xts, (p, e2))
      | _ :: _ ->
        let xs = List.map (fun k -> fst (List.nth xts k)) pvars in
        Error.runtime ~loc "the beta hint@\n@[%t@]@\nnever matches bound variables %t"
          (print_beta_hint [] (xts, (p, e2)))
          (Print.sequence Name.print ", " xs)
