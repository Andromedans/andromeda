(** The type of term patterns. *)
type term =
  | PVar of Syntax.bound
  | Name of Name.t
  | Spine of term * (Tt.ty, Tt.ty) Tt.abstraction * term list
  | Bracket of ty
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of Tt.term * Tt.ty

(** The type of type patterns. *)
and ty = Ty of term

(** A pattern is given as an abstraction of a term pattern *)
type t = (Tt.ty, term) Tt.abstraction

type beta_hint = Name.t * (Tt.ty, term * Tt.term) Tt.abstraction

type eta_hint = Name.t * (Tt.ty, ty * Syntax.bound * Syntax.bound) Tt.abstraction

type hint = Name.t * (Tt.ty, ty * term * term) Tt.abstraction

type inhabit = (Tt.ty, ty) Tt.abstraction

(** Attempt to remove [x] from list [xs]. *)
let rec remove_bound x xs =
  match xs with
  | [] -> None
  | y :: ys ->
    if x = y
    then Some ys
    else (match remove_bound x ys with None -> None | Some ys -> Some (y :: ys))

(** The name in the head position of a pattern *)
let rec head_name = function
  | Name x -> Some x
  | Spine (e, _, _) -> head_name e
  | PVar _ | Eq _ | Refl _ | Bracket _ | Term _ -> None

(** Convert a term [e] of type [t] to a pattern with respect to the
    given bound variables [pvars]. That is, the bound variables from [pvars]
    are treated as pattern variables. Return the list of those [pvars] that
    were not encoutered, and the pattern generated. *)
let rec of_term pvars ((e',loc) as e) t =
  let original = pvars, Term (e,t) in
  match e' with

  | Tt.Type | Tt.Inhab | Tt.Lambda _ | Tt.Prod _ -> original

  | Tt.Name x -> pvars, Name x

  | Tt.Bound k ->
    begin match remove_bound k pvars with
      | None -> original
      | Some pvars -> pvars, PVar k
    end

  | Tt.Spine (e, (xts, u), es) ->
    let rec fold pvars all_terms args_so_far ps xts args_left =
      match xts, args_left with
      | [], [] -> pvars, all_terms, List.rev ps
      | (x, t) :: xts, e :: args_left ->
        let t = Tt.instantiate_ty args_so_far 0 t in
        let pvars, p = of_term pvars e t in
        let all_terms = (match p with Term _ -> all_terms | _ -> false) in
        fold pvars all_terms (e::args_so_far) (p::ps) xts args_left
      | ([],_::_) | (_::_,[]) ->
        Error.impossible ~loc "malformed spine in Pattern.of_term"
    in

    let pvars, e = of_term pvars e (Tt.mk_prod_ty ~loc xts u) in
    let pvars, all_terms, es = fold pvars true [] [] xts es in
    (* if [name_of_term] came back then e is a name and thus a Tt.term *)
    begin if all_terms
      then original
      else pvars, Spine (e, (xts, u), es)
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

  | Tt.Bracket t ->
    let pvars, t = of_ty pvars t in
    begin match t with
      | Ty (Term _) -> original
      | _ -> pvars, (Bracket t)
    end

and of_ty pvars (Tt.Ty t) =
  let pvars, t = of_term pvars t Tt.typ in
  pvars, (Ty t)

let rec print_term ?max_level xs e ppf =
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

      | Name x ->
        (* XXX check this *)
        Name.print x ppf

      | Spine (e, xts, es) ->
        print ~at_level:1 "@[<hov 2>%t@ %t@]"
          (print_term ~max_level:0 xs e)
          (Print.sequence (print_term ~max_level:0 xs) "" es)

      | Eq (t, e1, e2) ->
        print ~at_level:2 "@[<hv 2>%t@ ==%t %t@]"
          (print_term ~max_level:1 xs e1)
          (print_ty xs t)
          (print_term ~max_level:1 xs e2)

      | Refl (t, e) ->
        print ~at_level:1 "refl%t %t"
          (print_ty xs t)
          (print_term ~max_level:0 xs e)

      | Bracket t ->
        print "[%t]" (print_ty xs t)

and print_ty ?max_level xs (Ty t) ppf = print_term ?max_level xs t ppf

let print_beta_hint ?max_level xs (_, (yts, (p, e))) ppf =
  let print_beta_body xs ppf =
    Print.print ppf "@ =>@ @[<hov 2>%t ~~>@ %t@]"
      (print_term xs p)
      (Tt.print_term xs e)
  in
  Print.print ?max_level ppf "@[%t@]" (Name.print_binders Tt.print_ty print_beta_body xs yts)

let print_hint ?max_level xs (_, (yts, (pt, pe1, pe2))) ppf =
  let print_body xs ppf =
    Print.print ppf "@ =>@ @[<hov 2>%t ==[%t] %t@]"
      (print_term xs pe1)
      (print_ty xs pt)
      (print_term xs pe2)
  in
  Print.print ?max_level ppf "@[%t@]" (Name.print_binders Tt.print_ty print_body xs yts)

let print_eta_hint ?max_level xs (h, (yts, (pt, k1, k2))) ppf =
  print_hint ?max_level xs (h, (yts, (pt, PVar k1, PVar k2))) ppf

let print_inhabit_hint ?max_level xs (yts, pt) ppf =
  let print_body xs ppf =
    Print.print ppf "@ =>@ %t"
      (print_ty xs pt)
  in
  Print.print ?max_level ppf "@[%t@]"
    (Name.print_binders Tt.print_ty print_body xs yts)

let print_pattern ?max_level xs (xts, p) ppf =
  Print.print ?max_level ppf "@[%t@]"
    (Name.print_binders
       Tt.print_ty
       (fun xs ppf -> Print.print ppf "@ =>@ @[<hov 2>%t@]" (print_term xs p))
       xs xts)

(** given an abstraction [xts] with [n] elements, return the list [[0,...,{n-1}]]. *)
let pvars_of_binders xts =
  snd (List.fold_left (fun (k, pvars) _ -> (k+1), k :: pvars) (0, []) xts)

let make_beta_hint ~loc (xts, (t, e1, e2)) =
  let pvars = pvars_of_binders xts in
  let pvars, p = of_term pvars e1 t in
    match pvars with
      | [] ->
        begin match head_name p with
          | Some x -> x, (xts, (p, e2))
          | None -> Error.runtime ~loc
              "the left-hand side of a beta hint must be a symbol@ or a symbol applied to arguments"
        end
      | _ :: _ ->
        let xs = List.map (fun k -> fst (List.nth xts k)) pvars in
        Error.runtime ~loc "this beta hint leaves some variables unmatched (%t)"
          (Print.sequence Name.print ", " xs)

let make_eta_hint ~loc (xts, (t, e1, e2)) =
  let pvars = pvars_of_binders xts in
  (** We should *first* turn [e1] and [e2] into patterns and only then [t]
      in case [e1] or [e2] is [pvar] which also appears in [t]. This is so because
      we want [e1] and [e2] to be distinct pattern variables.
   *)
  let pvars, p1 = of_term pvars e1 t in
  let pvars, p2 = of_term pvars e2 t in
  let pvars, ((Ty pt') as pt) = of_ty pvars t in
  match head_name pt', p1, p2 with
    | Some x, PVar k1, PVar k2 when k1 <> k2 -> x, (xts, (pt, k1, k2))
    | None, _, _ ->
        Error.runtime ~loc
          "the type of an eta hint must be a symbol@ or a symbol applied to arguments"
    | Some _, _, _ ->
        Error.runtime ~loc
          "the left- and right-hand side of an eta hint must be distinct variables"

let make_hint ~loc (xts, (t, e1, e2)) =
  let pvars = pvars_of_binders xts in
  let pvars, ((Ty pt') as pt) = of_ty pvars t in
  let pvars, pe1 = of_term pvars e1 t in
  let pvars, pe2 = of_term pvars e2 t in
  match head_name pt' with
    | Some x -> x, (xts, (pt, pe1, pe2))
    | None ->
        Error.runtime ~loc
          "the type of a hint must be a symbol@ or a symbol applied to arguments"

let make_inhabit ~loc (xts, t) =
  let pvars = pvars_of_binders xts in
  let pvars, ((Ty pt') as pt) = of_ty pvars t in
    (xts, pt)
