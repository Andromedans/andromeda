(** Pattern matching support for hints. *)

(** A type which is exactly like [Tt.ty] except that its bound
    variables refer to pattern variables instead of the ordinary
    bound variables. *)
type pty = Tt.ty

type pterm = Tt.term

(** The type of term patterns. *)
type term =
  | PVar of Syntax.bound
  | Name of Name.t
  | PrimApp of Name.t * term list
  | Spine of term * (pty, pty) Tt.abstraction * term list
  | Bracket of ty
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of pterm * pty

(** The type of type patterns. *)
and ty = Ty of term

(** A pattern is given as an abstraction of a term pattern *)
type t = (Tt.ty, term) Tt.abstraction

(** A beta hint is an abstracted term pattern and a term. We match against
    the pattern and rewrite into the term. *)
type beta_pattern =
  | BetaName of Name.t
  | BetaPrimApp of Name.t * term list
  | BetaSpine of term * (pty, pty) Tt.abstraction * term list

type beta_hint = (Tt.ty, beta_pattern * Tt.term) Tt.abstraction

(** An eta hint is an abstracted type pattern together with variables that match
    the lhs and rhs of an equation. *)
type eta_hint = (Tt.ty, ty * Syntax.bound * Syntax.bound) Tt.abstraction

(** A general hint is an abstracted triple of patterns that match the type and both
    sides of equation. *)
type general_hint = (Tt.ty, ty * term * term) Tt.abstraction

(** An inhabit hint is a universally quantified type. *)
type inhabit_hint = (Tt.ty, ty) Tt.abstraction

type hint_key =
  | Key_Type
  | Key_Name of Name.t
  | Key_PrimApp of Name.t
  | Key_Lambda
  | Key_Prod
  | Key_Eq
  | Key_Refl
  | Key_Inhab
  | Key_Bracket

let rec term_key (e',loc) =
  match e' with
  | Tt.Type -> Key_Type
  | Tt.Name x -> Key_Name x
  | Tt.Bound _ -> Error.impossible ~loc "De Bruijn index encountered in term_key"
  | Tt.PrimApp (x, _) -> Key_PrimApp x
  | Tt.Lambda _ -> Key_Lambda
  | Tt.Spine (e, _, _) -> term_key e
  | Tt.Prod _ -> Key_Prod
  | Tt.Eq _ -> Key_Eq
  | Tt.Refl _ -> Key_Refl
  | Tt.Inhab -> Key_Inhab
  | Tt.Bracket _ -> Key_Bracket

let ty_key (Tt.Ty t) = term_key t

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

      | PrimApp (x, []) ->
        Name.print x ppf

      | PrimApp (x, ((_::_) as es)) ->
        print ~at_level:1 "@[<hov 2>%t@ %t@]"
          (Name.print x)
          (Print.sequence (print_term ~max_level:0 xs) "" es)

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

let print_beta_hint ?max_level xs (yts, (pb, e)) ppf =
  let print_beta_body xs ppf =
    let p =
      begin match pb with
        | BetaSpine (pe, xts, pes) -> Spine (pe, xts, pes)
        | BetaPrimApp (x, pes) -> PrimApp (x, pes)
        | BetaName x -> Name x
      end
    in
    Print.print ppf "@ =>@ @[<hov 2>%t ~~>@ %t@]"
      (print_term xs p)
      (Tt.print_term xs e)
  in
  Print.print ?max_level ppf "@[%t@]" (Name.print_binders (Name.print_binder1 Tt.print_ty) print_beta_body xs yts)

let print_hint ?max_level xs (yts, (pt, pe1, pe2)) ppf =
  let print_body xs ppf =
    Print.print ppf "@ =>@ @[<hov 2>%t ==[%t] %t@]"
      (print_term xs pe1)
      (print_ty xs pt)
      (print_term xs pe2)
  in
  Print.print ?max_level ppf "@[%t@]" (Name.print_binders (Name.print_binder1 Tt.print_ty) print_body xs yts)

let print_eta_hint ?max_level xs (yts, (pt, k1, k2)) ppf =
  print_hint ?max_level xs (yts, (pt, PVar k1, PVar k2)) ppf

let print_inhabit_hint ?max_level xs (yts, pt) ppf =
  let print_body xs ppf =
    Print.print ppf "@ =>@ %t"
      (print_ty xs pt)
  in
  Print.print ?max_level ppf "@[%t@]"
    (Name.print_binders (Name.print_binder1 Tt.print_ty) print_body xs yts)

let print_pattern ?max_level xs (xts, p) ppf =
  Print.print ?max_level ppf "@[%t@]"
    (Name.print_binders
       (Name.print_binder1 Tt.print_ty)
       (fun xs ppf -> Print.print ppf "@ =>@ @[<hov 2>%t@]" (print_term xs p))
       xs xts)

