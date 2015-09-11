(** Pattern matching support for hints. *)

(** A type which is exactly like [Tt.ty] except that its bound
    variables refer to pattern variables instead of the ordinary
    bound variables. *)
type pty = Tt.ty

type pterm = Tt.term

(** The type of term patterns. *)
type term =
  | PVar of Syntax.bound
  | Atom of Name.atom
  | Constant of Name.ident * term list
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
  | BetaAtom of Name.atom
  | BetaConstant of Name.ident * term list
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
  | Key_Constant of Name.ident
  | Key_Atom of Name.atom
  | Key_Lambda
  | Key_Prod
  | Key_Eq
  | Key_Refl
  | Key_Inhab
  | Key_Bracket

let rec term_key_opt (e',loc) =
  match e' with
  | Tt.Type -> Some Key_Type
  | Tt.Atom x -> Some (Key_Atom x)
  | Tt.Bound _ -> None
  | Tt.Constant (x, _) -> Some (Key_Constant x)
  | Tt.Lambda _ -> Some Key_Lambda
  | Tt.Spine (e, _, _) -> term_key_opt e
  | Tt.Prod _ -> Some Key_Prod
  | Tt.Eq _ -> Some Key_Eq
  | Tt.Refl _ -> Some Key_Refl
  | Tt.Inhab -> Some Key_Inhab
  | Tt.Bracket _ -> Some Key_Bracket

let term_key e =
  match term_key_opt e with
  | Some k -> k
  | None -> Error.impossible ~loc:(snd e) "De Bruijn index encountered in term_key"

let ty_key (Tt.Ty t) = term_key t
let ty_key_opt (Tt.Ty t) = term_key_opt t

let general_key e1 e2 t =
  let key = term_key_opt e1, term_key_opt e2, ty_key_opt t in
  match key with
  | Some k1, Some k2, Some kt -> Some (k1, k2, kt)
  | _, _, _ -> None

let rec print_term ?max_level xs e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
    match e with
      | Term (e, t) -> Tt.print_term ?max_level xs e ppf

      | PVar k ->
        begin
          try
            print ~at_level:0 "?%t" (Name.print_ident (List.nth xs k))
          with
          | Not_found | Failure "nth" ->
              (** XXX this should never get printed *)
              print ~at_level:0 "?DEBRUIJN[%d]" k
        end

      | Atom x ->
        Name.print_atom x ppf

      | Constant (x, []) ->
        Name.print_ident x ppf

      | Constant (x, ((_::_) as es)) ->
        print ~at_level:1 "@[<hov 2>%t@ %t@]"
          (Name.print_ident x)
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
        | BetaConstant (x, pes) -> Constant (x, pes)
        | BetaAtom x -> Atom x
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


let print_key ?max_level k ppf =
  match k with
  | Key_Atom x -> Print.print ?max_level ppf "Atom %t" (Name.print_atom x)
  | Key_Constant x -> Print.print ?max_level ppf "PrimApp %t" (Name.print_ident x)
  | Key_Type -> Print.print ?max_level ppf "%s" "Type"
  | Key_Lambda -> Print.print ?max_level ppf "%s" "Lambda"
  | Key_Prod -> Print.print ?max_level ppf "%s" "Prod"
  | Key_Eq -> Print.print ?max_level ppf "%s" "Eq"
  | Key_Refl -> Print.print ?max_level ppf "%s" "Refl"
  | Key_Inhab -> Print.print ?max_level ppf "%s" "Inhab"
  | Key_Bracket -> Print.print ?max_level ppf "%s" "Bracket"

let print_general_key ?max_level k ppf =
  match k with
  | None -> Print.print ?max_level ppf "None"
  | Some (k1, k2, kt) ->
    Print.print ?max_level ppf "(e1: %t, e2: %t, t: %t)"
      (print_key k1) (print_key k2) (print_key kt)
