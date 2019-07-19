(****** Printing routines *****)

open Nucleus_types

(** Add the given identifier to the list of names that cannot be used as bound names. *)
let forbid x penv = { penv with forbidden = Name.set_add x penv.forbidden }

(** Register a deBruijn index name *)
let debruijn x penv =
  { penv with forbidden = Name.set_add x penv.forbidden ; debruijn = x :: penv.debruijn }

(** Print the thesis if a type judgement. *)
let rec thesis_ty ?max_level ~penv t ppf =
  match t with

  | TypeConstructor (c, args) ->
     constructor ?max_level ~penv c args ppf

  | TypeMeta (mv, args) ->
     meta ?max_level ~penv mv args ppf

(** Print the thesis if a term judgement. *)
and thesis_term ?max_level ~penv e ppf =
  match e with
  | TermAtom {atom_nonce=x; _} ->
     Nonce.print ~parentheses:true x ppf

  | TermBound k -> Name.print_debruijn penv.debruijn k ppf

  | TermConstructor (c, args) ->
     constructor ?max_level ~penv c args ppf

  | TermMeta (mv, args) ->
     meta ?max_level ~penv mv args ppf

  | TermConvert (e, _, _) -> thesis_term ~penv ?max_level e ppf

(** Print the boundary of a type equality judgement. *)
and boundary_eq_type ?max_level ~penv (t1, t2) ppf =
  Print.print
    ?max_level
    ~at_level:Level.eq
    ppf
    "%t@ %s@ %t"
    (thesis_ty ~penv t1)
    (Print.char_equal ())
    (thesis_ty ~penv t2)

(** Print a type equality judgement. *)
and thesis_eq_type ?max_level ~penv (EqType (_asmp, t1, t2)) ppf =
  (* TODO: print _asmp? *)
  boundary_eq_type ?max_level ~penv (t1, t2) ppf

(** Print the boundary of a term equality judgement. *)
and boundary_eq_term ?max_level ~penv (e1, e2, t) ppf =
  (* TODO: print _asmp? *)
  Print.print
    ?max_level
    ~at_level:Level.eq
    ppf
    "%t@ %s@ %t@ :@ %t"
    (thesis_term ~penv e1)
    (Print.char_equal ())
    (thesis_term ~penv e2)
    (thesis_ty ~penv t)

(** Print a term equality judgement. *)
and thesis_eq_term ?max_level ~penv (EqTerm (_asmp, e1, e2, t)) ppf =
  (* TODO: print _asmp? *)
  boundary_eq_term ?max_level ~penv (e1, e2, t) ppf

(** Print a meta-variable *)
and meta :
  type a . ?max_level:Level.t -> penv:print_environment
            -> a meta -> is_term list -> Format.formatter -> unit
  = fun ?max_level ~penv {meta_nonce;_} args ppf ->
  match args with
  | [] ->
     Nonce.print ~parentheses:true meta_nonce ppf
  | _::_ ->
     Print.print ~at_level:Level.meta ?max_level ppf "%t@ %t"
    (Nonce.print ~parentheses:true meta_nonce)
    (Print.sequence (thesis_term ~max_level:Level.meta_arg ~penv) "" args) ;

and constructor ?max_level ~penv c args ppf =
  match args with
  | [] ->
     Ident.print ~opens:penv.opens ~parentheses:true c ppf
  | _::_ ->
     Print.print ~at_level:Level.constructor ?max_level ppf "%t@ %t"
       (Ident.print ~opens:penv.opens ~parentheses:true c)
       (Print.sequence (argument ~penv) "" args) ;

and abstraction
   : 'b . (bound -> 'b -> bool) ->
          (?max_level:Level.t -> penv:print_environment -> 'b -> Format.formatter -> unit) ->
          ?max_level:Level.t ->
          penv:print_environment ->
          'b abstraction ->
          Format.formatter -> unit
  = fun occurs_v print_v ?max_level ~penv abstr ppf ->
  let rec fold penv abstr ppf =
    match abstr with

    | NotAbstract v ->
          print_v ~max_level:Level.abstraction_body ~penv v ppf

    | Abstract ({atom_nonce=x; atom_type=u}, abstr) ->
       let x =
         (if Occurs.abstraction occurs_v 0 abstr then
            Name.refresh penv.forbidden (Nonce.name x)
          else
            Name.anonymous ())
       in
       Print.print ppf "%t@ " (binder ~penv (x, u)) ;
       let penv = debruijn x penv in
       fold penv abstr ppf
  in
  match abstr with
  | NotAbstract v -> print_v ?max_level ~penv v ppf
  | Abstract _ -> Print.print ~at_level:Level.abstraction ?max_level ppf "%t" (fold penv abstr)

and argument ~penv arg ppf =
  match arg with
  | JudgementIsType abstr ->
     abstraction Occurs.is_type thesis_ty ~max_level:Level.constructor_arg ~penv abstr ppf
  | JudgementIsTerm abstr ->
     abstraction Occurs.is_term thesis_term ~max_level:Level.constructor_arg ~penv abstr ppf
  | JudgementEqType abstr ->
     abstraction Occurs.eq_type thesis_eq_type ~max_level:Level.constructor_arg ~penv abstr ppf
  | JudgementEqTerm abstr ->
     abstraction Occurs.eq_term thesis_eq_term ~max_level:Level.constructor_arg ~penv abstr ppf


and binder ~penv (x,t) ppf =
  Print.print ppf "{%t@ :@ %t}"
    (Name.print ~parentheses:true x)
    (thesis_ty ~max_level:Level.binder ~penv t)


(** Printing judgements *)

let is_type ?max_level ~penv t ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "@[<hov 2>%s@ %t@ type@]"
              (Print.char_vdash ())
              (thesis_ty ~max_level:Level.highest ~penv t)

let is_term ?max_level ~penv e ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (thesis_term ~max_level:Level.highest ~penv e)

let eq_type ?max_level ~penv eq ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (thesis_eq_type ~max_level:Level.highest ~penv eq)

let eq_term ?max_level ~penv eq ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (thesis_eq_term ~max_level:Level.highest ~penv eq)

let is_type_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs.is_type is_type ?max_level ~penv abstr ppf

let is_term_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs.is_term is_term ?max_level ~penv abstr ppf

let eq_type_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs.eq_type eq_type ?max_level ~penv abstr ppf

let eq_term_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs.eq_term eq_term ?max_level ~penv abstr ppf

(* Printing of boundaries *)
(* TODO: print invisible assumptions, or maybe the entire context *)
let boundary ?max_level ~penv bdry ppf =
  match bdry with
  | BoundaryIsType abstr ->
     abstraction (fun _ () -> false) (fun ?max_level ~penv bdry ppf -> Format.printf "") ?max_level ~penv abstr ppf

  | BoundaryIsTerm abstr ->
     abstraction Occurs.is_type is_type ?max_level ~penv abstr ppf

  | BoundaryEqType abstr ->
     abstraction
       (fun k (t1, t2) -> Occurs.is_type k t1 || Occurs.is_type k t2)
       boundary_eq_type
       ?max_level ~penv abstr ppf

  | BoundaryEqTerm abstr ->
     abstraction
       (fun k (e1, e2, t) -> Occurs.is_term k e1 || Occurs.is_term k e2 || Occurs.is_type k t)
       boundary_eq_term
       ?max_level ~penv abstr ppf

let error ~penv err ppf =
  let open Nucleus_types in
  match err with
  | InvalidInstantiation -> Format.fprintf ppf "invalid instantiation"

  | InvalidAbstraction -> Format.fprintf ppf "invalid abstraction"

  | TooFewArguments -> Format.fprintf ppf "too few arguments"

  | TooManyArguments -> Format.fprintf ppf "too many arguments"

  | TermExpected -> Format.fprintf ppf "term expected"

  | TypeExpected -> Format.fprintf ppf "type expected"

  | ExtraAssumptions -> Format.fprintf ppf "extra assumptions"

  | InvalidApplication -> Format.fprintf ppf "invalid application"

  | InvalidArgument -> Format.fprintf ppf "invalid argument"

  | ArgumentExpected bdry ->
     Format.fprintf ppf "expected a judgment with boundary@ %t"
       (boundary ~penv bdry)

  | AbstractionExpected -> Format.fprintf ppf "abstraction expected"

  | InvalidSubstitution -> Format.fprintf ppf "invalid substutition"

  | InvalidCongruence -> Format.fprintf ppf "invalid congruence argument"

  | InvalidConvert (t1, t2) ->
     Format.fprintf ppf "trying to convert something at@ %t@ using an equality on@ %t@"
       (thesis_ty ~penv t1) (thesis_ty ~penv t2)

  | AlphaEqualTypeMismatch (t1, t2) ->
     Format.fprintf ppf "the types@ %t@ and@ %t@ should be alpha equal"
       (thesis_ty ~penv t1) (thesis_ty ~penv t2)

  | AlphaEqualTermMismatch (e1, e2) ->
     Format.fprintf ppf "the terms@ %t@ and@ %t@ should be alpha equal"
       (thesis_term ~penv e1) (thesis_term ~penv e2)
