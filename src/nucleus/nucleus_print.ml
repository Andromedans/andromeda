(****** Printing routines *****)

open Nucleus_types

(** Add the given identifier to the list of names that cannot be used as bound names. *)
let forbid x penv = { penv with forbidden = Name.set_add x penv.forbidden }

(** Register the name of a bound variable *)
let debruijn_var x penv =
  { penv with forbidden = Name.set_add x penv.forbidden ; debruijn_var = x :: penv.debruijn_var }

(** Register the name of a bound meta-variable *)
let debruijn_meta x penv =
  let x = Nonce.name x in
  { penv with forbidden = Name.set_add x penv.forbidden ; debruijn_meta = x :: penv.debruijn_meta }


(** Print the thesis if a type judgement. *)
let rec thesis_is_type ?max_level ~penv t ppf =
  match t with

  | TypeConstructor (c, args) ->
     constructor ?max_level ~penv c args ppf

  | TypeMeta (mv, args) ->
     meta ?max_level ~penv mv args ppf

(** Print the thesis if a term judgement. *)
and thesis_is_term ?max_level ~penv e ppf =
  match e with
  | TermAtom {atom_nonce=x; _} ->
     Nonce.print ~questionmark:false ~parentheses:true x ppf

  | TermBoundVar k -> Name.print_debruijn_var penv.debruijn_var k ppf

  | TermConstructor (c, args) ->
     constructor ?max_level ~penv c args ppf

  | TermMeta (mv, args) ->
     meta ?max_level ~penv mv args ppf

  | TermConvert (e, _, _) -> thesis_is_term ~penv ?max_level e ppf

(** Print a type equality judgement. *)
and thesis_eq_type ?max_level ~penv (EqType (_asmp, t1, t2)) ppf =
  (* TODO: print _asmp? *)
  Print.print
    ?max_level
    ~at_level:Level.boundary
    ppf
    "%t@ %s@ %t"
    (thesis_is_type ~max_level:Level.eq_left ~penv t1)
    (Print.char_equal ())
    (thesis_is_type ~max_level:Level.eq_right ~penv t2)

(** Print a term equality judgement. *)
and thesis_eq_term ?max_level ~penv (EqTerm (_asmp, e1, e2, t)) ppf =
  (* TODO: print _asmp? *)
  Print.print
    ?max_level
    ~at_level:Level.eq
    ppf
    "%t@ %s@ %t@ :@ %t"
    (thesis_is_term ~max_level:Level.eq_left ~penv e1)
    (Print.char_equal ())
    (thesis_is_term ~max_level:Level.eq_right ~penv e2)
    (thesis_is_type ~max_level:Level.eq_type ~penv t)

(** Print the boundary of a type judgement. *)
and boundary_is_type ?max_level ~penv ~print_head () ppf =
  Print.print
    ?max_level
    ~at_level:Level.boundary
    ppf
    "%t type" (print_head)

(** Print the boundary of a term judgement. *)
and boundary_is_term ?max_level ~penv ~print_head t ppf =
  Print.print
    ?max_level
    ~at_level:Level.boundary
    ppf
    "%t@ :@ %t"
    (print_head)
    (thesis_is_type ~max_level:Level.ascribe ~penv t)

(** Print the boundary of a type equality judgement. *)
and boundary_eq_type ?max_level ~penv ~print_head (t1, t2) ppf =
  Print.print
    ?max_level
    ~at_level:Level.boundary
    ppf
    "%t@ %s@ %t as %t"
    (thesis_is_type ~max_level:Level.eq_left ~penv t1)
    (Print.char_equal ())
    (thesis_is_type ~max_level:Level.eq_right ~penv t2)
    (print_head)

(** Print the boundary of a term equality judgement. *)
and boundary_eq_term ?max_level ~penv ~print_head (e1, e2, t) ppf =
  (* TODO: print _asmp? *)
  Print.print
    ?max_level
    ~at_level:Level.eq
    ppf
    "%t@ %s@ %t@ :@ %t as %t"
    (thesis_is_term ~max_level:Level.eq_left ~penv e1)
    (Print.char_equal ())
    (thesis_is_term ~max_level:Level.eq_right ~penv e2)
    (thesis_is_type ~max_level:Level.ascribe ~penv t)
    (print_head)

(** Print a meta-variable instantiation *)
and meta ?max_level ~penv mv args ppf =
  let print_mv =
    match mv with
    | MetaFree {meta_nonce; _} -> Nonce.print ~questionmark:true ~parentheses:true meta_nonce
    | MetaBound k -> (fun ppf -> Name.print_debruijn_meta penv.debruijn_meta k ppf)
  and print_arg arg ppf =
    Format.fprintf ppf "{%t}" (thesis_is_term ~penv arg)
  in
  match args with
  | [] ->
     print_mv ppf

  | _::_ ->
     Print.print ~at_level:Level.meta ?max_level ppf "%t@ %t"
       (print_mv)
       (Print.sequence print_arg "" args)

and argument ?max_level ~penv arg ppf =
  let rec fold xs penv arg ppf =
    match arg with

    | Arg_NotAbstract jdg ->
       Print.print ?max_level ppf "{%t}@ %t"
          (Print.sequence (Name.print ~parentheses:true) "" xs)
          (judgement_as_argument ~max_level:Level.abstraction_body ~penv jdg)

    | Arg_Abstract (x, arg) ->
       let x =
         (if Occurs_bound.argument 0 arg then
            Name.refresh penv.forbidden x
          else
            Name.anonymous ())
       in
       let penv = debruijn_var x penv in
       fold (x::xs) penv arg ppf
  in
  match arg with
  | Arg_NotAbstract jdg -> judgement_as_argument ?max_level ~penv jdg ppf
  | Arg_Abstract _ -> Print.print ~at_level:Level.abstraction ?max_level ppf "%t" (fold [] penv arg)


and constructor ?max_level ~penv c args ppf =
  match args with
  | [] ->
     Ident.print ~opens:penv.opens ~parentheses:true c ppf
  | _::_ ->
     Print.print ~at_level:Level.constructor ?max_level ppf "%t@ %t"
       (Ident.print ~opens:penv.opens ~parentheses:true c)
       (Print.sequence (argument ~max_level:Level.constructor_arg ~penv) "" args) ;

and print_assumptions ?max_level ~penv {free_var; free_meta; bound_var=_; bound_meta=_} ppf =
  (* If we were more paranoid, we could assert here that [bound_var] and [bound_meta] are empty,
     as we should never print assumptions inside a binder. *)
  let empty_free_var = Nonce.map_is_empty free_var
  and empty_free_meta = Nonce.map_is_empty free_meta in
  Print.print
    ?max_level ppf "%t%s%t%s"
    (Print.sequence
       (fun (x, abstr) ppf -> boundary_abstraction'
                                ~penv:(forbid (Nonce.name x) penv)
                                ~print_head:(Nonce.print ~questionmark:true ~parentheses:true x) abstr ppf)
       "," (Nonce.map_bindings free_meta))
    (if empty_free_var || empty_free_meta then "" else ", ") (* XXX maybe put in something more visible than a , here, such as ; *)
    (Print.sequence
       (fun (x,t) ppf -> Print.print ppf "%t@ :@ %t"
                           (Nonce.print ~questionmark:false ~parentheses:true x)
                           (thesis_is_type ~max_level:Level.ascribe ~penv t))
       "," (Nonce.map_bindings free_var))
    (if empty_free_var && empty_free_meta then "" else " ")

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

    | Abstract (x, u, abstr) ->
       let x =
         (if Occurs_bound.abstraction occurs_v 0 abstr then
            Name.refresh penv.forbidden x
          else
            Name.anonymous ())
       in
       Print.print ppf "%t@ " (binder ~penv (x, u)) ;
       let penv = debruijn_var x penv in
       fold penv abstr ppf
  in
  match abstr with
  | NotAbstract v -> print_v ?max_level ~penv v ppf
  | Abstract _ -> Print.print ~at_level:Level.abstraction ?max_level ppf "%t" (fold penv abstr)

and thesis_judgement ?max_level ~penv arg ppf =
  match arg with
  | JudgementIsType t -> Print.print ?max_level ppf "%t@ type" (thesis_is_type ?max_level ~penv t)
  | JudgementIsTerm e -> thesis_is_term ?max_level ~penv e ppf (* also print the type of [e] *)
  | JudgementEqType eq -> thesis_eq_type ?max_level ~penv eq ppf
  | JudgementEqTerm eq -> thesis_eq_term ?max_level ~penv eq ppf

and judgement_as_argument ?max_level ~penv arg ppf =
  match arg with
  | JudgementIsType t -> thesis_is_type ?max_level ~penv t ppf
  | JudgementIsTerm e -> thesis_is_term ?max_level ~penv e ppf
  | JudgementEqType eq -> thesis_eq_type ?max_level ~penv eq ppf
  | JudgementEqTerm eq -> thesis_eq_term ?max_level ~penv eq ppf

(* Printing of boundaries *)
and thesis_boundary ?max_level ~penv ~print_head bdry ppf =
  match bdry with
  | BoundaryIsType () -> boundary_is_type ?max_level ~penv ~print_head () ppf

  | BoundaryIsTerm e -> boundary_is_term ?max_level ~penv ~print_head e ppf

  | BoundaryEqType eq -> boundary_eq_type ?max_level ~penv ~print_head eq ppf

  | BoundaryEqTerm eq -> boundary_eq_term ?max_level ~penv ~print_head eq ppf

and boundary_abstraction' ?max_level ~penv ~print_head abstr ppf =
  abstraction Occurs_bound.boundary (thesis_boundary ~print_head) ?max_level ~penv abstr ppf

and binder ~penv (x,t) ppf =
  Print.print ppf "{%t@ :@ %t}"
    (Name.print ~parentheses:true x)
    (thesis_is_type ~max_level:Level.binder ~penv t)

(** Printing judgements *)

let is_type ?max_level ~penv t ppf =
  Print.print ?max_level ~at_level:Level.judgement ppf
              "@[<hov 2>%s@ %t@ type@]"
              (Print.char_vdash ())
              (thesis_is_type ~max_level:Level.highest ~penv t)

let is_term ?max_level ~penv e ppf =
  Print.print ?max_level ~at_level:Level.judgement ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (thesis_is_term ~max_level:Level.highest ~penv e)

let eq_type ?max_level ~penv eq ppf =
  Print.print ?max_level ~at_level:Level.judgement ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (thesis_eq_type ~max_level:Level.highest ~penv eq)

let eq_term ?max_level ~penv eq ppf =
  Print.print ?max_level ~at_level:Level.judgement ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (thesis_eq_term ~max_level:Level.highest ~penv eq)

let judgement_abstraction ?max_level ~penv abstr ppf =
  let asmp = Collect_assumptions.abstraction Collect_assumptions.judgement abstr in
  Print.print
    ?max_level ~at_level:Level.judgement ppf
    "%t%s %t"
    (print_assumptions ~max_level:Level.vdash_left ~penv asmp)
    (Print.char_vdash ())
    (abstraction Occurs_bound.judgement thesis_judgement ~max_level:Level.vdash_right ~penv abstr)

let print_qqmark ppf = Format.fprintf ppf "%s" (Print.char_qqmark ())

let boundary_abstraction ?max_level ~penv abstr ppf =
  let asmp = Collect_assumptions.abstraction Collect_assumptions.boundary abstr in
  Print.print
    ?max_level ~at_level:Level.boundary ppf
    "%t%s %t"
    (print_assumptions ~max_level:Level.vdash_left ~penv asmp)
    (Print.char_vdash ())
    (abstraction Occurs_bound.boundary (thesis_boundary ~print_head:print_qqmark) ~max_level:Level.vdash_right ~penv  abstr)

let is_type_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs_bound.is_type thesis_is_type ?max_level ~penv abstr ppf

let is_term_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs_bound.is_term thesis_is_term ?max_level ~penv abstr ppf

let eq_type_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs_bound.eq_type thesis_eq_type ?max_level ~penv abstr ppf

let eq_term_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs_bound.eq_term thesis_eq_term ?max_level ~penv abstr ppf

let premise ~penv n prem ppf =
  boundary_abstraction' ~penv:(forbid (Nonce.name n) penv) ~print_head:(Name.print ~parentheses:true (Nonce.name n)) prem ppf

let derivation ?max_level ~penv drv ppf =
  let rec fold ~penv drv ppf =
    match drv with
    | Conclusion jdg -> Print.print ppf "%s@ %t" (Print.char_arrow ()) (thesis_judgement ~penv jdg)
    | Premise (n, prem, drv) ->
       Print.print ppf "(%t)@ %t"
                   (premise ~penv n prem)
                   (fold ~penv:(debruijn_meta n penv) drv)
  in
  Print.print ppf ?max_level ~at_level:Level.derive "derive@ %t" (fold ~penv drv)



(** Printing of error messages *)
(* TODO: Some of these are probably internal while others count as runtime errors. We
   shoudl differentiate between them and tell the user the internal ones are not their
   fault. *)
let error ~penv err ppf =
  let open Nucleus_types in
  match err with
  | InvalidInstantiation -> Format.fprintf ppf "invalid instantiation"

  | InvalidAbstraction -> Format.fprintf ppf "invalid abstraction"

  | TooFewArguments -> Format.fprintf ppf "too few arguments"

  | TooManyArguments -> Format.fprintf ppf "too many arguments"

  | IsTypeExpected -> Format.fprintf ppf "type expected"

  | IsTermExpected -> Format.fprintf ppf "term expected"

  | IsTypeBoundaryExpected -> Format.fprintf ppf "type boundary expected"

  | IsTermBoundaryExpected -> Format.fprintf ppf "term boundary expected"

  | ExtraAssumptions -> Format.fprintf ppf "extra assumptions"

  | InvalidApplication -> Format.fprintf ppf "invalid application"

  | InvalidArgument -> Format.fprintf ppf "invalid argument"

  | ArgumentExpected bdry ->
     Format.fprintf ppf "expected a judgment with boundary@ %t"
       (thesis_boundary ~penv ~print_head:print_qqmark bdry)

  | AbstractionExpected -> Format.fprintf ppf "abstraction expected"

  | InvalidSubstitution -> Format.fprintf ppf "invalid substutition"

  | InvalidCongruence -> Format.fprintf ppf "invalid congruence argument"

  | InvalidConvert (t1, t2) ->
     Format.fprintf ppf "trying to convert something at@ %t@ using an equality on@ %t@"
       (thesis_is_type ~penv t1) (thesis_is_type ~penv t2)

  | AlphaEqualTypeMismatch (t1, t2) ->
     Format.fprintf ppf "the types@ %t@ and@ %t@ should be alpha equal"
       (thesis_is_type ~penv t1) (thesis_is_type ~penv t2)

  | AlphaEqualTermMismatch (e1, e2) ->
     Format.fprintf ppf "the terms@ %t@ and@ %t@ should be alpha equal"
       (thesis_is_term ~penv e1) (thesis_is_term ~penv e2)

(* Naming things *)
let rec strip_abstraction = function
  | Abstract (_, _, abstr) -> strip_abstraction abstr
  | NotAbstract x -> x

let name_of_judgement abstr =
  match strip_abstraction abstr with
  | JudgementIsTerm _ -> "a term"
  | JudgementIsType _ -> "a type"
  | JudgementEqTerm _ -> "a term equality"
  | JudgementEqType _ -> "a type equality"

let name_of_boundary abstr =
  match strip_abstraction abstr with
  | BoundaryIsTerm _ -> "a term boundary"
  | BoundaryIsType _ -> "a type boundary"
  | BoundaryEqTerm _ -> "a term equality boundary"
  | BoundaryEqType _ -> "a type equality boundary"
