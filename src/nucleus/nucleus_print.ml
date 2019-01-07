(****** Printing routines *****)

open Nucleus_types

(** Add the given identifier to the list of names of de Bruijn indices. *)
let add_name x names = x :: names

let rec ty ?max_level ~names t ppf =
  match t with

  | TypeConstructor (c, args) ->
     constructor ?max_level ~names c args ppf

  | TypeMeta (mv, args) ->
     meta ?max_level ~names mv args ppf

and term ?max_level ~names e ppf =
  match e with
  | TermAtom {atom_nonce=x; _} ->
     Nonce.print ~parentheses:true x ppf

  | TermBound k -> Name.print_debruijn names k ppf

  | TermConstructor (c, args) ->
     constructor ?max_level ~names c args ppf

  | TermMeta (mv, args) ->
     meta ?max_level ~names mv args ppf

  | TermConvert (e, _, _) -> term ~names ?max_level e ppf

and eq_type ?max_level ~names (EqType (_asmp, t1, t2)) ppf =
  (* TODO: print _asmp? *)
  Print.print
    ?max_level
    ~at_level:Level.eq
    ppf
    "%t@ %s@ %t"
    (ty ~names t1)
    (Print.char_equal ())
    (ty ~names t2)

and eq_term ?max_level ~names (EqTerm (_asmp, e1, e2, t)) ppf =
  (* TODO: print _asmp? *)
  Print.print
    ?max_level
    ~at_level:Level.eq
    ppf
    "%t@ %s@ %t@ :@ %t"
    (term ~names e1)
    (Print.char_equal ())
    (term ~names e2)
    (ty ~names t)

and meta :
  type a . ?max_level:Level.t -> names:(Name.t list)
            -> a meta -> is_term list -> Format.formatter -> unit
  = fun ?max_level ~names {meta_nonce;_} args ppf ->
  match args with
  | [] ->
     Nonce.print ~parentheses:true meta_nonce ppf
  | _::_ ->
     Print.print ~at_level:Level.meta ?max_level ppf "%t@ %t"
    (Nonce.print ~parentheses:true meta_nonce)
    (Print.sequence (term ~max_level:Level.meta_arg ~names) "" args) ;

and constructor ?max_level ~names c args ppf =
  match args with
  | [] ->
     Ident.print ~parentheses:true c ppf
  | _::_ ->
     Print.print ~at_level:Level.constructor ?max_level ppf "%t@ %t"
       (Ident.print c)
       (Print.sequence (argument ~names) "" args) ;

and abstraction
   : 'b . (bound -> 'b -> bool) ->
          (?max_level:Level.t -> names:(Name.t list) -> 'b -> Format.formatter -> unit) ->
          ?max_level:Level.t ->
          names:(Name.t list) ->
          'b abstraction ->
          Format.formatter -> unit
  = fun occurs_v print_v ?max_level ~names abstr ppf ->
  let rec fold names abstr ppf =
    match abstr with

    | NotAbstract v ->
          print_v ~max_level:Level.abstraction_body ~names v ppf

    | Abstract ({atom_nonce=x; atom_type=u}, abstr) ->
       let x =
         (if Occurs.abstraction occurs_v 0 abstr then
            Name.refresh names (Nonce.name x)
          else
            Name.anonymous ())
       in
       Print.print ppf "%t@ " (binder ~names (x, u)) ;
       let names = add_name x names in
       fold names abstr ppf
  in
  match abstr with
  | NotAbstract v -> print_v ?max_level ~names v ppf
  | Abstract _ -> Print.print ~at_level:Level.abstraction ?max_level ppf "%t" (fold names abstr)

and argument ~names arg ppf =
  match arg with
  | ArgumentIsType abstr ->
     abstraction Occurs.is_type ty ~max_level:Level.constructor_arg ~names abstr ppf
  | ArgumentIsTerm abstr ->
     abstraction Occurs.is_term term ~max_level:Level.constructor_arg ~names abstr ppf
  | ArgumentEqType abstr ->
     abstraction Occurs.eq_type eq_type ~max_level:Level.constructor_arg ~names abstr ppf
  | ArgumentEqTerm abstr ->
     abstraction Occurs.eq_term eq_term ~max_level:Level.constructor_arg ~names abstr ppf


and binder ~names (x,t) ppf =
  Print.print ppf "{%t@ :@ %t}"
    (Name.print ~parentheses:true x)
    (ty ~max_level:Level.binder ~names t)


(** Printing judgements *)

let is_type ?max_level ~names t ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "@[<hov 2>%s@ %t@ type@]"
              (Print.char_vdash ())
              (ty ~max_level:Level.highest ~names t)

let is_term ?max_level ~names e ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (term ~max_level:Level.highest ~names e)

let eq_type ?max_level ~names eq ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (eq_type ~max_level:Level.highest ~names eq)

let eq_term ?max_level ~names eq ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "@[<hov 2>%s@ %t@]"
              (Print.char_vdash ())
              (eq_term ~max_level:Level.highest ~names eq)

let is_type_abstraction ?max_level ~names abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs.is_type is_type ?max_level ~names abstr ppf

let is_term_abstraction ?max_level ~names abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs.is_term is_term ?max_level ~names abstr ppf

let eq_type_abstraction ?max_level ~names abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs.eq_type eq_type ?max_level ~names abstr ppf

let eq_term_abstraction ?max_level ~names abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  abstraction Occurs.eq_term eq_term ?max_level ~names abstr ppf



let error ~names err ppf =
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
  | IsTypeExpected -> Format.fprintf ppf "type argument expected"
  | IsTermExpected -> Format.fprintf ppf "term argument expected"
  | EqTypeExpected -> Format.fprintf ppf "type equality argument expected"
  | EqTermExpected -> Format.fprintf ppf "term equality argument expected"
  | AbstractionExpected -> Format.fprintf ppf "abstraction expected"
  | InvalidSubstitution -> Format.fprintf ppf "invalid substutition"
  | InvalidCongruence -> Format.fprintf ppf "invalid congruence argument"

  | InvalidConvert (t1, t2) ->
     Format.fprintf ppf "trying to convert something at@ %t@ using an equality on@ %t@"
                    (ty ~names t1) (ty ~names t2)

  | AlphaEqualTypeMismatch (t1, t2) ->
     Format.fprintf ppf "the types@ %t@ and@ %t@ should be alpha equal"
                    (ty ~names t1) (ty ~names t2)

  | AlphaEqualTermMismatch (e1, e2) ->
     Format.fprintf ppf "the terms@ %t@ and@ %t@ should be alpha equal"
                    (term ~names e1) (term ~names e2)
