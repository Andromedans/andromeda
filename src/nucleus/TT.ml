(** The abstract syntax of Andromedan type theory (TT). *)

type bound = int

(** A thing labeled with some assumptions. *)
type 'a assumptions = {
  thing : 'a ;
  assumptions : Assumption.t
}

type term = term' assumptions

and term' =
  | Atom of Name.atom
  | Bound of bound
  | TermConstructor of Name.constructor * argument list
  (* obsolete *)
  | Constant of Name.constant

and ty = ty' assumptions

and ty' =
  | TypeConstructor of Name.constructor * argument list
  (* obsolete *)
  | Type
  | El of term

(** An argument of a term or a type constructor *)
and argument =
  | ArgIsTerm of term abstraction
  | ArgIsType of ty abstraction
  | ArgEqType
  | ArgEqTerm

(** An abstracted entity. Note that abstractions only ever appear as arguments
   to constructors. Thus we do not carry any type information for the abstracted
   variable, as it can be recovered from the constructor. *)
and 'a abstraction =
  | Abstract of Name.ident * 'a abstraction
  | NotAbstract of 'a

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)

(* Helper functions *)

(* let ty_hyps {Location.thing={assumptions=a;_};_} = a
 *
 * let rec hyp_union acc = function
 *   | [] -> acc
 *   | x::rem -> hyp_union (Assumption.union acc x) rem *)

let mk_atom x =
  { thing = Atom x
  ; assumptions = Assumption.singleton x
  }

let mk_constant x =
  { thing = Constant x
  ; assumptions = Assumption.empty
  }

let mk_not_abstract x = assert false

let mk_abstract_term x t abstr = assert false
  (* Location.locate
   *   { thing = TermAbstract ((x, a), (e, b))
   *   ; assumptions = hyp_union (ty_hyps a) (List.map Assumption.bind1 [ty_hyps b; e.Location.thing.assumptions]) ;
   *   }
   *   loc *)

let mk_abstract_type x t abstr = assert false
  (* Location.locate
   *   { thing = TypeAbstract ((x, a), b)
   *   ; assumptions=hyp_union (ty_hyps a) [Assumption.bind1 (ty_hyps b)]
   *   }
   *   loc *)

let mk_el e =
  { thing = El e
  ; assumptions = e.assumptions
  }

(** The [Type] constant. *)
let typ =
  { thing = Type
  ; assumptions = Assumption.empty
  }

let mention_atoms a e =
  { e with assumptions = Assumption.add_atoms a e.assumptions }

let mention_atoms_ty a e =
  { e with assumptions = Assumption.add_atoms a e.assumptions }

let mention a e =
  { e with assumptions = Assumption.union e.assumptions a }

let gather_assumptions {assumptions;_} = assumptions

let assumptions e =
  let a = gather_assumptions e in
  Assumption.as_atom_set a

let assumptions_term = assumptions

let assumptions_ty = assumptions

(** Instantiate *)
let instantiate_atom x ~lvl assumptions =
  {thing = Atom x; assumptions}

let instantiate_bound es ~lvl k assumptions =
  if k < lvl
  then
    {thing = Bound k; assumptions}
    (* this is a variable bound in an abstraction inside the
       instantiated term, so we leave it as it is *)
  else
    let n = List.length es in
    if k < lvl + n
    then (* variable corresponds to a substituted term, replace it *)
      let e = List.nth es (k - lvl) in
      mention assumptions e
    else
      {thing = Bound (k - n); assumptions}
      (* this is a variable bound in an abstraction outside the
         instantiated term, so it remains bound, but its index decreases
         by the number of bound variables replaced by terms *)

let instantiate_hyps es ~lvl h =
  let hs = List.map gather_assumptions es in
  Assumption.instantiate hs lvl h

let rec instantiate_term es ?(lvl=0) ({thing=e';assumptions=hs} as e) =
  match es with
  | [] -> e
  | _::_ ->
     begin
       let assumptions = instantiate_hyps es ~lvl hs in
       if Assumption.equal assumptions hs
       then e
       else
         match e' with
         | Constant _ as term -> {thing = term; assumptions}
         | TermConstructor (c, args) ->
            let args = instantiate_arguments es ~lvl args in
            {thing  =TermConstructor(c, args); assumptions}
         | Atom x -> instantiate_atom x ~lvl assumptions
         | Bound k -> instantiate_bound es ~lvl k assumptions
     end

and instantiate_type es ?(lvl=0) ({thing=t';assumptions=hs} as t) =
  match es with
  | [] -> t
  | _::_ ->
     begin
       let assumptions = instantiate_hyps ~lvl es hs in
       if Assumption.equal assumptions hs
       then t
       else
         match t' with
         | Type as ty -> {thing=ty;assumptions}
         | TypeConstructor (c, args) ->
            let args = instantiate_arguments es ~lvl args in
            {thing = TypeConstructor(c, args); assumptions}
         | El e ->
            let e = instantiate_term es e in
            {thing = El e; assumptions}
     end

and instantiate_arguments es ~lvl args =
  List.map (instantiate_argument es ~lvl) args

and instantiate_argument es ~lvl = function
    | ArgIsType t -> ArgIsType (instantiate_abstraction (instantiate_type es) ~lvl t)
    | ArgIsTerm e -> ArgIsTerm (instantiate_abstraction (instantiate_term es) ~lvl e)
    | ArgEqType -> ArgEqType
    | ArgEqTerm -> ArgEqTerm

and instantiate_abstraction : 'a . (?lvl:bound -> 'a -> 'a) -> lvl:bound -> 'a abstraction -> 'a abstraction =
  fun inst_u ~lvl ->
  function
  | Abstract (x, a) -> Abstract (x, instantiate_abstraction inst_u ~lvl:(lvl+1) a)
  | NotAbstract u -> NotAbstract (inst_u ~lvl u)


let unabstract_term xs ?(lvl=0) e =
  let es = List.map mk_atom xs
  in instantiate_term es ~lvl e

let unabstract_type xs ?(lvl=0) t =
  let es = List.map mk_atom xs
  in instantiate_type es ~lvl t

(** Abstract *)
let abstract_atom xs ~lvl x assumptions =
  begin
    match Name.index_of_atom x xs with
      | None -> {thing = Atom x; assumptions}
      | Some k -> {thing = Bound (lvl + k); assumptions}
  end

let abstract_bound ~lvl k assumptions =
  {thing = Bound k; assumptions}

let abstract_hyps xs ~lvl h =
  Assumption.abstract xs lvl h

let rec abstract_term xs ?(lvl=0) ({thing=e';assumptions=hs} as e) =
  match xs with
  | [] -> e
  | _::_ ->
     begin
         let assumptions = abstract_hyps xs ~lvl hs in
         if Assumption.equal assumptions hs
         then e
         else
           match e' with
           | Constant _ as term -> {thing = term; assumptions}
           | TermConstructor (c, args) ->
              let args = abstract_arguments xs ~lvl args in
              {thing = TermConstructor(c, args); assumptions}
           | Atom x -> abstract_atom xs ~lvl x assumptions
           | Bound k -> abstract_bound ~lvl k assumptions
     end
     (* WAS: at_var (abstract_atom xs) abstract_bound (abstract_hyps xs) ~lvl e *)

and abstract_type xs ?(lvl=0) t =
  match xs with
  | [] -> t
  | _::_ ->
     assert false
     (* WAS: at_var_ty (abstract_atom xs) abstract_bound (abstract_hyps xs) ~lvl t *)

and abstract_arguments xs ~lvl args =
  List.map (abstract_argument xs ~lvl) args

and abstract_argument xs ~lvl = function
    | ArgIsType t -> ArgIsType (abstract_abstraction (abstract_type xs) ~lvl t)
    | ArgIsTerm e -> ArgIsTerm (abstract_abstraction (abstract_term xs) ~lvl e)
    | ArgEqType -> ArgEqType
    | ArgEqTerm -> ArgEqTerm

and abstract_abstraction : 'a . (?lvl:int -> 'a -> 'a) -> lvl:int -> 'a abstraction -> 'a abstraction =
  fun inst_u ~lvl ->
  function
  | Abstract (x, a) -> Abstract (x, abstract_abstraction inst_u ~lvl:(lvl+1) a)
  | NotAbstract u -> NotAbstract (inst_u ~lvl u)


(** Substitute *)
let substitute_term xs es e =
  match xs, es with
  | [], [] -> e
  | _, _ ->
    let e = abstract_term xs ~lvl:0 e in
    instantiate_term es ~lvl:0 e

let substitute_type xs es t =
  match xs, es with
  | [], [] -> t
  | _, _ ->
    let t = abstract_type xs ~lvl:0 t in
    instantiate_type es ~lvl:0 t

(* Does the bound variable [k] occur in an expression? Used only for printing. *)
let rec occurs_term k {thing=e';_} =
  match e' with
  | Atom _ -> false
  | Bound m -> k = m
  | Constant x -> false
  | TermConstructor (_, args) -> occurs_args k args

and occurs_type k {thing=t';_} =
  match t' with
  | Type -> false
  | TypeConstructor (_, args) -> occurs_args k args
  | El e -> occurs_term k e

and occurs_args k = function
  | [] -> false
  | (ArgIsTerm e) :: args -> occurs_abstraction occurs_term k e || occurs_args k args
  | (ArgIsType e) :: args -> occurs_abstraction occurs_type k e || occurs_args k args
  | (ArgEqType | ArgEqTerm) :: args -> occurs_args k args

and occurs_abstraction : 'a . (bound -> 'a -> bool) -> bound -> 'a abstraction -> bool =
  fun occurs_u k ->
  function
  | Abstract (_, a) -> occurs_abstraction occurs_u (k+1) a
  | NotAbstract u -> occurs_u k u

(****** Alpha equality ******)

let rec alpha_equal {thing=e1;_} {thing=e2;_} =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | Atom x, Atom y -> Name.eq_atom x y

    | Bound i, Bound j -> i = j

    | Constant x, Constant y -> Name.eq_ident x y

    | TermConstructor (c, args), TermConstructor (c', args') ->
       Name.eq_ident c c' && alpha_equal_args args args'

    | (Atom _ | Bound _ | TermConstructor _  | Constant _), _ ->
      false
  end

and alpha_equal_ty {thing=t1;_} {thing=t2;_} =
  match t1, t2 with
  | Type, Type -> true

  | TypeConstructor (c, args), TypeConstructor (c', args') ->
     Name.eq_ident c c' && alpha_equal_args args args'

  | El e1, El e2 -> alpha_equal e1 e2

  | (Type | TypeConstructor _ | El _), _ -> false

and alpha_equal_args args args' =
  match args, args' with
  | [], [] -> true
  | (ArgIsTerm e)::args, (ArgIsTerm e')::args' -> alpha_equal_abstraction alpha_equal e e' && alpha_equal_args args args'
  | (ArgIsType t)::args, (ArgIsType t')::args' -> alpha_equal_abstraction alpha_equal_ty t t' && alpha_equal_args args args'
  | ArgEqType :: args, ArgEqType :: args' -> alpha_equal_args args args'
  | ArgEqTerm :: args, ArgEqTerm :: args' -> alpha_equal_args args args'
  | (ArgIsTerm _ | ArgIsType _ | ArgEqType | ArgEqTerm)::_, _::_
  | (_::_), []
  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false

and alpha_equal_abstraction : 'a . ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool =
  fun equal_u u u' ->
  match u, u' with
  | Abstract (_, a), Abstract(_, a') -> alpha_equal_abstraction equal_u a a'
  | NotAbstract u, NotAbstract u' -> equal_u u u'
  | (Abstract _ | NotAbstract _), _ -> false

(****** Printing routines *****)
type print_env =
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ; }

let add_forbidden x penv = { penv with forbidden = x :: penv.forbidden }

let rec print_term ?max_level ~penv {thing=e;_} ppf =
    print_term' ~penv ?max_level e ppf

and print_term' ~penv ?max_level e ppf =
  match e with
  | Atom x ->
     Name.print_atom ~printer:(penv.atoms) x ppf

  | TermConstructor (c, args) ->
     print_constructor ?max_level ~penv c args ppf

  | Constant x ->
     Name.print_ident x ppf

  | Bound k -> Name.print_debruijn penv.forbidden k ppf

and print_type ?max_level ~penv {thing=t;_} ppf =
  match t with

  | Type -> Format.fprintf ppf "Type"

  | TypeConstructor (c, args) ->
     print_constructor ?max_level ~penv c args ppf

  | El e -> Format.fprintf ppf "El@ %t" (print_term ~max_level:Level.el_arg ~penv e)

and print_constructor ?max_level ~penv c args ppf =
  Format.pp_open_hovbox ppf 2 ;
  Print.print ~at_level:Level.app ?max_level ppf "%t@ %t"
    (Name.print_ident c)
    (Print.sequence (print_arg ~penv) "" args) ;
  Format.pp_close_box ppf ()

and print_arg ~penv arg ppf =
  match arg with
  | ArgIsTerm abstr -> print_abstraction occurs_term print_term ~max_level:Level.app_right ~penv abstr ppf
  | ArgIsType abstr -> print_abstraction occurs_type print_type ~max_level:Level.app_right ~penv abstr ppf
  | ArgEqType -> ()
  | ArgEqTerm -> ()

(** [print_abstraction occurs_u print_u ?max_level ~penv abstr ppf] prints an abstraction using formatter [ppf]. *)
and print_abstraction :
      'a . (int -> 'a -> bool) ->
           (?max_level:Level.t -> penv:print_env -> 'a -> Format.formatter -> unit) ->
           ?max_level:Level.t ->
           penv:print_env ->
           'a abstraction ->
           Format.formatter -> unit =
  fun occurs_u print_u ?max_level ~penv abstr ppf ->
  let rec fold penv xs = function

    | NotAbstract e ->
       let xs = List.rev xs in
       Print.print ?max_level ppf ~at_level:Level.binder "@[<hov 2>{%t}@ %t@]"
              (Print.sequence (Name.print_ident ~parentheses:true) "" xs)
              (print_u ~penv e)

    | Abstract (x, abstr) ->
       let x = (if occurs_abstraction occurs_u 0 abstr then Name.refresh penv.forbidden x else Name.anonymous ()) in
       let penv = add_forbidden x penv in
       fold penv (x :: xs) abstr
  in
  fold penv [] abstr

(** Conversion to JSON *)

module Json =
struct

  let rec term {thing=e; assumptions=asm} =
    Json.tuple [term' e; Assumption.Json.assumptions asm]

  and term' e =
    match e with

      | Atom a -> Json.tag "Atom" [Name.Json.atom a]

      | Bound b -> Json.tag "Bound" [Json.Int b]

      | Constant c -> Json.tag "Constant" [Name.Json.ident c]

      | TermConstructor (c, lst) -> Json.tag "TermConstructor" (Name.Json.ident c :: args lst)

  and ty {thing=t; assumptions=asm} =
    Json.tuple [ty' t; Assumption.Json.assumptions asm]

  and ty' t =
    match t with
      | Type -> Json.tag "Type" []

      | TypeConstructor (c, lst) -> Json.tag "TypeConstructor" (Name.Json.ident c :: args lst)

      | El e -> Json.tag "El" [term e]

  and args lst =
    (List.map
       (function
        | ArgIsTerm abstr -> Json.tag "ArgIsTerm" (abstraction term [] abstr)
        | ArgIsType abstr -> Json.tag "ArgIsType" (abstraction ty [] abstr)
        | ArgEqType -> Json.tag "ArgIsType" []
        | ArgEqTerm -> Json.tag "ArgEqTerm" [])
       lst)

  and abstraction : 'a . ('a -> Json.t) -> Name.ident list -> 'a abstraction -> Json.t list =
    fun json_u xs ->
    function
    | Abstract (x, abstr) ->
       abstraction json_u (x::xs) abstr
    | NotAbstract u ->
       let xs = List.map Name.Json.ident (List.rev xs) in
       [Json.tuple xs ; json_u u]
end
