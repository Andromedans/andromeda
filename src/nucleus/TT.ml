(** The abstract syntax of Andromedan type theory (TT). *)

type ('a, 'b) abstraction = (Name.ident * 'a) * 'b

type bound = int

(** A thing labeled with some assumptions. *)
type 'a assumptions = {
  thing : 'a ;
  assumptions : Assumption.t
}

type term = (term' assumptions) Location.located

and term' =
  | Atom of Name.atom
  | Bound of bound
  | Constant of Name.constant
  | TermConstructor of Name.constructor * argument list
  | Abstract of (term * ty) ty_abstraction

and ty = (ty' assumptions) Location.located

and ty' =
  | Type
  | TyConstructor of Name.constructor * argument list
  | AbstractTy of ty ty_abstraction
  | El of term

and argument =
  | TermArgument of term
  | TyArgument of ty

and 'a ty_abstraction = (ty, 'a) abstraction

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)

(* Helper functions *)

let ty_hyps {Location.thing={assumptions=a;_};_} = a

let rec hyp_union acc = function
  | [] -> acc
  | x::rem -> hyp_union (Assumption.union acc x) rem

let mk_atom ~loc x =
  Location.locate
    { thing = Atom x
    ; assumptions = Assumption.singleton x
    }
    loc

let mk_constant ~loc x =
  Location.locate
    { thing = Constant x
    ; assumptions = Assumption.empty
    }
    loc

let mk_abstract ~loc x a e b =
  Location.locate
    { thing = Abstract ((x, a), (e, b))
    ; assumptions = hyp_union (ty_hyps a) (List.map Assumption.bind1 [ty_hyps b; e.Location.thing.assumptions]) ;
    }
    loc

let mk_abstract_ty ~loc x a b =
  Location.locate
    { thing = AbstractTy ((x, a), b)
    ; assumptions=hyp_union (ty_hyps a) [Assumption.bind1 (ty_hyps b)]
    }
    loc

let mk_type ~loc =
  Location.locate
    { thing = Type
    ; assumptions = Assumption.empty;
    }
    loc

let mk_el ~loc e =
  Location.locate
    { thing = El e
    ; assumptions = e.Location.thing.assumptions
    }
    loc

(** The [Type] constant, without a location. *)
let typ = mk_type ~loc:Location.unknown

let mention_atoms a {Location.thing=e; loc} =
  Location.locate { e with assumptions = Assumption.add_atoms a e.assumptions } loc

let mention_atoms_ty a {Location.thing=e; loc} =
  Location.locate { e with assumptions = Assumption.add_atoms a e.assumptions } loc

let mention a {Location.thing=e; loc} =
  Location.locate { e with assumptions = Assumption.union e.assumptions a } loc

let gather_assumptions {Location.thing={assumptions;_};_} = assumptions

let assumptions e =
  let a = gather_assumptions e in
  Assumption.as_atom_set ~loc:e.Location.loc a

let assumptions_term = assumptions

let assumptions_ty = assumptions

(** Generic fold on a term. The functions [atom], [bound] and
    [hyps] tell it what to do with atoms, bound variables, and
    assumptions, respectively.

    If the assumptions on a subterm do not change, this means the entire subterm does not change.

    If [substitute] used [at_var] directly, this shortcut would be incorrect:
    [x where x = x * x] with [x] some atom does not change the assumptions.

    However we only use [at_var] in the following cases:
    - instantiation, which changes bound variables to atoms
    - abstraction, which changes atoms to bound variables
    So if a variable which will change appears, it will be in the assumptions and the assumptions will change.
    *)
let rec at_var atom bound hyps ~lvl ({Location.loc=loc;thing={thing=e';assumptions=hs}} as e) =
  let assumptions = hyps ~lvl hs in
  if Assumption.equal assumptions hs
  then e
  else
  match e' with
    | Constant _ as term -> Location.locate {thing=term;assumptions} loc
    | TermConstructor (c, args) ->
       let args = at_arguments atom bound hyps ~lvl args in
       Location.locate {thing=TermConstructor(c, args); assumptions} loc
    | Atom x -> atom ~lvl x assumptions loc
    | Bound k -> bound ~lvl k assumptions loc
    | Abstract ((x,a),(e,b)) ->
      let a = at_var_ty atom bound hyps ~lvl a
      and b = at_var_ty atom bound hyps ~lvl:(lvl+1) b
      and e = at_var atom bound hyps ~lvl:(lvl+1) e in
      let term = Abstract ((x,a),(e,b)) in
      Location.locate {thing=term;assumptions} loc

and at_var_ty atom bound hyps ~lvl ({Location.loc=loc;thing={thing=t';assumptions=hs}} as t) =
  let assumptions = hyps ~lvl hs in
  if Assumption.equal assumptions hs
  then t
  else
  match t' with
  | Type as ty -> Location.locate {thing=ty;assumptions} loc
    | TyConstructor (c, args) ->
       let args = at_arguments atom bound hyps ~lvl args in
       Location.locate {thing=TyConstructor(c, args); assumptions} loc
  | AbstractTy ((x,a),b) ->
     let a = at_var_ty atom bound hyps ~lvl a
     and b = at_var_ty atom bound hyps ~lvl:(lvl+1) b in
     let ty = AbstractTy ((x,a),b) in
     Location.locate {thing=ty;assumptions} loc
  | El e ->
     let e = at_var atom bound hyps ~lvl e in
     let term = El e in
     Location.locate {thing=term;assumptions} loc

and at_arguments atom bound hyps ~lvl args =
  List.map
  (function
   | TermArgument e -> TermArgument (at_var atom bound hyps ~lvl e)
   | TyArgument t -> TyArgument (at_var_ty atom bound hyps ~lvl t))
  args

(** Instantiate *)
let instantiate_atom ~lvl x assumptions loc =
  Location.locate {thing = Atom x; assumptions} loc

let instantiate_bound es ~lvl k assumptions loc =
  if k < lvl
  then
    Location.locate {thing = Bound k; assumptions} loc
    (* this is a variable bound in an abstraction inside the
       instantiated term, so we leave it as it is *)
  else
    let n = List.length es in
    if k < lvl + n
    then (* variable corresponds to a substituted term, replace it *)
      let e = List.nth es (k - lvl) in
      mention assumptions e
    else
      Location.locate {thing = Bound (k - n); assumptions} loc
      (* this is a variable bound in an abstraction outside the
         instantiated term, so it remains bound, but its index decreases
         by the number of bound variables replaced by terms *)

let instantiate_hyps es =
  let hs = List.map gather_assumptions es in
  fun ~lvl h -> Assumption.instantiate hs lvl h

let instantiate es ?(lvl=0) e =
  match es with
  | [] -> e
  | _::_ -> at_var instantiate_atom (instantiate_bound es) (instantiate_hyps es) ~lvl e

let instantiate_ty es ?(lvl=0) t =
  match es with
  | [] -> t
  | _::_ -> at_var_ty instantiate_atom (instantiate_bound es) (instantiate_hyps es) ~lvl t

let unabstract xs ?(lvl=0) e =
  let es = List.map (mk_atom ~loc:Location.unknown) xs
  in instantiate es ~lvl e

let unabstract_ty xs ?(lvl=0) t =
  let es = List.map (mk_atom ~loc:Location.unknown) xs
  in instantiate_ty es ~lvl t

(** Abstract *)
let abstract_atom xs ~lvl x assumptions loc =
  begin
    match Name.index_of_atom x xs with
      | None -> Location.locate {thing = Atom x; assumptions} loc
      | Some k -> Location.locate {thing = Bound (lvl + k); assumptions} loc
  end

let abstract_bound ~lvl k assumptions loc =
  Location.locate {thing = Bound k; assumptions} loc

let abstract_hyps xs ~lvl h =
  Assumption.abstract xs lvl h

let abstract xs ?(lvl=0) e =
  match xs with
  | [] -> e
  | _::_ -> at_var (abstract_atom xs) abstract_bound (abstract_hyps xs) ~lvl e

let abstract_ty xs ?(lvl=0) t =
  match xs with
  | [] -> t
  | _::_ -> at_var_ty (abstract_atom xs) abstract_bound (abstract_hyps xs) ~lvl t

(** Substitute *)
let substitute xs es e =
  match xs, es with
  | [], [] -> e
  | _, _ ->
    let e = abstract xs ~lvl:0 e in
    instantiate es ~lvl:0 e

let substitute_ty xs es t =
  match xs, es with
  | [], [] -> t
  | _, _ ->
    let t = abstract_ty xs ~lvl:0 t in
    instantiate_ty es ~lvl:0 t

(** Occurs (for printing) *)
let occurs_abstraction occurs_u occurs_v k ((x,u), v) =
  occurs_u k u || occurs_v (k+1) v

(* Does the bound variable [k] occur in an expression? Used only for printing. *)
let rec occurs k {Location.loc;thing={thing=e';_}} =
  match e' with
  | Atom _ -> false
  | Bound m -> k = m
  | Constant x -> false
  | TermConstructor (_, args) -> occurs_args k args
  | Abstract a -> occurs_abstraction occurs_ty occurs_term_ty k a

and occurs_ty k {Location.loc;thing={thing=t';_}} =
  match t' with
  | Type -> false
  | TyConstructor (_, args) -> occurs_args k args
  | AbstractTy a -> occurs_abstraction occurs_ty occurs_ty k a
  | El e -> occurs k e

and occurs_term_ty k (e, t) =
  occurs k e || occurs_ty k t

and occurs_args k = function
  | [] -> false
  | (TermArgument e) :: args -> occurs k e || occurs_args k args
  | (TyArgument e) :: args -> occurs_ty k e || occurs_args k args


(****** Alpha equality ******)

let alpha_equal_abstraction alpha_equal_u alpha_equal_v ((x,u), v) ((x,u'), v') =
  alpha_equal_u u u' &&
  alpha_equal_v v v'

let rec alpha_equal {Location.thing={thing=e1;_};_} {Location.thing={thing=e2;_};_} =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | Atom x, Atom y -> Name.eq_atom x y

    | Bound i, Bound j -> i = j

    | Constant x, Constant y -> Name.eq_ident x y

    | TermConstructor (c, args), TermConstructor (c', args') ->
       Name.eq_ident c c' && alpha_equal_args args args'

    | Abstract abs, Abstract abs' ->
      alpha_equal_abstraction alpha_equal_ty alpha_equal_term_ty abs abs'

    | (Atom _ | Bound _ | TermConstructor _  | Constant _ | Abstract _), _ ->
      false
  end

and alpha_equal_ty {Location.thing={thing=t1;_};_} {Location.thing={thing=t2;_};_} =
  match t1, t2 with
  | Type, Type -> true

  | TyConstructor (c, args), TyConstructor (c', args') ->
     Name.eq_ident c c' && alpha_equal_args args args'

  | AbstractTy abs, AbstractTy abs' ->
     alpha_equal_abstraction alpha_equal_ty alpha_equal_ty abs abs'

  | El e1, El e2 -> alpha_equal e1 e2

  | (Type | TyConstructor _ | AbstractTy _ | El _), _ -> false

and alpha_equal_args args args' =
  match args, args' with
  | [], [] -> true
  | (TermArgument e)::args, (TermArgument e')::args' -> alpha_equal e e' && alpha_equal_args args args'
  | (TyArgument t)::args, (TyArgument t')::args' -> alpha_equal_ty t t' && alpha_equal_args args args'
  | (TermArgument _)::_, (TyArgument _)::_
  | (TyArgument _)::_, (TermArgument _)::_
  | (_::_), []
  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false

and alpha_equal_term_ty (e, t) (e', t') = alpha_equal e e' && alpha_equal_ty t t'

(****** Printing routines *****)
type print_env =
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ; }

let add_forbidden x penv = { penv with forbidden = x :: penv.forbidden }

let print_binders ~penv print_u print_v xus ppf =
  Format.pp_open_hovbox ppf 2 ;
  let rec fold ~penv = function
    | [] -> penv
    | (x,u) :: xus ->
       let y = Name.refresh penv.forbidden x in
       Print.print ppf "@;<1 -4>{%t : %t}"
                   (Name.print_ident y)
                   (print_u ~penv u) ;
       fold ~penv:(add_forbidden y penv) xus
  in
  let penv = fold ~penv xus in
  Print.print ppf "@ %t" (print_v ~penv) ;
  Format.pp_close_box ppf ()

let rec print_term ?max_level ~penv {Location.thing={thing=e;_};_} ppf =
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

  | Abstract a -> print_abstract ?max_level ~penv a ppf

and print_ty ?max_level ~penv {Location.thing={thing=t;_};_} ppf =
  match t with

  | Type -> Format.fprintf ppf "Type"

  | TyConstructor (c, args) ->
     print_constructor ?max_level ~penv c args ppf

  | AbstractTy xts -> print_abstract_ty ?max_level ~penv xts ppf

  | El e -> Format.fprintf ppf "El@ %t" (print_term ~max_level:Level.el_arg ~penv e)

and print_constructor ?max_level ~penv c args ppf =
  Format.pp_open_hovbox ppf 2 ;
  Print.print ~at_level:Level.app ?max_level ppf "%t@ %t"
    (Name.print_ident c)
    (Print.sequence (print_arg ~penv) "" args) ;
  Format.pp_close_box ppf ()

and print_arg ~penv arg ppf =
  match arg with
  | TermArgument e -> print_term ~max_level:Level.app_right ~penv e ppf
  | TyArgument t -> print_ty ~max_level:Level.app_right ~penv t ppf


(** [print_abstract ?max_level ~pend ((x,u), (e,t)) ppf] prints an abstraction using formatter [ppf]. *)
and print_abstract ?max_level ~penv ((x, u), (e, _)) ppf =
  let x = (if not (occurs 0 e) then Name.anonymous () else x) in
  let rec collect xus e =
    match e.Location.thing.thing with
    | Abstract ((x, u), (e, _)) ->
       let x = (if not (occurs 0 e) then Name.anonymous () else x) in
       collect ((x, u) :: xus) e
    | _ ->
       (List.rev xus, e)
  in
  let xus, e = collect [(x,u)] e in
  Print.print ?max_level ~at_level:Level.binder ppf "%t"
    (print_binders ~penv
                   (print_ty ~max_level:Level.ascription)
                   (fun ~penv -> print_term ~max_level:Level.in_binder ~penv e)
                   xus)

(** [print_abstract_ty a e t ppf] prints a type abstraction using formatter [ppf]. *)
and print_abstract_ty ?max_level ~penv ((x, u), t) ppf =
  let x = (if not (occurs_ty 0 t) then Name.anonymous () else x) in
  let rec collect xus ({Location.thing={thing=t;_};_} as t_ty) =
    match t with
    | AbstractTy ((x, u), t_ty) ->
       let x = (if not (occurs_ty 0 t_ty) then Name.anonymous () else x) in
       collect ((x, u) :: xus) t_ty
    | _ ->
       (List.rev xus, t_ty)
  in
  let xus, t = collect [(x,u)] t in
  Print.print ?max_level ~at_level:Level.binder ppf "%t"
    (print_binders ~penv
       (print_ty ~max_level:Level.ascription)
       (fun ~penv -> print_ty ~max_level:Level.in_binder ~penv t)
       xus)


(** Conversion to JSON *)

module Json =
struct

  let rec term {Location.loc;thing={thing=e; assumptions=asm}} =
    if !Config.json_location
    then Json.tuple [term' e; Assumption.Json.assumptions asm; Location.Json.location loc]
    else Json.tuple [term' e; Assumption.Json.assumptions asm]

  and term' e =
    match e with

      | Atom a -> Json.tag "Atom" [Name.Json.atom a]

      | Bound b -> Json.tag "Bound" [Json.Int b]

      | Constant c -> Json.tag "Constant" [Name.Json.ident c]

      | TermConstructor (c, lst) -> Json.tag "TermConstructor" (Name.Json.ident c :: args lst)

      | Abstract (xt, (e, u)) ->
         Json.tag "Abstract" [abstraction xt (Json.tuple [term e; ty u])]

  and abstraction (x, t) d = Json.tuple [Name.Json.ident x; ty t; d]

  and ty {Location.loc;thing={thing=t; assumptions=asm}} =
    if !Config.json_location
    then Json.tuple [ty' t; Assumption.Json.assumptions asm; Location.Json.location loc]
    else Json.tuple [ty' t; Assumption.Json.assumptions asm]

  and ty' t =
    match t with
      | Type -> Json.tag "Type" []

      | TyConstructor (c, lst) -> Json.tag "TyConstructor" (Name.Json.ident c :: args lst)

      | AbstractTy (xt, u) -> Json.tag "AbstractTy" [abstraction xt (ty u)]

      | El e -> Json.tag "El" [term e]

  and args lst =
    (List.map
       (function
        | TermArgument e -> term e
        | TyArgument t -> ty t)
       lst)

end
