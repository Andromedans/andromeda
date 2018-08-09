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
  | Lambda of (term * ty) ty_abstraction
  | Apply of term * ty ty_abstraction * term

and ty = (ty' assumptions) Location.located

and ty' =
  | Type
  | Prod of ty ty_abstraction
  | El of term

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

let mk_lambda ~loc x a e b =
  Location.locate
    { thing = Lambda ((x, a), (e, b))
    ; assumptions = hyp_union (ty_hyps a) (List.map Assumption.bind1 [ty_hyps b; e.Location.thing.assumptions]) ;
    }
    loc

let mk_apply ~loc e1 x a b e2 =
  Location.locate
  { thing = Apply (e1, ((x, a),b), e2)
  ; assumptions = hyp_union (ty_hyps a)
                    [Assumption.bind1 (ty_hyps b);
                     e1.Location.thing.assumptions;
                     e2.Location.thing.assumptions]
  }
  loc

let mk_prod ~loc x a b =
  Location.locate
    { thing = Prod ((x, a), b)
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
    | Atom x -> atom ~lvl x assumptions loc
    | Bound k -> bound ~lvl k assumptions loc
    | Lambda ((x,a),(e,b)) ->
      let a = at_var_ty atom bound hyps ~lvl a
      and b = at_var_ty atom bound hyps ~lvl:(lvl+1) b
      and e = at_var atom bound hyps ~lvl:(lvl+1) e in
      let term = Lambda ((x,a),(e,b)) in
      Location.locate {thing=term;assumptions} loc
    | Apply (e1,((x,a),b),e2) ->
      let a = at_var_ty atom bound hyps ~lvl a
      and b = at_var_ty atom bound hyps ~lvl:(lvl+1) b
      and e1 = at_var atom bound hyps ~lvl e1
      and e2 = at_var atom bound hyps ~lvl e2 in
      let term = Apply (e1,((x,a),b),e2) in
      Location.locate {thing=term;assumptions} loc

and at_var_ty atom bound hyps ~lvl ({Location.loc=loc;thing={thing=t';assumptions=hs}} as t) =
  let assumptions = hyps ~lvl hs in
  if Assumption.equal assumptions hs
  then t
  else
  match t' with
  | Type as ty -> Location.locate {thing=ty;assumptions} loc
  | Prod ((x,a),b) ->
     let a = at_var_ty atom bound hyps ~lvl a
     and b = at_var_ty atom bound hyps ~lvl:(lvl+1) b in
     let ty = Prod ((x,a),b) in
     Location.locate {thing=ty;assumptions} loc
  | El e ->
     let e = at_var atom bound hyps ~lvl e in
     let term = El e in
     Location.locate {thing=term;assumptions} loc

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

(* How many times does bound variable [k] occur in an expression? Used only for printing. *)
let rec occurs k {Location.loc;thing={thing=e';_}} =
  match e' with
  | Atom _ -> false
  | Bound m -> k = m
  | Constant x -> false
  | Lambda a -> occurs_abstraction occurs_ty occurs_term_ty k a
  | Apply (e1, xtst, e2) ->
    occurs k e1 ||
    occurs_abstraction occurs_ty occurs_ty k xtst ||
    occurs k e2

and occurs_ty k {Location.loc;thing={thing=t';_}} =
  match t' with
  | Type -> false
  | Prod a ->
    occurs_abstraction occurs_ty occurs_ty k a
  | El e -> occurs k e

and occurs_term_ty k (e, t) =
  occurs k e || occurs_ty k t

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

    | Lambda abs, Lambda abs' ->
      alpha_equal_abstraction alpha_equal_ty alpha_equal_term_ty abs abs'

    | Apply (e1, xts, e2), Apply (e1', xts', e2') ->
      alpha_equal e1 e1' &&
      alpha_equal_abstraction alpha_equal_ty alpha_equal_ty xts xts' &&
      alpha_equal e2 e2'

    | (Atom _ | Bound _ | Constant _ | Lambda _ | Apply _), _ ->
      false
  end

and alpha_equal_ty {Location.thing={thing=t1;_};_} {Location.thing={thing=t2;_};_} =
  match t1, t2 with
  | Type, Type -> true

  | Prod abs, Prod abs' ->
     alpha_equal_abstraction alpha_equal_ty alpha_equal_ty abs abs'

  | El e1, El e2 -> alpha_equal e1 e2

  | (Type | Prod _ | El _), _ -> false

and alpha_equal_term_ty (e, t) (e', t') = alpha_equal e e' && alpha_equal_ty t t'

(****** Printing routines *****)
type print_env =
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ; }

type name_printing =
  | As_atom of Name.atom
  | As_ident of Name.ident

let add_forbidden x penv = { penv with forbidden = x :: penv.forbidden }

let print_binders ~penv print_u print_v xus ppf =
  Format.pp_open_hovbox ppf 2 ;
  let rec fold ~penv = function
    | [] -> penv
    | (x,u) :: xus ->
       let y = Name.refresh penv.forbidden x in
       Print.print ppf "@;<1 -4>(%t : %t)"
                   (Name.print_ident y)
                   (print_u ~penv u) ;
       fold ~penv:(add_forbidden y penv) xus
  in
  let penv = fold ~penv xus in
  Print.print ppf ",@ %t" (print_v ~penv) ;
  Format.pp_close_box ppf ()

let rec print_term ?max_level ~penv {Location.thing={thing=e;_};_} ppf =
    print_term' ~penv ?max_level e ppf

and print_term' ~penv ?max_level e ppf =
  match e with
  | Atom x ->
     Name.print_atom ~printer:(penv.atoms) x ppf

  | Constant x ->
     Name.print_ident x ppf

  | Bound k -> Name.print_debruijn penv.forbidden k ppf

  | Lambda a -> print_lambda ?max_level ~penv a ppf

  | Apply (e1, _, e2) -> print_app ?max_level ~penv e1 e2 ppf

and print_ty ?max_level ~penv {Location.thing={thing=t;_};_} ppf =
  match t with

  | Type -> Format.fprintf ppf "Type"

  | Prod xts -> print_prod ?max_level ~penv xts ppf

  | El e -> Format.fprintf ppf "El@ %t" (print_term ~max_level:Level.el_arg ~penv e)

(** [print_app e1 e2 ppf] prints the application [e1 e2] using formatter [ppf],
    possibly as a prefix or infix operator. *)
and print_app ?max_level ~penv e1 e2 ppf =
  let e1_prefix =
    match e1.Location.thing.thing with
    | Bound k ->
       begin
         match List.nth penv.forbidden k with
         | Name.Ident (_, Name.Prefix) as op -> Some (As_ident op)
         | Name.Ident (_, _) -> None
         | exception Failure failure when failure = "nth" -> None
       end
    | Constant (Name.Ident (_, Name.Prefix) as op) -> Some (As_ident op)
    | Atom (Name.Atom (_, Name.Prefix, _) as op) -> Some (As_atom op)

    | Constant (Name.Ident (_, (Name.Word | Name.Anonymous _| Name.Infix _)))
    | Atom (Name.Atom (_, (Name.Word | Name.Anonymous _| Name.Infix _), _))
    | Lambda _ | Apply _ -> None
  in
  match e1_prefix with
  | Some (As_atom op) ->
     Print.print ppf ?max_level ~at_level:Level.prefix "%t@ %t"
                 (Name.print_atom ~parentheses:false ~printer:penv.atoms op)
                 (print_term ~max_level:Level.prefix_arg ~penv e2)

  | Some (As_ident op) ->
     Print.print ppf ?max_level ~at_level:Level.prefix "%t@ %t"
                 (Name.print_ident ~parentheses:false op)
                 (print_term ~max_level:Level.prefix_arg ~penv e2)

  | None ->
     (* Infix or ordinary application. *)
     begin
       let e1_infix =
         begin
           match e1.Location.thing.thing with
           | Apply ({Location.thing={thing=Bound k; _};_}, _, e1) ->
              begin
                match List.nth penv.forbidden k with
                | Name.Ident (_, Name.Infix fixity) as op ->
                   Some (As_ident op, fixity, e1)
                | Name.Ident (_, (Name.Word | Name.Anonymous _| Name.Prefix)) -> None
                | exception Failure failure when failure = "nth" -> None
              end
           | Apply ({Location.thing={thing=Constant (Name.Ident (_, Name.Infix fixity) as op);_};_},
                    _, e1) ->
              Some (As_ident op, fixity, e1)
           | Apply ({Location.thing={thing=Atom (Name.Atom (_, Name.Infix fixity, _) as op);_};_},
                    _, e1) ->
              Some (As_atom op, fixity, e1)

           | Apply _ (* Spelling out exactly which cases are not covered is quite
                        verbose, so we do not do it. *)
           | Lambda _ | Atom _ | Constant _ | Bound _ ->
             None
         end
       in
       match e1_infix with
       | Some (op, fixity, e1) ->
          let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
          Print.print ppf ?max_level ~at_level:lvl_op "%t@ %t@ %t"
                      (print_term ~max_level:lvl_left ~penv e1)
                      (match op with
                       | As_ident op -> Name.print_ident ~parentheses:false op
                       | As_atom op -> Name.print_atom ~parentheses:false ~printer:penv.atoms op)
                      (print_term ~max_level:lvl_right ~penv e2)
       | None ->
          (* ordinary application *)
          Print.print ppf ?max_level ~at_level:Level.app "%t@ %t"
                       (print_term ~max_level:Level.app_left ~penv e1)
                       (print_term ~max_level:Level.app_right ~penv e2)
     end


(** [print_lambda a e t ppf] prints a lambda abstraction using formatter [ppf]. *)
and print_lambda ?max_level ~penv ((x, u), (e, _)) ppf =
  let x = (if not (occurs 0 e) then Name.anonymous () else x) in
  let rec collect xus e =
    match e.Location.thing.thing with
    | Lambda ((x, u), (e, _)) ->
       let x = (if not (occurs 0 e) then Name.anonymous () else x) in
       collect ((x, u) :: xus) e
    | _ ->
       (List.rev xus, e)
  in
  let xus, e = collect [(x,u)] e in
  Print.print ?max_level ~at_level:Level.binder ppf "%s%t"
    (Print.char_lambda ())
    (print_binders ~penv
                   (print_ty ~max_level:Level.ascription)
                   (fun ~penv -> print_term ~max_level:Level.in_binder ~penv e)
                   xus)

(** [print_prod a e t ppf] prints a lambda abstraction using formatter [ppf]. *)
and print_prod ?max_level ~penv ((x, u), t) ppf =
  if not (occurs_ty 0 t) then
    Print.print ?max_level ~at_level:Level.arr ppf "%t@ %s@ %t"
          (print_ty ~max_level:Level.arr_left ~penv u)
          (Print.char_arrow ())
          (print_ty ~max_level:Level.arr_right ~penv:(add_forbidden (Name.anonymous ()) penv) t)
  else
    let rec collect xus ({Location.thing={thing=t;_};_} as t_ty) =
      match t with
      | Prod ((x, u), t_ty) when occurs_ty 0 t_ty ->
         collect ((x, u) :: xus) t_ty
      | _ ->
         (List.rev xus, t_ty)
    in
    let xus, t = collect [(x,u)] t in
    Print.print ?max_level ~at_level:Level.binder ppf "%s%t"
                (Print.char_prod ())
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

      | Lambda (xt, (e, u)) ->
         Json.tag "Lambda" [abstraction xt (Json.tuple [term e; ty u])]

      | Apply (e1, (xt, u), e2) -> Json.tag "Apply" [term e1; abstraction xt (ty u); term e2]

  and abstraction (x, t) d = Json.tuple [Name.Json.ident x; ty t; d]

  and ty {Location.loc;thing={thing=t; assumptions=asm}} =
    if !Config.json_location
    then Json.tuple [ty' t; Assumption.Json.assumptions asm; Location.Json.location loc]
    else Json.tuple [ty' t; Assumption.Json.assumptions asm]

  and ty' t =
    match t with
      | Type -> Json.tag "Type" []
      | Prod (xt, u) -> Json.tag "Prod" [abstraction xt (ty u)]
      | El e -> Json.tag "El" [term e]

end
