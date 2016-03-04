(** The abstract syntax of Andromedan type theory (TT). *)

type ('a,'b) constrain =
  | Unconstrained of 'a
  | Constrained of 'b

type ('a, 'b) abstraction = (Name.ident * 'a) * 'b

type bound = int

type term = {
  term : term';
  (* raw term *)

  assumptions : Assumption.t;
  (* set of atoms on which the term depends *)

  loc : Location.t
  (* the location in input where the term appeared, as much as that makes sense *)
}

and term' =
  | Type
  | Atom of Name.atom
  | Bound of bound
  | Constant of Name.constant
  | Lambda of (term * ty) ty_abstraction
  | Apply of term * ty ty_abstraction * term
  | Prod of ty ty_abstraction
  | Eq of ty * term * term
  | Refl of ty * term
  | Signature of signature
  | Structure of structure
  | Projection of term * signature * Name.label

and ty = Ty of term

and 'a ty_abstraction = (ty, 'a) abstraction

and sig_def = (Name.label * Name.ident * ty) list

and signature = Name.signature * (Name.ident, term) constrain list

and structure = signature * term list

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)

(* Helpers *)
let ty_hyps (Ty e) = e.assumptions
let rec hyp_union acc = function
  | [] -> acc
  | x::rem -> hyp_union (Assumption.union acc x) rem

let mk_atom ~loc x = {
  term = Atom x;
  assumptions = Assumption.singleton x;
  loc = loc
}

let mk_constant ~loc x = {
  term = Constant x;
  assumptions=Assumption.empty;
  loc = loc
}

let mk_lambda ~loc x a e b = {
  term = Lambda ((x, a), (e, b)) ;
  assumptions=hyp_union (ty_hyps a) (List.map (Assumption.bind 1) [ty_hyps b;e.assumptions]) ;
  loc = loc
}

let mk_prod ~loc x a b = {
  term = Prod ((x, a), b) ;
  assumptions=hyp_union (ty_hyps a) [Assumption.bind 1 (ty_hyps b)] ;
  loc = loc
}

let mk_apply ~loc e1 x a b e2 = {
  term = Apply (e1, ((x, a),b), e2);
  assumptions = hyp_union (ty_hyps a) [Assumption.bind 1 (ty_hyps b);e1.assumptions;e2.assumptions] ;
  loc = loc
}

let mk_type ~loc =
  { term = Type;
    assumptions = Assumption.empty;
    loc = loc }

let mk_eq ~loc t e1 e2 =
  { term = Eq (t, e1, e2);
    assumptions = hyp_union (ty_hyps t) [e1.assumptions;e2.assumptions];
    loc = loc }

let mk_refl ~loc t e =
  { term = Refl (t, e);
    assumptions = hyp_union (ty_hyps t) [e.assumptions];
    loc = loc }

let assumptions_sig (_,shares) =
  let rec fold lvl acc = function
    | [] -> acc
    | (Unconstrained _) :: shares -> fold (lvl+1) acc shares
    | (Constrained e) :: shares ->
      let acc = Assumption.union acc (Assumption.bind lvl e.assumptions) in
      fold lvl acc shares
  in
  fold 0 Assumption.empty shares

let mk_signature ~loc s =
  { term = Signature s;
    assumptions = assumptions_sig s;
    loc = loc }

let mk_structure ~loc s es =
  { term = Structure (s, es);
    assumptions = List.fold_left (fun acc e -> Assumption.union acc e.assumptions)
                                 (assumptions_sig s) es;
    loc = loc }

let mk_projection ~loc e s l =
  { term = Projection (e, s, l);
    assumptions = Assumption.union (assumptions_sig s) e.assumptions;
    loc = loc }

(** Convert a term to a type. *)
let ty e = Ty e

let mk_eq_ty ~loc t e1 e2 = ty (mk_eq ~loc t e1 e2)
let mk_prod_ty ~loc x a b = ty (mk_prod ~loc x a b)
let mk_type_ty ~loc = ty (mk_type ~loc)
let mk_signature_ty ~loc s = ty (mk_signature ~loc s)

(** The [Type] constant, without a location. *)
let typ = Ty (mk_type ~loc:Location.unknown)

let mention_atoms a e =
  { e with assumptions = Assumption.add_atoms a e.assumptions }

let mention a e =
  { e with assumptions = Assumption.union e.assumptions a }

let gather_assumptions {assumptions;_} = assumptions

let assumptions_term ({loc;_} as e) =
  let a = gather_assumptions e in
  Assumption.as_atom_set ~loc a

let assumptions_ty (Ty t) = assumptions_term t


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
let rec at_var atom bound hyps ~lvl ({term=e';assumptions=hs;loc} as e) =
  let assumptions = hyps ~lvl hs in
  if Assumption.equal assumptions hs
  then e
  else
  match e' with
    | (Type | Constant _) as term -> {term;assumptions;loc}
    | Atom x -> atom ~lvl x assumptions loc
    | Bound k -> bound ~lvl k assumptions loc
    | Prod ((x,a),b) ->
      let a = at_var_ty atom bound hyps ~lvl a
      and b = at_var_ty atom bound hyps ~lvl:(lvl+1) b in
      let term = Prod ((x,a),b) in
      {term;assumptions;loc}
    | Lambda ((x,a),(e,b)) ->
      let a = at_var_ty atom bound hyps ~lvl a
      and b = at_var_ty atom bound hyps ~lvl:(lvl+1) b
      and e = at_var atom bound hyps ~lvl:(lvl+1) e in
      let term = Lambda ((x,a),(e,b)) in
      {term;assumptions;loc}
    | Apply (e1,((x,a),b),e2) ->
      let a = at_var_ty atom bound hyps ~lvl a
      and b = at_var_ty atom bound hyps ~lvl:(lvl+1) b
      and e1 = at_var atom bound hyps ~lvl e1
      and e2 = at_var atom bound hyps ~lvl e2 in
      let term = Apply (e1,((x,a),b),e2) in
      {term;assumptions;loc}
    | Eq (a,e1,e2) ->
      let a = at_var_ty atom bound hyps ~lvl a
      and e1 = at_var atom bound hyps ~lvl e1
      and e2 = at_var atom bound hyps ~lvl e2 in
      let term = Eq (a,e1,e2) in
      {term;assumptions;loc}
    | Refl (a,e) ->
      let a = at_var_ty atom bound hyps ~lvl a
      and e = at_var atom bound hyps ~lvl e in
      let term = Refl (a,e) in
      {term;assumptions;loc}
    | Signature s ->
      let s = at_var_sig atom bound hyps ~lvl s in
      let term = Signature s in
      {term;assumptions;loc}
    | Structure (s, es) ->
      let s = at_var_sig atom bound hyps ~lvl s
      and es = at_var_struct atom bound hyps ~lvl es in
      let term = Structure (s, es) in
      {term;assumptions;loc}
    | Projection (e,s,l) ->
      let e = at_var atom bound hyps ~lvl e
      and s = at_var_sig atom bound hyps ~lvl s in
      let term = Projection (e,s,l) in
      {term;assumptions;loc}

and at_var_ty atom bound hyps ~lvl (Ty a) =
  Ty (at_var atom bound hyps ~lvl a)

and at_var_sig atom bound hyps ~lvl (s, shares) =
  let rec fold lvl res = function
    | [] -> s, List.rev res
    | (Unconstrained x) :: shares -> fold (lvl+1) ((Unconstrained x)::res) shares
    | (Constrained e) :: shares ->
      let e = at_var atom bound hyps ~lvl e in
      fold lvl ((Constrained e)::res) shares
  in
  fold lvl [] shares

and at_var_struct atom bound hyps ~lvl es =
  List.map (at_var atom bound hyps ~lvl) es

(** Instantiate *)
let instantiate_atom ~lvl x assumptions loc =
  {term=Atom x;assumptions;loc}

let instantiate_bound es ~lvl k assumptions loc =
  if k < lvl
  then
    {term=Bound k;assumptions;loc}
    (* this is a variable bound in an abstraction inside the
    instantiated term, so we leave it as it is *)
  else
    let n = List.length es in
    if k < lvl + n
    then (* variable corresponds to a substituted term, replace it *)
      let e = List.nth es (k - lvl) in
      mention assumptions e
    else
      {term = Bound (k - n); assumptions; loc}
      (* this is a variable bound in an abstraction outside the
         instantiated term, so it remains bound, but its index decreases
         by the number of bound variables replaced by terms *)

let instantiate_hyps es =
  let hs = List.map gather_assumptions es in
  fun ~lvl h -> Assumption.instantiate hs lvl h

let instantiate es ?(lvl=0) e =
  if es = [] then e else
  at_var instantiate_atom (instantiate_bound es) (instantiate_hyps es) ~lvl e

let instantiate_ty es ?(lvl=0) (Ty t) =
  let t = instantiate es ~lvl t
  in Ty t

let unabstract xs ?(lvl=0) e =
  let es = List.map (mk_atom ~loc:Location.unknown) xs
  in instantiate es ~lvl e

let unabstract_ty xs ?(lvl=0) (Ty t) =
  let t = unabstract xs ~lvl t
  in Ty t


(** Abstract *)
let abstract_atom xs ~lvl x assumptions loc =
  begin
    match Name.index_of_atom x xs with
      | None -> {term=Atom x;assumptions;loc}
      | Some k -> {term = Bound (lvl + k); assumptions; loc}
  end

let abstract_bound ~lvl k assumptions loc =
  {term=Bound k;assumptions;loc}

let abstract_hyps xs ~lvl h =
  Assumption.abstract xs lvl h

let abstract xs ?(lvl=0) e =
  if xs = [] then e else
  at_var (abstract_atom xs) abstract_bound (abstract_hyps xs) ~lvl e

let abstract_ty xs ?(lvl=0) (Ty t) =
  let t = abstract xs ~lvl t
  in Ty t

(** Substitute *)
let substitute xs es t =
  if xs = [] && es = []
  then t
  else
    let t = abstract xs ~lvl:0 t in
    instantiate es ~lvl:0 t

let substitute_ty xs es (Ty ty) =
  Ty (substitute xs es ty)

(** Occurs (for printing) *)
let occurs_abstraction occurs_u occurs_v k ((x,u), v) =
  occurs_u k u + occurs_v (k+1) v

(* How many times does bound variable [k] occur in an expression? Used only for printing. *)
let rec occurs k {term=e';loc;_} =
  match e' with
  | Type -> 0
  | Atom _ -> 0
  | Bound m -> if k = m then 1 else 0
  | Constant x -> 0
  | Lambda a -> occurs_abstraction occurs_ty occurs_term_ty k a
  | Apply (e1, xtst, e2) ->
    occurs k e1 +
    occurs_abstraction occurs_ty occurs_ty k xtst +
    occurs k e2
  | Prod a ->
    occurs_abstraction occurs_ty occurs_ty k a
  | Eq (t, e1, e2) ->
    occurs_ty k t + occurs k e1 + occurs k e2
  | Refl (t, e) ->
    occurs_ty k t + occurs k e
  | Signature s -> occurs_sig k s
  | Structure (s, es) -> occurs_sig k s + occurs_struct k es
  | Projection (e,s,_) -> occurs k e + occurs_sig k s

and occurs_ty k (Ty t) = occurs k t

and occurs_shares k shares =
  let rec fold acc k = function
    | [] -> acc
    | (Unconstrained _) :: shares -> fold acc (k+1) shares
    | (Constrained e) :: shares -> let acc = acc + occurs k e in fold acc k shares
  in
  fold 0 k shares

and occurs_sig k (_,shares) = occurs_shares k shares

and occurs_struct k es =
  let rec fold acc = function
    | [] -> acc
    | e :: es ->
      let acc = acc + occurs k e in
      fold acc es
  in
  fold 0 es

and occurs_term_ty k (e, t) =
  occurs k e + occurs_ty k t

let occurs_ty_abstraction f = occurs_abstraction occurs_ty f

(****** Alpha equality ******)

let alpha_equal_abstraction alpha_equal_u alpha_equal_v ((x,u), v) ((x,u'), v') =
  alpha_equal_u u u' &&
  alpha_equal_v v v'

let rec alpha_equal {term=e1;_} {term=e2;_} =
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

    | Type, Type -> true

    | Prod abs, Prod abs' ->
      alpha_equal_abstraction alpha_equal_ty alpha_equal_ty abs abs'

    | Eq (t, e1, e2), Eq (t', e1', e2') ->
      alpha_equal_ty t t' &&
      alpha_equal e1 e1' &&
      alpha_equal e2 e2'

    | Refl (t, e), Refl (t', e') ->
      alpha_equal_ty t t' &&
      alpha_equal e e'

    | Signature s1, Signature s2 ->
      alpha_equal_sig s1 s2

    | Structure (s1, lst1), Structure (s2, lst2) ->
      alpha_equal_sig s1 s2 &&
      alpha_equal_struct lst1 lst2

    | Projection (e1, s1, l1), Projection (e2, s2, l2) ->
       Name.eq_ident l1 l2 &&
       alpha_equal_sig s1 s2 &&
       alpha_equal e1 e2

    | (Atom _ | Bound _ | Constant _ | Lambda _ | Apply _ |
        Type | Prod _ | Eq _ | Refl _ |
        Signature _ | Structure _ | Projection _), _ ->
      false
  end

and alpha_equal_ty (Ty t1) (Ty t2) = alpha_equal t1 t2

and alpha_equal_sig (s1,shares1) (s2,shares2) =
  Name.eq_ident s1 s2 &&
  let rec fold lst1 lst2 = match lst1, lst2 with
    | [], [] -> true
    | (Unconstrained _)::lst1, (Unconstrained _)::lst2 -> fold lst1 lst2
    | (Constrained e1) :: lst1, (Constrained e2) :: lst2 ->
      alpha_equal e1 e2 &&
      fold lst1 lst2
    | (Unconstrained _) :: _, (Constrained _) :: _ | (Constrained _) :: _, (Unconstrained _) :: _ -> false
    | [], _:: _ | _ :: _, [] -> Error.impossible ~loc:Location.unknown "alpha_equal_sig: malformed signatures"
  in
  fold shares1 shares2

and alpha_equal_struct es1 es2 =
  let rec fold es1 es2 = match es1, es2 with
    | [], [] -> true
    | e1 :: es1, e2 :: es2 ->
      alpha_equal e1 e2 &&
      fold es1 es2
    | [], _ :: _ | _ :: _, [] -> false
  in
  fold es1 es2

and alpha_equal_term_ty (e, t) (e', t') = alpha_equal e e' && alpha_equal_ty t t'

(****** Printing routines *****)
type print_env =
  { forbidden : Name.ident list ;
    sigs : Name.signature -> Name.label list }

type name_printing =
  | As_atom of Name.atom
  | As_ident of Name.ident

let add_forbidden x penv = { penv with forbidden = x :: penv.forbidden }

(** Optionally print a typing annotation in brackets. *)
let print_annot ?(prefix="") k ppf =
  if !Config.annotate then
    Format.fprintf ppf "%s[@[%t@]]" prefix k
  else
    Format.fprintf ppf ""

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

let print_label l x ppf =
  if Name.eq_ident l x
  then Format.fprintf ppf "%t" (Name.print_ident l)
  else Format.fprintf ppf "%t as %t" (Name.print_ident l) (Name.print_ident x)

let rec print_term ?max_level ~penv {term=e;assumptions;_} ppf =
  if !Config.print_dependencies && not (Assumption.is_empty assumptions)
  then
    Format.fprintf ppf "(%t)^{{%t}}"
                (print_term' ~penv ~max_level:Level.highest e)
                (Assumption.print penv.forbidden assumptions)
  else
    print_term' ~penv ?max_level e ppf

and print_term' ~penv ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
    match e with
      | Type ->
        Format.fprintf ppf "Type"

      | Atom x ->
        Name.print_atom x ppf

      | Constant x ->
         Name.print_ident x ppf

      | Bound k -> Name.print_debruijn penv.forbidden k ppf

      | Lambda a -> print_lambda ?max_level ~penv a ppf

      | Apply (e1, _, e2) -> print_app ?max_level ~penv e1 e2 ppf

      | Prod xts -> print_prod ?max_level ~penv xts ppf

      | Eq (t, e1, e2) ->
        print ~at_level:Level.eq "%t@ %s%t@ %t"
          (print_term ~max_level:Level.eq_left ~penv e1)
          (Print.char_equal ())
          (print_annot (print_ty ~penv t))
          (print_term ~max_level:Level.eq_right ~penv e2)

      | Refl (t, e) ->
        print ~at_level:Level.app "refl%t@ %t"
          (print_annot (print_ty ~penv t))
          (print_term ~max_level:Level.app_right ~penv  e)

      | Signature s ->
        print_sig ~penv s ppf

      | Structure (s, es) ->
         print_structure ?max_level ~penv s es ppf

      | Projection (e, s, l) ->
         print ~at_level:Level.proj "%t%t.%t"
               (print_term ~max_level:Level.proj_left ~penv e)
               (print_annot (print_sig ~penv s))
               (Name.print_ident l)

and print_ty ?max_level ~penv (Ty t) ppf = print_term ?max_level ~penv t ppf

(** [print_app e1 e2 ppf] prints the application [e1 e2] using formatter [ppf],
    possibly as a prefix or infix operator. *)
and print_app ?max_level ~penv e1 e2 ppf =
  let e1_prefix =
    match e1.term with
    | Bound k ->
       begin
         match List.nth penv.forbidden k with
         | Name.Ident (_, Name.Prefix) as op -> Some (As_ident op)
         | Name.Ident (_, _) -> None
         | exception Failure "nth" -> None
       end
    | Constant (Name.Ident (_, Name.Prefix) as op) -> Some (As_ident op)
    | Atom (Name.Atom (_, Name.Prefix, _) as op) -> Some (As_atom op)

    | Constant (Name.Ident (_, (Name.Word | Name.Anonymous | Name.Infix _)))
    | Atom (Name.Atom (_, (Name.Word | Name.Anonymous | Name.Infix _), _))
    | Type | Lambda _ | Apply _ | Prod _ | Eq _ | Refl _ | Signature _
    | Structure _ | Projection _ ->
      None
  in
  match e1_prefix with
  | Some (As_atom op) ->
     Print.print ppf ?max_level ~at_level:Level.prefix "%t@ %t"
                 (Name.print_atom ~parentheses:false op)
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
           match e1.term with
           | Apply ({term=Bound k; _}, _, e1) ->
              begin
                match List.nth penv.forbidden k with
                | Name.Ident (_, Name.Infix fixity) as op ->
                   Some (As_ident op, fixity, e1)
                | Name.Ident (_, (Name.Word | Name.Anonymous | Name.Prefix)) -> None
                | exception Failure "nth" -> None
              end
           | Apply ({term=Constant (Name.Ident (_, Name.Infix fixity) as op);_},
                    _, e1) ->
              Some (As_ident op, fixity, e1)
           | Apply ({term=Atom (Name.Atom (_, Name.Infix fixity, _) as op);_},
                    _, e1) ->
              Some (As_atom op, fixity, e1)

           | Apply _ (* Spelling out exactly which cases are not covered is quite
                        verbose, so we do not do it. *)
           | Type | Lambda _ | Prod _ | Eq _ | Refl _ | Signature _
           | Structure _ | Projection _ | Atom _ | Constant _ | Bound _ ->
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
                       | As_atom op -> Name.print_atom ~parentheses:false op)
                      (print_term ~max_level:lvl_right ~penv e2)
       | None ->
          (* ordinary application *)
          Print.print ppf ?max_level ~at_level:Level.app "%t@ %t"
                       (print_term ~max_level:Level.app_left ~penv e1)
                       (print_term ~max_level:Level.app_right ~penv e2)
     end


(** [print_lambda a e t ppf] prints a lambda abstraction using formatter [ppf]. *)
and print_lambda ?max_level ~penv ((x, u), (e, _)) ppf =
  let x = (if occurs 0 e = 0 then Name.anonymous else x) in
  let rec collect xus e =
    match e.term with
    | Lambda ((x, u), (e, _)) ->
       let x = (if occurs 0 e = 0 then Name.anonymous else x) in
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
  if occurs_ty 0 t = 0 then
    Print.print ?max_level ~at_level:Level.arr ppf "%t@ %s@ %t"
          (print_ty ~max_level:Level.arr_left ~penv u)
          (Print.char_arrow ())
          (print_ty ~max_level:Level.arr_right ~penv:(add_forbidden Name.anonymous penv) t)
  else
    let rec collect xus ((Ty t) as t_ty) =
      match t.term with
      | Prod ((x, u), t_ty) when occurs_ty 0 t_ty > 0 ->
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

and print_sig_clause penv x y t ppf =
  if Name.eq_ident x y then
    Format.fprintf ppf "@[<hov>%t :@ %t@]"
      (Name.print_ident x)
      (print_ty ~max_level:Level.sig_clause ~penv t)
  else
    Format.fprintf ppf "@[<hov>%t as %t :@ %t@]"
      (Name.print_ident x)
      (Name.print_ident y)
      (print_ty ~max_level:Level.sig_clause ~penv t)

and print_sig_def ~penv xts ppf =
  match xts with
  | [] -> ()
  | [x,y,t] ->
     let y = Name.refresh penv.forbidden y in
     print_sig_clause penv x y t ppf
  | (x,y,t) :: lst ->
     let y = Name.refresh penv.forbidden y in
     Print.print ppf "%t,@ %t"
        (print_sig_clause penv x y t)
        (print_sig_def ~penv:(add_forbidden y penv) lst)

and print_share ~penv lshare ppf = match lshare with
  | l, Unconstrained x -> print_label l x ppf
  | l, Constrained e -> Format.fprintf ppf "%t@ =@ %t" (Name.print_ident l) (print_term ~penv e)

and print_selected_shares ~penv lshares ppf =
  match lshares with
  | [] -> ()
  | (_,None) :: lshares ->
    print_selected_shares ~penv:(add_forbidden Name.anonymous penv) lshares ppf
  | (l,Some share) :: rem when (List.for_all (fun (_,maybe) -> maybe = None) rem) ->
    print_share ~penv (l,share) ppf
  | (l, Some ((Unconstrained x) as share)) :: lshares ->
    let x = Name.refresh penv.forbidden x in
    Format.fprintf ppf "%t,@ %t" (print_share ~penv (l,share))
                                 (print_selected_shares ~penv:(add_forbidden x penv) lshares)
  | (l, Some ((Constrained _) as share)) :: lshares ->
    Format.fprintf ppf "%t,@ %t" (print_share ~penv (l,share))
                                 (print_selected_shares ~penv lshares)

and print_shares ~penv s_def shares ppf =
  let rec select acc = function
    | [] -> List.rev acc
    | ((Unconstrained x) as share) :: shares ->
      if occurs_shares 0 shares > 0
      then
        select (Some share :: acc) shares
      else
        select (None::acc) shares
    | ((Constrained _) as share) :: shares ->
      select (Some share :: acc) shares
  in
  let lshares = List.combine s_def (select [] shares) in
  print_selected_shares ~penv lshares ppf

and print_sig ~penv (s,shares) ppf =
  if List.for_all (function | Unconstrained _ -> true | Constrained _ -> false) shares
  then
    Name.print_ident s ppf
  else
    Format.fprintf ppf "{@[<hv>%t with %t@]}" (Name.print_ident s) (print_shares ~penv (penv.sigs s) shares)

and print_structure_clause ~penv (l,e) ppf =
  Format.fprintf ppf "@[<hov>%t@ =@ %t@]"
                 (Name.print_ident l)
                 (print_term ~max_level:Level.struct_clause ~penv e)

and print_structure ?max_level ~penv (s,shares) es ppf =
  let ls = penv.sigs s in
  let rec fold acc es ls shares = match ls, shares with
    | [], [] -> List.rev acc
    | _::ls, (Constrained _) :: shares -> fold acc es ls shares
    | l::ls, (Unconstrained _) :: shares ->
      begin match es with
        | [] -> Error.impossible ~loc:Location.unknown "print_structure: malformed structure"
        | e::es -> fold ((l,e)::acc) es ls shares
      end
    | _::_, [] | [], _ :: _ -> Error.impossible ~loc:Location.unknown "print_structure: malformed signature"
  in
  let les = fold [] es ls shares in
  Print.print ppf "{@[<hv>%t@]}"
       (Print.sequence (print_structure_clause ~penv) "," les)

(****** Structure stuff ********)

type struct_field =
  | Shared of term
  | Explicit of term

let struct_combine ~loc ((_,shares),es) =
  (* [fields] is the return
     [exs] are the previous explicit fields which instantiate constraints
     [es] are the remaining explicit fields
     We assume we work on a valid structure so no need to check that no [es] remain at the end. *)
  let rec fold fields exs es = function
    | [] -> List.rev fields
    | (Constrained e) :: shares ->
      let e = instantiate exs e in
      fold ((Shared e)::fields) exs es shares
    | (Unconstrained _) :: shares ->
      begin match es with
        | [] -> Error.impossible ~loc "struct_combine: malformed structure"
        | e::es -> fold ((Explicit e)::fields) (e::exs) es shares
      end
  in
  fold [] [] es shares

let field_value ~loc s_def str p =
  let rec fold vs def fields = match def, fields with
    | (l,_,_)::_, e :: _ when Name.eq_ident p l ->
      begin match e with
        | Shared e -> instantiate vs e
        | Explicit e -> e
      end
    | _::def, e :: fields ->
      begin match e with
        | Shared e -> fold vs def fields
        | Explicit e -> fold (e::vs) def fields
      end
    | [], [] -> Error.impossible ~loc "field_value: no such field %t" (Name.print_ident p)
    | [], _ :: _ | _ :: _, [] -> Error.impossible ~loc "field_value: malformed structure"
  in
  fold [] s_def (struct_combine ~loc str)

let field_project ~loc s_def ((_,shares) as s) trm p =
  (* The [vs] instantiate the internal `as x` names in the signature definition,
     the [projs] instantiate the labels in the constraints *)
  let rec fold vs projs = function
    | ((l,_,t),e)::rem ->
      if Name.eq_ident p l
      then
        let e = match e with
          | Constrained e -> instantiate projs e
          | Unconstrained _ -> mk_projection ~loc trm s l
        and t = instantiate_ty vs t in
        e,t
      else
        let e,projs = match e with
          | Constrained e -> instantiate projs e,projs
          | Unconstrained _ ->
            let e = mk_projection ~loc trm s l in
            e,(e::projs)
        in
        fold (e::vs) projs rem
    | [] -> Error.impossible ~loc "field_type: no such field %t" (Name.print_ident p)
    in
  fold [] [] (List.combine s_def shares)

