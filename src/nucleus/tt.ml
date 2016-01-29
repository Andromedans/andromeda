(** The abstract syntax of Andromedan type theory (TT). *)

type ('a, 'b) abstraction = (Name.ident * 'a) * 'b

type term = {
  term : term';
  (* raw term *)

  assumptions : Assumption.t;
  (* set of atoms on which the term dependsassumptions on the subterms *)

  loc : Location.t
  (* the location in input where the term appeared, as much as that makes sense *)
}

and term' =
  | Type
  | Atom of Name.atom
  | Bound of Syntax.bound
  | Constant of Name.ident
  | Lambda of (term * ty) ty_abstraction
  | Apply of term * ty ty_abstraction * term
  | Prod of ty ty_abstraction
  | Eq of ty * term * term
  | Refl of ty * term
  | Signature of signature
  | Structure of structure
  | Projection of term * signature * Name.ident

and ty = Ty of term

and 'a ty_abstraction = (ty, 'a) abstraction

and signature = (Name.ident * Name.ident * ty) list

and structure = (Name.ident * Name.ident * ty * term) list

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)

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
  assumptions=Assumption.empty ;
  loc = loc
}

let mk_prod ~loc x a b = {
  term = Prod ((x, a), b) ;
  assumptions=Assumption.empty ;
  loc = loc
}

let mk_apply ~loc e1 x a b e2 = {
  term = Apply (e1, ((x, a),b), e2);
  assumptions = Assumption.empty;
  loc = loc
}

let mk_type ~loc =
  { term = Type;
    assumptions = Assumption.empty;
    loc = loc }

let mk_eq ~loc t e1 e2 =
  { term = Eq (t, e1, e2);
    assumptions = Assumption.empty;
    loc = loc }

let mk_refl ~loc t e =
  { term = Refl (t, e);
    assumptions = Assumption.empty;
    loc = loc }

let mk_signature ~loc lst =
  { term = Signature lst;
    assumptions = Assumption.empty;
    loc = loc }

let mk_structure ~loc lst =
  { term = Structure lst;
    assumptions = Assumption.empty;
    loc = loc }

let mk_projection ~loc te xts x =
  { term = Projection (te,xts,x);
    assumptions = Assumption.empty;
    loc = loc }

(** Convert a term to a type. *)
let ty e = Ty e

let mk_eq_ty ~loc t e1 e2 = ty (mk_eq ~loc t e1 e2)
let mk_prod_ty ~loc x a b = ty (mk_prod ~loc x a b)
let mk_type_ty ~loc = ty (mk_type ~loc)
let mk_signature_ty ~loc lst = ty (mk_signature ~loc lst)

(** The [Type] constant, without a location. *)
let typ = Ty (mk_type ~loc:Location.unknown)

let mention_atoms a e =
  { e with assumptions = Assumption.add_atoms a e.assumptions }

let mention a e =
  { e with assumptions = Assumption.union e.assumptions a }


let rec gather_assumptions_ty_abs : 'a. ('a -> Assumption.t) -> 'a ty_abstraction -> Assumption.t = fun gather_v ((x,u),v) ->
  let a1 = gather_assumptions_ty u in
  let a2 = gather_v v in
  Assumption.union a1 (Assumption.bind 1 a2)

and gather_assumptions {term=e;assumptions;_} =
  match e with
    | Type | Atom _ | Constant _ | Bound _ -> assumptions

    | Lambda a -> gather_assumptions_ty_abs gather_term_ty a

    | Apply (e1,xts,e2) ->
      let a1 = gather_assumptions e1
      and a2 = gather_assumptions_ty_abs gather_assumptions_ty xts
      and a3 = gather_assumptions e2 in
      Assumption.union a1 (Assumption.union a2 a3)

    | Prod a -> gather_assumptions_ty_abs gather_assumptions_ty a

    | Eq (t,e1,e2) ->
      let t = gather_assumptions_ty t
      and e1 = gather_assumptions e1
      and e2 = gather_assumptions e2 in
      Assumption.union assumptions (Assumption.union t (Assumption.union e1 e2))

    | Refl (t,e) ->
      let t = gather_assumptions_ty t
      and e = gather_assumptions e in
      Assumption.union assumptions (Assumption.union t e)

    | Signature xts ->
      let assumptions' = List.fold_left (fun assumptions (l,x,t) ->
          let assumptions = Assumption.bind 1 assumptions in
          let t = gather_assumptions_ty t in
          Assumption.union assumptions t)
        Assumption.empty (List.rev xts)
      in
      Assumption.union assumptions assumptions'

    | Structure xtes ->
      let assumptions' = List.fold_left (fun assumptions (l,x,t,e) ->
          let assumptions = Assumption.bind 1 assumptions in
          let t = gather_assumptions_ty t
          and e = gather_assumptions e in
          Assumption.union assumptions (Assumption.union e t))
        Assumption.empty (List.rev xtes)
      in
      Assumption.union assumptions assumptions'

    | Projection (e,xts,l) ->
      let assumptions' = List.fold_left (fun assumptions (l,x,t) ->
          let assumptions = Assumption.bind 1 assumptions in
          let t = gather_assumptions_ty t in
          Assumption.union assumptions t)
        Assumption.empty (List.rev xts)
      in
      let e = gather_assumptions e in
      Assumption.union assumptions (Assumption.union e assumptions')

and gather_assumptions_ty (Ty t) = gather_assumptions t

and gather_term_ty (e,t) =
  let a = gather_assumptions e
  and a' = gather_assumptions_ty t in
  Assumption.union a a'

let assumptions_term ({loc;_} as e) =
  let a = gather_assumptions e in
  Assumption.as_atom_set ~loc a

let assumptions_ty (Ty t) = assumptions_term t


(** Manipulation of variables *)
let rec at_var atom bound hyps ~lvl {term=e';assumptions;loc} =
  let assumptions = hyps ~lvl assumptions in
  match e' with
    | Type | Constant _ as term -> {term;assumptions;loc}
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
    | Signature xts ->
      let xts = at_var_sig atom bound hyps ~lvl xts in
      let term = Signature xts in
      {term;assumptions;loc}
    | Structure xtes ->
      let xtes = at_var_struct atom bound hyps ~lvl xtes in
      let term = Structure xtes in
      {term;assumptions;loc}
    | Projection (e,xts,l) ->
      let e = at_var atom bound hyps ~lvl e
      and xts = at_var_sig atom bound hyps ~lvl xts in
      let term = Projection (e,xts,l) in
      {term;assumptions;loc}

and at_var_ty atom bound hyps ~lvl (Ty a) =
  Ty (at_var atom bound hyps ~lvl a)

and at_var_sig atom bound hyps ~lvl xts =
  let rec fold ~lvl xts = function
    | [] ->
      List.rev xts
    | (l,x,a)::rem ->
      let a = at_var_ty atom bound hyps ~lvl a in
      fold ~lvl:(lvl+1) ((l,x,a)::xts) rem
  in
  fold ~lvl [] xts

and at_var_struct atom bound hyps ~lvl xtes =
  let rec fold ~lvl xtes = function
    | [] ->
      List.rev xtes
    | (l,x,a,e)::rem ->
      let a = at_var_ty atom bound hyps ~lvl a
      and e = at_var atom bound hyps ~lvl e in
      fold ~lvl:(lvl+1) ((l,x,a,e)::xtes) rem
  in
  fold ~lvl [] xtes

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
let rec occurs k {term=e';_} =
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
  | Signature xts ->
    let rec fold k res = function
      | [] -> res
      | (x,y,t)::rem ->
        let i = occurs_ty k t in
        fold (k+1) (res+i) rem
      in
    fold k 0 xts
  | Structure xts ->
    let rec fold k res = function
      | [] -> res
      | (x,y,t,te)::rem ->
        let i = occurs_ty k t in
        let j = occurs k te in
        fold (k+1) (res+i+j) rem
      in
    fold k 0 xts

  | Projection (te,xts,p) ->
    let rec fold k res = function
      | [] -> res
      | (x,y,t)::rem ->
        let i = occurs_ty k t in
        fold (k+1) (res+i) rem
      in
    fold k (occurs k te) xts

and occurs_ty k (Ty t) = occurs k t

and occurs_term_ty k (e, t) =
  occurs k e + occurs_ty k t

let occurs_ty_abstraction f = occurs_abstraction occurs_ty f


(****** Alpha equality ******)

(* Currently, the only difference between alpha and structural equality is that
   the names of variables in abstractions are ignored. *)
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

    | Signature xts1, Signature xts2 ->
      let rec fold xts1 xts2 = match xts1, xts2 with
        | [], [] -> true
        | (x1,_,t1)::xts1, (x2,_,t2)::xts2 ->
          Name.eq_ident x1 x2 &&
          alpha_equal_ty t1 t2 &&
          fold xts1 xts2
        | _::_,[] | [],_::_ -> false
        in
      fold xts1 xts2

    | Structure xts1, Structure xts2 ->
      let rec fold xts1 xts2 = match xts1, xts2 with
        | [], [] -> true
        | (x1,_,t1,te1)::xts1, (x2,_,t2,te2)::xts2 ->
          Name.eq_ident x1 x2 &&
          alpha_equal_ty t1 t2 &&
          alpha_equal te1 te2 &&
          fold xts1 xts2
        | _::_,[] | [],_::_ -> false
        in
      fold xts1 xts2

    | Projection (te1,xts1,p1), Projection (te2,xts2,p2) ->
      Name.eq_ident p1 p2 &&
      alpha_equal te1 te2 &&
      let rec fold xts1 xts2 = match xts1, xts2 with
        | [], [] -> true
        | (x1,_,t1)::xts1, (x2,_,t2)::xts2 ->
          Name.eq_ident x1 x2 &&
          alpha_equal_ty t1 t2 &&
          fold xts1 xts2
        | _::_,[] | [],_::_ -> false
        in
      fold xts1 xts2

    | (Atom _ | Bound _ | Constant _ | Lambda _ | Apply _ |
        Type | Prod _ | Eq _ | Refl _ |
        Signature _ | Structure _ | Projection _), _ ->
      false
  end

and alpha_equal_ty (Ty t1) (Ty t2) = alpha_equal t1 t2

and alpha_equal_term_ty (e, t) (e', t') = alpha_equal e e' && alpha_equal_ty t t'


(****** Printing routines *****)

(** Optionally print a typing annotation in brackets. *)
let print_annot ?(prefix="") k ppf =
  if !Config.annotate then
    Format.fprintf ppf "%s[@[%t@]]" prefix k
  else
    Format.fprintf ppf ""

(*

  Level 0: Type, name, bound
  Level 1: apply (0,0), refl (0)
  Level 2: eq (1,1)
  Level 3: lambda, prod, arrow

  let, ascribe

*)

let rec print_term ?max_level xs {term=e;assumptions;_} ppf =
  if !Config.print_dependencies && not (Assumption.is_empty assumptions)
  then
    Print.print ppf ?max_level ~at_level:3 "(%t)^{{%t}}"
                (print_term' ~max_level:3 xs e)
                (Assumption.print xs assumptions)
  else
    print_term' ?max_level xs e ppf

and print_term' ?max_level xs e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
    match e with
      | Type ->
        print ~at_level:0 "Type"

      | Atom x ->
        print ~at_level:0 "%t" (Name.print_atom x)

      | Constant x ->
        print ~at_level:0 "%t" (Name.print_ident x)

      | Bound k ->
        begin
          try
            if !Config.debruijn
            then print ~at_level:0 "%t[%d]" (Name.print_ident (List.nth xs k)) k
            else print ~at_level:0 "%t" (Name.print_ident (List.nth xs k))
          with
          | Not_found | Failure "nth" ->
              (** XXX this should never get printed *)
              print ~at_level:0 "DEBRUIJN[%d]" k
        end

      | Lambda a -> print ~at_level:3 "%t" (print_lambda xs a)

      | Apply (e, xtst, es) -> print ~at_level:1 "%t" (print_apply xs e xtst es)

      | Prod xts -> print ~at_level:3 "%t" (print_prod xs xts)

      | Eq (t, e1, e2) ->
        print ~at_level:2 "@[<hv 2>%t@ %s%t %t@]"
          (print_term ~max_level:1 xs e1)
          (Print.char_equal ())
          (print_annot (print_ty xs t))
          (print_term ~max_level:1 xs e2)

      | Refl (t, e) ->
        print ~at_level:1 "refl%t %t"
          (print_annot (print_ty xs t))
          (print_term ~max_level:0 xs e)

      | Signature xts ->
        print ~at_level:0 "{@[<hov>%t@]}"
          (print_signature xs xts)

      | Structure [] -> print ~at_level:0 "()"

      | Structure xts ->
        print ~at_level:0 "{@[<hov>%t@]}"
          (print_structure xs xts)

      | Projection (te,xts,p) -> print ~at_level:1 "%t" (print_projection xs te xts p)

and print_ty ?max_level xs (Ty t) ppf = print_term ?max_level xs t ppf

(** [print_lambda a e t ppf] prints a lambda abstraction using formatter [ppf]. *)
and print_lambda xs (yus, (e, t)) ppf =
  Print.print ppf "@[<hov 2>%s %t@]"
    (Print.char_lambda ())
    (Name.print_binders
      (Name.print_binder1 print_ty)
      (fun xs ppf -> Print.print ppf "%t@ %t"
        (print_annot (print_ty xs t))
        (print_term xs e))
      xs
      yus)

(** [print_prod xs ts t ppf] prints a dependent product using formatter [ppf]. *)
and print_prod xs ((y,u),t) ppf =
  if occurs_ty 0 t > 0
  then
    Print.print ppf "@[<hov 2>%s %t@]"
      (Print.char_prod ())
      (Name.print_binders
        (Name.print_binder1 print_ty)
        (fun xs -> print_ty xs t)
        xs (y,u))
  else
    Print.print ppf "@[<hov 2>%t@ %s@ %t@]"
          (print_ty ~max_level:2 xs u)
          (Print.char_arrow ())
          (print_ty (Name.anonymous::xs) t)

and print_apply xs e1 (yts, u) e2 ppf =
  let rec collect_args es e =
    match e.term with
    | Apply (e, _, e') -> collect_args (e' :: es) e
    | (Type | Atom _ | Bound _ | Constant _ | Lambda _
    | Prod _ | Eq _ | Refl _ | Signature _ | Structure _ | Projection _) ->
       e, es
  in
  let e, es = collect_args [e2] e1 in
  Print.print ppf "@[<hov 2>%t@ %t@]"
              (print_term ~max_level:0 xs e)
              (Print.sequence (print_term ~max_level:0 xs) "" es)

and print_signature_clause xs x y t ppf =
  if Name.eq_ident x y then
    Print.print ppf "@[<h>%t :@ %t@]"
      (Name.print_ident x)
      (print_ty xs t)
  else
    Print.print ppf "@[<h>%t as %t :@ %t@]"
      (Name.print_ident x)
      (Name.print_ident y)
      (print_ty xs t)

and print_signature xs xts ppf =
  match xts with
  | [] -> ()
  | [x,y,t] -> 
     let y = Name.refresh xs y in
     print_signature_clause xs x y t ppf
  | (x,y,t) :: lst ->
     let y = Name.refresh xs y in
     Print.print ppf "%t,@ %t"
        (print_signature_clause xs x y t)
        (print_signature (y::xs) lst)

and print_structure_clause xs x y t te ppf =
  if Name.eq_ident x y then
    Print.print ppf "@[<h>%t%t@ :=@ %t@]"
      (Name.print_ident x)
      (print_annot ~prefix:" " (print_ty xs t))
      (print_term xs te)
  else
    Print.print ppf "@[<h>%t as %t%t@ := %t@]"
      (Name.print_ident x)
      (Name.print_ident y)
      (print_annot ~prefix:" " (print_ty xs t))
      (print_term xs te)

and print_structure xs xts ppf =
  match xts with
  | [] -> ()
  | [x,y,t,te] -> 
     let y = Name.refresh xs y in
     print_structure_clause xs x y t te ppf
  | (x,y,t,te) :: lst ->
     let y = Name.refresh xs y in
     Print.print ppf "%t,@ %t"
        (print_structure_clause xs x y t te)
        (print_structure (y::xs) lst)

and print_projection xs te xts p ppf =
  if !Config.annotate
  then
    Print.print ppf "@[<hov 2>%t@ @@{%t}.%t@]"
      (print_term ~max_level:0 xs te)
      (print_signature xs xts)
      (Name.print_ident p)
  else
    Print.print ppf "@[<hov 2>%t@ .%t@]"
      (print_term ~max_level:0 xs te)
      (Name.print_ident p)

(****** Structure stuff ********)

let field_value ~loc xtes p =
  let rec fold vs = function
    | [] -> Error.impossible ~loc "Tt.field_value: field %t not found" (Name.print_ident p)
    | (l,x,t,te)::rem ->
      let te = instantiate vs te in
      if Name.eq_ident p l
      then te
      else fold (te::vs) rem
    in
  fold [] xtes

let field_type ~loc xts e p =
  let rec fold vs = function
    | [] -> Error.typing ~loc "%t has no field %t" (print_term [] e) (Name.print_ident p)
    | (l,x,t)::rem ->
      if Name.eq_ident p l
      then instantiate_ty vs t
      else
        let el = mk_projection ~loc e xts l in
        fold (el::vs) rem
    in
  fold [] xts

