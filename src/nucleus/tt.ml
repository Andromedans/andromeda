(** The abstract syntax of Andromedan type theory (TT). *)

type ('a, 'b) abstraction = (Name.ident * 'a) list * 'b

type term = { term : term' ; loc : Location.t}
and term' =
  | Type
  | Atom of Name.atom
  | Bound of Syntax.bound
  | Constant of Name.ident * term list
  | Lambda of (term * ty) ty_abstraction
  | Spine of term * ty ty_abstraction * term list
  | Prod of ty ty_abstraction
  | Eq of ty * term * term
  | Refl of ty * term
  | Inhab of ty
  | Bracket of ty
  | Signature of signature
  | Structure of structure
  | Projection of term * signature * Name.ident

and ty = Ty of term

and 'a ty_abstraction = (ty, 'a) abstraction

and signature = (Name.ident * Name.ident * ty) list

and structure = (Name.ident * Name.ident * ty * term) list

type constsig = ((bool * ty), ty) abstraction

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)
let mk_atom ~loc x = {term = Atom x; loc}
let mk_bound ~loc k ={term = Bound k; loc}

let mk_constant ~loc x es = {term = Constant (x, es); loc}

let mk_lambda ~loc xts e t =
  match xts with
  | [] -> e
  | _ :: _ -> {term = Lambda (xts, (e, t)); loc}

let mk_prod ~loc xts ((Ty e) as t) =
  match xts with
  | [] -> e
  | _ :: _ ->
    begin match t with
    (* XXX join locations loc and loc' *)
    | Ty {term=Prod (yts, t); loc=loc'} -> {term = Prod (xts @ yts, t); loc}
    | t -> {term = Prod (xts, t); loc}
    end

let mk_spine ~loc e xts t es =
  match xts with
    | [] -> {term = e.term; loc}
    | _::_ -> {term = Spine (e, (xts, t), es); loc}

let mk_type ~loc = {term = Type; loc}
let mk_eq ~loc t e1 e2 = {term = Eq (t, e1, e2); loc}
let mk_refl ~loc t e = {term = Refl (t, e); loc}

let mk_inhab ~loc t = {term = Inhab t; loc}
let mk_bracket ~loc t = {term = Bracket t; loc}

let mk_signature ~loc lst = {term = Signature lst; loc}
let mk_structure ~loc lst = {term = Structure lst; loc}
let mk_projection ~loc te xts x = {term = Projection (te,xts,x); loc}

(** Convert a term to a type. *)
let ty e = Ty e

let mk_eq_ty ~loc t e1 e2 = ty (mk_eq ~loc t e1 e2)
let mk_prod_ty ~loc xts t = ty (mk_prod ~loc xts t)
let mk_type_ty ~loc = ty (mk_type ~loc)
let mk_bracket_ty ~loc t = ty (mk_bracket ~loc t)
let mk_signature_ty ~loc lst = ty (mk_signature ~loc lst)

(** The [Type] constant, without a location. *)
let typ = Ty (mk_type ~loc:Location.unknown)


(** Manipulation of variables *)

let rec instantiate_ty_abstraction :
  'a. (term list -> ?lvl:int -> 'a -> 'a) ->
  term list -> ?lvl:int -> 'a ty_abstraction -> 'a ty_abstraction
  = fun instantiate_v es ?(lvl=0) (xus, v) ->
    let rec inst acc lvl = function
      | [] ->
         let v = instantiate_v es ~lvl v
         in List.rev acc, v
      | (x,u) :: xus ->
         let u = instantiate_ty es ~lvl u in
         inst ((x,u) :: acc) (lvl+1) xus
    in
    inst [] lvl xus

and instantiate es ?(lvl=0) ({term=e';loc;} as e) =
  (* XXX possible optimization: check whether [es] is empty *)
  if es = [] then e else
    match e' with

    | Type -> e

    | Atom _ -> e

    | Bound k ->
       if k < lvl
       then e
        (* this is a variable bound in an abstraction inside the
           instantiated term, so we leave it as it is *)
       else
         let n = List.length es in
         if k < lvl + n
         then List.nth es (k - lvl) (* variable corresponds to a substituted term, replace it *)
         else {term = Bound (k - n); loc}
          (* this is a variable bound in an abstraction outside the
             instantiated term, so it remains bound, but its index decreases
             by the number of bound variables replaced by terms *)

    | Constant (x, ds) ->
      let ds = List.map (instantiate es ~lvl) ds in
      {term = Constant (x, ds); loc}

    | Lambda a ->
       let a = instantiate_ty_abstraction instantiate_term_ty es ~lvl a in
       {term = Lambda a; loc}

    | Spine (e, xtst, ds) ->
       let e = instantiate es ~lvl e
       and xtst = instantiate_ty_abstraction instantiate_ty es ~lvl xtst
       and ds = List.map (instantiate es ~lvl) ds in
       {term = Spine (e, xtst, ds); loc}

    | Prod a ->
       let a = instantiate_ty_abstraction instantiate_ty es ~lvl a in
       {term = Prod a; loc}

    | Eq (t, e1, e2) ->
       let t = instantiate_ty es ~lvl t
       and e1 = instantiate es ~lvl e1
       and e2 = instantiate es ~lvl e2 in
       {term = Eq (t, e1, e2); loc}

    | Refl (t, e) ->
       let t = instantiate_ty es ~lvl t
       and e = instantiate es ~lvl e in
       {term = Refl (t, e); loc}

    | Inhab t ->
       let t = instantiate_ty es ~lvl t in
       {term = Inhab t; loc}

    | Bracket t ->
      let t = instantiate_ty es ~lvl t in
      {term = Bracket t; loc}

    | Signature xts ->
      let rec fold lvl res = function
        | [] -> List.rev res
        | (x,y,t)::rem ->
          let t = instantiate_ty es ~lvl t in
          fold (lvl+1) ((x,y,t)::res) rem
        in
      let xts = fold lvl [] xts in
      {term = Signature xts; loc}

    | Structure xts ->
      let rec fold lvl res = function
        | [] -> List.rev res
        | (x,y,t,te)::rem ->
          let t = instantiate_ty es ~lvl t in
          let te = instantiate es ~lvl te in
          fold (lvl+1) ((x,y,t,te)::res) rem
        in
      let xts = fold lvl [] xts in
      {term = Structure xts; loc}

    | Projection (te,xts,p) ->
      let te = instantiate es ~lvl te in
      let rec fold lvl res = function
        | [] -> List.rev res
        | (x,y,t)::rem ->
          let t = instantiate_ty es ~lvl t in
          fold (lvl+1) ((x,y,t)::res) rem
        in
      let xts = fold lvl [] xts in
      {term = Projection (te,xts,p); loc}

and instantiate_ty es ?(lvl=0) (Ty t) =
  let t = instantiate es ~lvl t
  in Ty t

and instantiate_term_ty es ?(lvl=0) (e, t) =
  let e = instantiate es ~lvl e
  and t = instantiate_ty es ~lvl t
  in (e, t)

let unabstract xs ?(lvl=0) e =
  let es = List.map (mk_atom ~loc:Location.unknown) xs
  in instantiate es ~lvl e

let rec unabstract_ty xs ?(lvl=0) (Ty t) =
  let t = unabstract xs ~lvl t
  in Ty t


let rec abstract_ty_abstraction :
  'a. (Name.atom list -> ?lvl:int -> 'a -> 'a) ->
  Name.atom list -> ?lvl:int -> 'a ty_abstraction -> 'a ty_abstraction
  = fun abst_v ys ?(lvl=0) (xus,v) ->
    let rec abst acc lvl = function
      | [] ->
         let v = abst_v ys ~lvl v
         in List.rev acc, v
      | (x,u) :: xus ->
         let u = abstract_ty ys ~lvl u in
         abst ((x,u) :: acc) (lvl+1) xus
    in
    abst [] lvl xus

and abstract xs ?(lvl=0) ({term=e';loc;} as e) =
  match e' with

  | Type -> e

  | Bound k -> e

  | Constant (y, es) ->
     let es = List.map (abstract xs ~lvl) es in
      {term = Constant (y, es); loc}

  | Atom x ->
    begin
      match Name.index_of_atom x xs with
      | None -> e
      | Some k -> {term = Bound (lvl + k); loc}
    end

  | Lambda a ->
    let a = abstract_ty_abstraction abstract_term_ty xs ~lvl a in
    {term = Lambda a; loc}

  | Spine (e, xtst, es) ->
    let e = abstract xs ~lvl e
    and xtst = abstract_ty_abstraction abstract_ty xs ~lvl xtst
    and es = List.map (abstract xs ~lvl) es in
    {term = Spine (e, xtst, es); loc}

  | Prod a ->
    let a = abstract_ty_abstraction abstract_ty xs ~lvl a in
    {term = Prod a; loc}

  | Eq (t, e1, e2) ->
    let t = abstract_ty xs ~lvl t
    and e1 = abstract xs ~lvl e1
    and e2 = abstract xs ~lvl e2 in
    {term = Eq (t, e1, e2); loc}

  | Refl (t, e) ->
    let t = abstract_ty xs ~lvl t
    and e = abstract xs ~lvl e in
    {term = Refl (t, e); loc}

  | Inhab t ->
    let t = abstract_ty xs ~lvl t in
    {term = Inhab t; loc}

  | Bracket t ->
    let t = abstract_ty xs ~lvl t in
    {term = Bracket t; loc}

  | Signature xts ->
     let rec fold lvl res = function
       | [] -> List.rev res
       | (x,y,t)::rem ->
          let t = abstract_ty xs ~lvl t in
          fold (lvl+1) ((x,y,t)::res) rem
     in
     let xts = fold lvl [] xts in
     {term = Signature xts; loc}

  | Structure xts ->
     let rec fold lvl res = function
       | [] -> List.rev res
       | (x,y,t,te)::rem ->
          let t = abstract_ty xs ~lvl t in
          let te = abstract xs ~lvl te in
          fold (lvl+1) ((x,y,t,te)::res) rem
     in
     let xts = fold lvl [] xts in
     {term = Structure xts; loc}

  | Projection (te,xts,p) ->
     let te = abstract xs ~lvl te in
     let rec fold lvl res = function
       | [] -> List.rev res
       | (x,y,t)::rem ->
          let t = abstract_ty xs ~lvl t in
          fold (lvl+1) ((x,y,t)::res) rem
     in
     let xts = fold lvl [] xts in
     {term = Projection (te,xts,p); loc}

and abstract_ty xs ?(lvl=0) (Ty t) =
  let t = abstract xs ~lvl t
  in Ty t

and abstract_term_ty xs ?(lvl=0) (e, t) =
  let e = abstract xs ~lvl e
  and t = abstract_ty xs ~lvl t
  in (e, t)

let shift_abstraction shift_u shift_v k lvl us v =
  let rec fold lvl us' = function
    | [] ->
      let v = shift_v k lvl v in
        List.rev us', v
    | (x,u)::us ->
      let u = shift_u k lvl u in
        fold (lvl+1) ((x,u) :: us') us
  in
    fold lvl [] us

let rec shift k lvl ({term=e';loc;} as e) =
  match e' with
    | (Type | Atom _) -> e

    | Bound j ->
      if lvl <= j
      then {term = Bound (j + k); loc}
      else e

    | Constant (x, es) ->
        let es = List.map (shift k lvl) es in
        {term = Constant (x, es); loc}

    | Lambda (xts, (e, t)) ->
        let xts, (e, t) = shift_abstraction shift_ty shift_term_ty k lvl xts (e,t) in
        {term = Lambda (xts, (e, t)); loc}

    | Spine (e, (xts, u), es) ->
        let e = shift k lvl e
        and xts, u = shift_abstraction shift_ty shift_ty k lvl xts u
        and es = List.map (shift k lvl) es in
        {term = Spine (e, (xts, u), es); loc}

    | Prod (xts, u) ->
        let xts, u = shift_abstraction shift_ty shift_ty k lvl xts u in
        {term = Prod (xts, u); loc}

    | Eq (t, e1, e2) ->
        let t = shift_ty k lvl t
        and e1 = shift k lvl e1
        and e2 = shift k lvl e2 in
        {term = Eq (t, e1, e2); loc}

    | Refl (t, e) ->
      let t = shift_ty k lvl t
      and e = shift k lvl e in
      {term = Refl (t, e); loc}

    | Inhab t ->
       let t = shift_ty k lvl t in
       {term = Inhab t; loc}

    | Bracket t ->
      let t = shift_ty k lvl t in
      {term = Bracket t; loc}

    | Signature xts ->
      let rec fold lvl res = function
        | [] -> List.rev res
        | (x,y,t)::rem ->
          let t = shift_ty k lvl t in
          fold (lvl+1) ((x,y,t)::res) rem
        in
      let xts = fold lvl [] xts in
      {term = Signature xts; loc}

    | Structure xts ->
      let rec fold lvl res = function
        | [] -> List.rev res
        | (x,y,t,te)::rem ->
          let t = shift_ty k lvl t in
          let te = shift k lvl te in
          fold (lvl+1) ((x,y,t,te)::res) rem
        in
      let xts = fold lvl [] xts in
      {term = Structure xts; loc}

    | Projection (te,xts,p) ->
      let te = shift k lvl te in
      let rec fold lvl res = function
        | [] -> List.rev res
        | (x,y,t)::rem ->
          let t = shift_ty k lvl t in
          fold (lvl+1) ((x,y,t)::res) rem
        in
      let xts = fold lvl [] xts in
      {term = Projection (te,xts,p); loc}

and shift_ty k lvl (Ty t) =
  let t = shift k lvl t in
    Ty t

and shift_term_ty k lvl (e, t) =
  let e = shift k lvl e
  and t = shift_ty k lvl t in
    (e, t)

(* We shadow [shift] and [shift_ty] to prevent evil uses. It is slightly
   evil to shadow values like this. A more honorable man would call the
   original [shift] something like [shift']. *)

let shift k lvl e =
  if k >= 0
  then shift k lvl e
  else
    (* NB: with reflection rule strengthening is not valid. Therefore we cannot
       shift by a negative amount. Never ever, even if it looks harmless to you. *)
    Error.impossible "shifting by a negative amount is not allowed, ever!"

let shift_ty k lvl t =
  if k >= 0
  then shift_ty k lvl t
  else
    (* NB: with reflection rule strengthening is not valid. Therefore we cannot
       shift by a negative amount. Never ever, even if it looks harmless to you. *)
    Error.impossible "shifting by a negative amount is not allowed, ever!"


let occurs_abstraction occurs_u occurs_v k (xus, v) =
  let rec fold k = function
    | [] -> occurs_v k v
    | (_,u) :: xus -> occurs_u k u + fold (k+1) xus
  in
    fold k xus

(* How many times does bound variable [k] occur in an expression? *)
let rec occurs k {term=e'} =
  match e' with
  | Type -> 0
  | Atom _ -> 0
  | Bound m -> if k = m then 1 else 0
  | Constant (x, es) -> List.fold_left (fun i e -> i + occurs k e) 0 es
  | Lambda a -> occurs_abstraction occurs_ty occurs_term_ty k a
  | Spine (e, xtst, es) ->
    occurs k e +
    occurs_abstraction occurs_ty occurs_ty k xtst +
    List.fold_left (fun i e -> i + occurs k e) 0 es
  | Prod a ->
    occurs_abstraction occurs_ty occurs_ty k a
  | Eq (t, e1, e2) ->
    occurs_ty k t + occurs k e1 + occurs k e2
  | Refl (t, e) ->
    occurs_ty k t + occurs k e
  | Inhab t -> occurs_ty k t
  | Bracket t ->
    occurs_ty k t
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
let alpha_equal_abstraction alpha_equal_u alpha_equal_v (xus, v) (xus', v') =
  let rec eq xus xus' =
    match xus, xus' with
    | [], [] -> true
    | (_, u) :: xus, (_, u') :: xus' ->
        alpha_equal_u u u' &&
        eq xus xus'
    | [], _::_ | _::_, [] -> false
  in
  eq xus xus' &&
  alpha_equal_v v v'

let rec alpha_equal_list equal_e es es' =
  match es, es' with
  | [], [] -> true
  | e :: es, e' :: es' ->
    equal_e e e' && alpha_equal_list equal_e es es'
  | ([],_::_) | ((_::_),[]) -> false

let rec alpha_equal {term=e1} {term=e2} =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | Atom x, Atom y -> Name.eq_atom x y

    | Bound i, Bound j -> i = j

    | Constant (x, es), Constant (x', es') ->
      Name.eq_ident x x' &&
      alpha_equal_list alpha_equal es es'

    | Lambda abs, Lambda abs' ->
      alpha_equal_abstraction alpha_equal_ty alpha_equal_term_ty abs abs'

    | Spine (e, xts, es), Spine (e', xts', es') ->
      alpha_equal e e' &&
      alpha_equal_abstraction alpha_equal_ty alpha_equal_ty xts xts' &&
      alpha_equal_list alpha_equal es es'

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

    | Bracket t1, Bracket t2 ->
      alpha_equal_ty t1 t2

    | Inhab t1, Inhab t2 ->
       alpha_equal_ty t1 t2

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

    | (Atom _ | Bound _ | Constant _ | Lambda _ | Spine _ |
        Type | Prod _ | Eq _ | Refl _ | Bracket _ | Inhab _ |
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
  Level 1: spine (0,0), refl (0)
  Level 2: eq (1,1)
  Level 3: lambda, prod, arrow

  let, ascribe

*)

let rec print_term ?max_level xs {term=e} ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
    match e with
      | Type ->
        print ~at_level:0 "Type"

      | Atom x ->
        print ~at_level:0 "%t" (Name.print_atom x)

      | Constant (x, []) ->
        print ~at_level:0 "%t" (Name.print_ident x)

      | Constant (x, ((_::_) as es)) ->
        print ~at_level:1 "%t %t" (Name.print_ident x) (Print.sequence (print_term ~max_level:0 xs) "" es)

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

      | Spine (e, xtst, es) -> print ~at_level:1 "%t" (print_spine xs e xtst es)

      | Prod (ts, t) -> print ~at_level:3 "%t" (print_prod xs ts t)

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

      | Inhab t -> print ~at_level:0 "[]%t"
                         (print_annot (print_ty xs t))

      | Bracket t ->
        print ~at_level:0 "[[%t]]"
          (print_ty xs t)

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
and print_prod xs yus v ppf =
  let rec split_binders = function
    | [] -> [], []
    | (y,u) :: yus ->
      if occurs_ty_abstraction occurs_ty 0 (yus, v) > 0 then
        let xus, yus = split_binders yus in
            (y,u) :: xus, yus
      else
        [], (y,u) :: yus
  in
  match split_binders yus with
  | [], [] -> Print.print ppf "%t" (print_ty xs v)
  | [], (y,u) :: yus ->
      Print.print ppf "@[<hov 2>%t@ %s@ %t@]"
          (print_ty ~max_level:2 xs u)
          (Print.char_arrow ())
          (print_prod (Name.anonymous::xs) yus v)
  | (_::_ as xus), yus ->
    Print.print ppf "@[<hov 2>%s %t@]"
      (Print.char_prod ())
      (Name.print_binders
        (Name.print_binder1 print_ty)
        (fun xs ppf -> Print.print ppf "@ %t" (print_prod xs yus v))
        xs xus)

and print_spine xs e (yts, u) es ppf =
  let spine_noannot ppf =
    Print.print ppf "@[<hov 2>%t@ %t@]"
      (print_term ~max_level:0 xs e)
      (Print.sequence (print_term ~max_level:0 xs) "" es)
  in
  if !Config.annotate
  then
    Print.print ppf "(%t)%t"
      spine_noannot
      (print_annot (Name.print_binders (Name.print_binder1 print_ty) (fun xs -> print_ty xs u) xs yts))
  else
    spine_noannot ppf

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

and print_binder xs (x, t) ppf =
  Print.print ppf "(%t :@ %t)"
        (Name.print_ident x)
        (print_ty xs t)

let print_constsig ?max_level xs (rxus, t) ppf =
  let print_xs =
    (fun xs x (red, u) ppf ->
       Print.print ppf "(@[<hv>%s%t :@ %t@])"
         (if red then "reduce " else "")
         (Name.print_ident x)
         (print_ty ~max_level:0 xs u)) in
  let print_u =
    (fun sp xs ppf ->
       Print.print ppf "%s:@;<1 -2>%t"
         sp (print_ty ?max_level xs t)) in
  match rxus with
  | [] -> print_u "" xs ppf
  | _::_ -> Name.print_binders print_xs (print_u " ") xs rxus ppf


(****** Structure stuff ********)

let field_value ~loc xtes p =
  let rec fold vs = function
    | [] -> Error.runtime "Tt.field_value: field %t not found" (Name.print_ident p)
    | (l,x,t,te)::rem ->
      let te = instantiate vs te in
      if Name.eq_ident p l
      then te
      else fold (te::vs) rem
    in
  fold [] xtes

let field_type ~loc xts e p =
  let rec fold vs = function
    | [] -> Error.typing "%t has no field %t" (print_term [] e) (Name.print_ident p)
    | (l,x,t)::rem ->
      if Name.eq_ident p l
      then instantiate_ty vs t
      else
        let el = mk_projection ~loc e xts l in
        fold (el::vs) rem
    in
  fold [] xts

