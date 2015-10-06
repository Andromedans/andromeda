(** The abstract syntax of Andromedan type theory (TT). *)

type term = term' * Location.t
and term' =

  (** term denoting the type of types *)
  | Type

  (** a free variable *)
  | Atom of Name.atom

  (** a bound variable *)
  | Bound of Syntax.bound

  (** constant *)
  | Constant of Name.ident * term list

  (** a lambda abstraction [fun (x1 : t1) ... (xn : tn) -> e : t] where
      [tk] depends on [x1, ..., x{k-1}], while [e] and [t] depend on
      [x1, ..., xn] *)
  | Lambda of (ty, term * ty) abstraction

  (** a spine [e ((x1 : t1) ..., (xn : tn) : t) e1 ... en] means that
      [e] is applied to [e1, ..., en], and that the type of [e] is
      [forall (x1 : t1) ... (xn : tn), t]. Here [tk] depends on
      [x1, ..., x{k-1}] and [t] depends on [x1, ..., xn]. *)
  | Spine of term * (ty, ty) abstraction * term list

  (** a dependent product [forall (x1 : t1) ... (xn : tn), t], where [tk]
      depends on [x1, ..., x{k-1}] and [t] depends on [x1, ..., xn]. *)
  | Prod of (ty, ty) abstraction

  (** strict equality type [e1 == e2] where [e1] and [e2] have type [t]. *)
  | Eq of ty * term * term

  (** reflexivity [refl e] where [e] has type [t]. *)
  | Refl of ty * term

  (** the inhabitant of a bracket type *)
  | Inhab

  (** bracket type *)
  | Bracket of ty

(** The type of TT types.
    Since we have [Type : Type] we do not distinguish terms from types,
    so the type [ty] of types is just a synonym for the type [term] of terms.
    However, we tag types with the [Ty] constructor to avoid nasty bugs. *)
and ty = Ty of term

and 'a abstraction = (Name.ident * ty) list * 'a

type constsig = bool list * ty abstraction

(** Unicode and ascii version of symbols *)

let char_lambda () = if !Config.ascii then "fun" else "λ"
let char_arrow ()  = if !Config.ascii then "->" else "→"
let char_darrow () = if !Config.ascii then "=>" else "⇒"
let char_prod ()   = if !Config.ascii then "forall" else "Π"
let char_equal ()  = if !Config.ascii then "==" else "≡"

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)
let mk_atom ~loc x = Atom x, loc
let mk_bound ~loc k = Bound k, loc

let mk_constant ~loc x es = Constant (x, es), loc

let mk_lambda ~loc xts e t =
  match xts with
  | [] -> e
  | _ :: _ -> Lambda (xts, (e, t)), loc

let mk_prod ~loc xts ((Ty e) as t) =
  match xts with
  | [] -> e
  | _ :: _ ->
    begin match t with
    (* XXX join locations loc and loc' *)
    | Ty (Prod (yts, t), loc') -> Prod (xts @ yts, t), loc
    | t -> Prod (xts, t), loc
    end

let mk_spine ~loc e xts t es =
  match xts with
    | [] -> fst e, loc
    | _::_ -> Spine (e, (xts, t), es), loc

let mk_type ~loc = Type, loc
let mk_eq ~loc t e1 e2 = Eq (t, e1, e2), loc
let mk_refl ~loc t e = Refl (t, e), loc

let mk_inhab ~loc = Inhab, loc
let mk_bracket ~loc t = Bracket t, loc

(** Convert a term to a type. *)
let ty e = Ty e

let mk_eq_ty ~loc t e1 e2 = ty (mk_eq ~loc t e1 e2)
let mk_prod_ty ~loc xts t = ty (mk_prod ~loc xts t)
let mk_type_ty ~loc = ty (mk_type ~loc)
let mk_bracket_ty ~loc t = ty (mk_bracket ~loc t)

(** The [Type] constant, without a location. *)
let typ = Ty (mk_type ~loc:Location.unknown)


(** Manipulation of variables *)

let instantiate_abstraction instantiate_u instantiate_v es depth (xus, v) =
  let rec inst acc depth = function
    | [] ->
       let v = instantiate_v es depth v
       in List.rev acc, v
    | (x,u) :: xus ->
       let u = instantiate_u es depth u in
       inst ((x,u) :: acc) (depth+1) xus
  in
    inst [] depth xus


let rec instantiate es depth ((e',loc) as e) =
  (* XXX possible optimization: check whether [es] is empty *)
  if es = [] then e else
    match e' with

    | Type -> e

    | Atom _ -> e

    | Bound k ->
       if k < depth
       then e
        (* this is a variable bound in an abstraction inside the
           instantiated term, so we leave it as it is *)
       else
         let n = List.length es in
         if k < depth + n
         then List.nth es (k - depth) (* variable corresponds to a substituted term, replace it *)
         else Bound (k - n), loc
          (* this is a variable bound in an abstraction outside the
             instantiated term, so it remains bound, but its index decreases
             by the number of bound variables replaced by terms *)

    | Constant (x, ds) ->
      let ds = List.map (instantiate es depth) ds in
      Constant (x, ds), loc

    | Lambda a ->
       let a = instantiate_abstraction instantiate_ty instantiate_term_ty es depth a
       in Lambda a, loc

    | Spine (e, xtst, ds) ->
       let e = instantiate es depth e
       and xtst = instantiate_abstraction instantiate_ty instantiate_ty es depth xtst
       and ds = List.map (instantiate es depth) ds
       in Spine (e, xtst, ds), loc

    | Prod a ->
       let a = instantiate_abstraction instantiate_ty instantiate_ty es depth a
       in Prod a, loc

    | Eq (t, e1, e2) ->
       let t = instantiate_ty es depth t
       and e1 = instantiate es depth e1
       and e2 = instantiate es depth e2
       in Eq (t, e1, e2), loc

    | Refl (t, e) ->
       let t = instantiate_ty es depth t
       and e = instantiate es depth e
       in Refl (t, e), loc

    | Inhab -> Inhab, loc

    | Bracket t ->
      let t = instantiate_ty es depth t in
      Bracket t, loc

and instantiate_ty es depth (Ty t) =
  let t = instantiate es depth t
  in Ty t

and instantiate_term_ty es depth (e, t) =
  let e = instantiate es depth e
  and t = instantiate_ty es depth t
  in (e, t)

let unabstract xs depth e =
  let es = List.map (mk_atom ~loc:Location.unknown) xs
  in instantiate es depth e

let unabstract_ty xs depth (Ty t) =
  let t = unabstract xs depth t
  in Ty t


and abstract_abstraction abst_u abst_v ys depth (xus,v) =
  let rec abst acc depth = function
    | [] ->
       let v = abst_v ys depth v
       in List.rev acc, v
    | (x,u) :: xus ->
       let u = abst_u ys depth u in
       abst ((x,u) :: acc) (depth+1) xus
  in
    abst [] depth xus

let rec abstract xs depth ((e',loc) as e) =
  match e' with

  | Type -> e

  | Bound k -> e

  | Constant (y, es) ->
     let es = List.map (abstract xs depth) es in
      Constant (y, es), loc

  | Atom x ->
    begin
      match Name.index_of_atom x xs with
      | None -> e
      | Some k -> Bound (depth + k), loc
    end

  | Lambda a ->
    let a = abstract_abstraction
              abstract_ty abstract_term_ty
              xs depth a
    in Lambda a, loc

  | Spine (e, xtst, es) ->
    let e = abstract xs depth e
    and xtst = abstract_abstraction
                 abstract_ty abstract_ty
                 xs depth xtst
    and es = List.map (abstract xs depth) es
    in Spine (e, xtst, es), loc

  | Prod a ->
    let a = abstract_abstraction
              abstract_ty abstract_ty
              xs depth a
    in Prod a, loc

  | Eq (t, e1, e2) ->
    let t = abstract_ty xs depth t
    and e1 = abstract xs depth e1
    and e2 = abstract xs depth e2
    in Eq (t, e1, e2), loc

  | Refl (t, e) ->
    let t = abstract_ty xs depth t
    and e = abstract xs depth e
    in Refl (t, e), loc

  | Inhab -> Inhab, loc

  | Bracket t ->
    let t = abstract_ty xs depth t in
    Bracket t, loc


and abstract_ty xs depth (Ty t) =
  let t = abstract xs depth t
  in Ty t

and abstract_term_ty xs depth (e, t) =
  let e = abstract xs depth e
  and t = abstract_ty xs depth t
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

let rec shift k lvl ((e',loc) as e) =
  match e' with
    | (Type | Atom _) -> e

    | Bound j ->
      if lvl <= j
      then (Bound (j + k), loc)
      else e

    | Constant (x, es) ->
        let es = List.map (shift k lvl) es in
        Constant (x, es), loc

    | Lambda (xts, (e, t)) ->
        let xts, (e, t) = shift_abstraction shift_ty shift_term_ty k lvl xts (e,t) in
          Lambda (xts, (e, t)), loc

    | Spine (e, (xts, u), es) ->
        let e = shift k lvl e
        and xts, u = shift_abstraction shift_ty shift_ty k lvl xts u
        and es = List.map (shift k lvl) es in
          Spine (e, (xts, u), es), loc

    | Prod (xts, u) ->
        let xts, u = shift_abstraction shift_ty shift_ty k lvl xts u in
          Prod (xts, u), loc

    | Eq (t, e1, e2) ->
        let t = shift_ty k lvl t
        and e1 = shift k lvl e1
        and e2 = shift k lvl e2 in
           Eq (t, e1, e2), loc

    | Refl (t, e) ->
      let t = shift_ty k lvl t
      and e = shift k lvl e in
        Refl (t, e), loc

    | Inhab -> Inhab, loc

    | Bracket t ->
      let t = shift_ty k lvl t in
        Bracket t, loc

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
let rec occurs k (e',_) =
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
  | Inhab -> 0
  | Bracket t ->
    occurs_ty k t

and occurs_ty k (Ty t) = occurs k t

and occurs_term_ty k (e, t) =
  occurs k e + occurs_ty k t

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

let rec print_term ?max_level xs (e,_) ppf =
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
          (char_equal ())
          (print_annot (print_ty xs t))
          (print_term ~max_level:1 xs e2)

      | Refl (t, e) ->
        print ~at_level:1 "refl%t %t"
          (print_annot (print_ty xs t))
          (print_term ~max_level:0 xs e)

      | Inhab -> print ~at_level:0 "[]"

      | Bracket t ->
        print ~at_level:0 "[[%t]]"
          (print_ty xs t)

and print_ty ?max_level xs (Ty t) ppf = print_term ?max_level xs t ppf

(** [print_lambda a e t ppf] prints a lambda abstraction using formatter [ppf]. *)
and print_lambda xs (yus, (e, t)) ppf =
  Print.print ppf "@[<hov 2>%s %t@]"
    (char_lambda ())
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
      if occurs_abstraction occurs_ty occurs_ty 0 (yus, v) > 0 then
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
          (char_arrow ())
          (print_prod (Name.anonymous::xs) yus v)
  | (_::_ as xus), yus ->
    Print.print ppf "@[<hov 2>%s %t@]"
      (char_prod ())
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

and print_binder xs (x, t) ppf =
  Print.print ppf "(%t :@ %t)"
        (Name.print_ident x)
        (print_ty xs t)

let print_constsig ?max_level xs (x_red_u_s, t) ppf =
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
  match x_red_u_s with
  | [] -> print_u "" xs ppf
  | _::_ -> Name.print_binders print_xs (print_u " ") xs x_red_u_s ppf
