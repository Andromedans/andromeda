(** The abstract syntax of Andromedan type theory (TT). *)

type term = term' * Location.t
and term' =
(** The type of TT terms.
    (For details on the mutual definition with [term'], see module Location.)

    We use locally nameless syntax: names for free variables and deBruijn
    indices for bound variables. In terms of type [term], bound variables are
    not allowed to appear "bare", i.e., without an associated binder.

    Instead of nesting binary applications [((e1 e2) ... en)], we use
    spines [e1 [e2; ...; en]]. The reason for this is one of efficiency:
    because we need to tag every application with the argument and result type,
    nested applications use quadratic space (in the number of the applications)
    whereas spines use linear space. Consequently, lambda abstractions and
    products also accept lists of arguments.

    To represent nested bindings, we use an auxiliary type
    [(A, B) abstraction], which consists of a list [(x1 : a1), ..., (xn : an)],
    where each [ak] has type [A] and can depend on variables [x1, ..., x{k-1}],
    and of a single [b] of type [B] that can depend on all [x1, ..., xn]. *)

  | Type
  (** term denoting the type of types *)
  | Name of Name.t
  (** a free variable *)
  | Bound of Syntax.bound
  (** a bound variable *)
  | Lambda of (ty, term * ty) abstraction
  (** a lambda abstraction [fun (x1 : t1) ... (xn : tn) -> e : t] where
      [tk] depends on [x1, ..., x{k-1}], while [e] and [t] depend on
      [x1, ..., xn] *)
  | Spine of term * (term * ty, ty) abstraction
  (** a spine [e [(x1 : (e1, t1)); ..., (xn : (en, tn))] : t] means that
      [e] is applied to [e1, ..., en], and that the type of [e] is
      [forall (x1 : t1) ... (xn : tn), t]. Here [tk] depends on
      [x1, ..., x{k-1}] and [t] depends on [x1, ..., xn]. *)
  | Prod of (ty, ty) abstraction
  (** a dependent product [forall (x1 : t1) ... (xn : tn), t], where [tk]
      depends on [x1, ..., x{k-1}] and [t] depends on [x1, ..., xn]. *)
  | Eq of ty * term * term
  (** strict equality type [e1 == e2] where [e1] and [e2] have type [t]. *)
  | Refl of ty * term
  (** reflexivity [refl e] where [e] has type [t]. *)

and ty = Ty of term
(** The type of TT types.
    Since we have [Type : Type] we do not distinguish terms from types,
    so the type [ty] of types is just a synonym for the type [term] of terms. 
    However, we tag types with the [Ty] constructor to avoid nasty bugs. *)

and ('a, 'b) abstraction = (Name.t * 'a) list * 'b
(** The auxiliary type of abstractions discussed above. *)

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)
let mk_name ~loc x = Name x, loc
let mk_bound ~loc k = Bound k, loc

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

let mk_spine ~loc e xets t = Spine (e, (xets, t)), loc
let mk_type ~loc = Type, loc
let mk_eq ~loc t e1 e2 = Eq (t, e1, e2), loc
let mk_refl ~loc t e = Refl (t, e), loc

(** Convert a term to a type. *)
let ty e = Ty e

let mk_eq_ty ~loc t e1 e2 = ty (mk_eq ~loc t e1 e2)
let mk_prod_ty ~loc xts t = ty (mk_prod ~loc xts t)
let mk_type_ty ~loc = ty (mk_type ~loc)

(** The [Type] constant, without a location. *)
let typ = Ty (mk_type ~loc:Location.nowhere)


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
  let n = List.length es in
    match e' with

    | Type -> e

    | Name _ -> e

    | Bound k ->
       if k < depth
       then e
        (* this is a variable bound in an abstraction inside the
           instantiated term, so we leave it as it is *)
       else 
         if k < depth + n
         then List.nth es (k - depth)
          (* this is a variable that corresponds to a substituted term,
             so we replace it *)
         else Bound (k - n), loc
          (* this is a variable bound in an abstraction outside the
             instantiated term, so it remains bound, but its index decreases
             by the number of bound variables replaced by terms *)

    | Lambda a ->
       let a = instantiate_abstraction instantiate_ty instantiate_term_ty es depth a
       in Lambda a, loc

    | Spine (e, a) ->
       let e = instantiate es depth e
       and a = instantiate_abstraction instantiate_term_ty instantiate_ty es depth a
       in Spine (e, a), loc

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

and instantiate_ty es depth (Ty t) = 
  let t = instantiate es depth t
  in Ty t

and instantiate_term_ty es depth (e, t) =
  let e = instantiate es depth e
  and t = instantiate_ty es depth t
  in (e, t)

let unabstract xs depth e =
  let es = List.map (mk_name ~loc:Location.nowhere) xs
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
  | Bound k -> assert (k < depth) ; e
  | Name x ->
    begin
      match Name.index_of x xs with
      | None -> e
      | Some k -> Bound (depth + k), loc
    end
  | Lambda a ->
    let a = abstract_abstraction
              abstract_ty abstract_term_ty
              xs depth a
    in Lambda a, loc
  | Spine (e, a) ->
    let e = abstract xs depth e
    and a = abstract_abstraction
              abstract_term_ty abstract_ty
              xs depth a
    in Spine (e, a), loc
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

and abstract_ty xs depth (Ty t) =
  let t = abstract xs depth t
  in Ty t

and abstract_term_ty xs depth (e, t) =
  let e = abstract xs depth e
  and t = abstract_ty xs depth t
  in (e, t)

let occurs_abstraction occurs_u occurs_v k (xus, v) =
  let rec fold k = function
    | [] -> occurs_v k v
    | (_,u) :: xus -> occurs_u k u || fold (k+1) xus
  in
    fold k xus

(* Does bound variable [k] occur in an expression? *)
let rec occurs k (e',_) =
  match e' with
  | Type -> false
  | Name _ -> false
  | Bound m -> (k = m)
  | Lambda a -> occurs_abstraction occurs_ty occurs_term_ty k a
  | Spine (e, a) ->
    occurs k e ||
    occurs_abstraction occurs_term_ty occurs_ty k a
  | Prod a ->
    occurs_abstraction occurs_ty occurs_ty k a
  | Eq (t, e1, e2) ->
    occurs_ty k t || occurs k e1 || occurs k e2
  | Refl (t, e) ->
    occurs_ty k t || occurs k e

and occurs_ty k (Ty t) = occurs k t

and occurs_term_ty k (e, t) =
  occurs k e || occurs_ty k t

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

let rec print_binders print_u print_v xs xus ppf =
match xus with
  | [] -> Print.print ppf "%t" (print_v xs)
  | [(x,u)] ->
    let x = Name.refresh xs x in
    Print.print ppf "(@[<hv>%t :@ %t@])%t"
      (Name.print x)
      (print_u xs u)
      (print_v (x::xs))  
  | (x,u) :: xus ->
    let x = Name.refresh xs x in
    Print.print ppf "(@[<hv>%t :@ %t@])@ %t"
      (Name.print x)
      (print_u xs u)
      (print_binders print_u print_v (x::xs) xus)


let rec print_term ?max_level xs (e,_) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
    match e with
      | Type ->
        print ~at_level:0 "Type"

      | Name x ->
        print ~at_level:0 "%t" (Name.print x)

      | Bound k ->
        begin
          try
            print ~at_level:0 "%t" (Name.print (List.nth xs k))
          with
          | Not_found -> 
              (** XXX this should never get printed *)
              print ~at_level:0 "DEBRUIJN[%d]" k
        end

      | Lambda a -> print ~at_level:3 "%t" (print_lambda xs a)

      | Spine (e, a) -> print ~at_level:1 "%t" (print_spine xs e a)

      | Prod (ts, t) -> print ~at_level:3 "%t" (print_prod xs ts t)

      | Eq (t, e1, e2) ->
        print ~at_level:2 "@[<hv 2>%t@ ==%t %t@]"
          (print_term ~max_level:1 xs e1)
          (print_annot (print_ty xs t))
          (print_term ~max_level:1 xs e2)

      | Refl (t, e) ->
        print ~at_level:1 "refl%t %t"
          (print_annot (print_ty xs t))
          (print_term ~max_level:0 xs e)

and print_ty ?max_level xs (Ty t) ppf = print_term ?max_level xs t ppf

(** [print_lambda a e t ppf] prints a lambda abstraction using formatter [ppf]. *)
and print_lambda xs (yus, (e, t)) ppf =
  Print.print ppf "@[<hov 2>fun %t@]"
    (print_binders
      print_ty
      (fun xs ppf -> Print.print ppf " %t=>@ %t"
        (print_annot (print_ty xs t))
        (print_term xs e))
      xs
      yus)

(** [print_prod xs ts t ppf] prints a dependent product using formatter [ppf]. *)
and print_prod xs yus v ppf =
  let rec split_binders = function
    | [] -> [], []
    | (y,u) :: yus ->
      if occurs_abstraction occurs_ty occurs_ty 0 (yus, v) then
        let xus, yus = split_binders yus in
            (y,u) :: xus, yus
      else
        [], (y,u) :: yus
  in
  match split_binders yus with
  | [], [] -> Print.print ppf "%t" (print_ty xs v)
  | [], (y,u) :: yus ->
      Print.print ppf "@[<hov 2>%t ->@ %t@]"
          (print_ty ~max_level:2 xs u)
          (print_prod (Name.anonymous::xs) yus v)
  | (_::_ as xus), yus ->
    Print.print ppf "@[<hov 2>forall %t@]"
      (print_binders
        print_ty
        (fun xs ppf -> Print.print ppf ",@ %t" (print_prod xs yus v))
        xs xus)

and print_spine xs e (yets, u) ppf =
  Print.print ppf "@[<hov 2>%t@ %t@]"
    (print_term ~max_level:0 xs e)
    (print_binders
      (fun xs (e, t) ppf -> Print.print ppf "%t%t" (print_term xs e) (print_annot (print_ty xs t)))
      (fun xs -> print_annot (print_ty xs u))
      xs
      yets)

and print_binder xs (x, t) ppf =
  Print.print ppf "(%t : %t)"
        (Name.print x)
        (print_ty xs t)
