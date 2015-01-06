(** The abstract syntax of Andromedan type theory (TT). *)

type term = term' * Position.t
and term' =
(** The type of TT terms.
    (For details on the mutual definition with term', see module Position.)

    We use locally nameless syntax: names for free variables and deBruijn
    indices for bound variables. In terms of type [term], bound variables are
    not allowed to appear "bare", i.e., without an associated binder.

    Instead of nesting binary applications [((e1 e2) ... en)], we use
    spines [e1 [e2; ...; en]]. The reason for this is one of efficiency:
    because we need to tag every application with the argument and result type,
    nested applications use quadratic space (in the number of the applications)
    whereas spines use linear space. Consequently, lambda abstractions and
    products also have more than a single argument.

    To represent nested bindings, we use an auxiliary type
    [(A, B) abstraction], which consists of a list [(x1 : a1), ..., (xn : an)],
    where each [ak] has type [A] and can depend on variables [x1, ..., x{k-1}],
    and of a single [b] of type [B] that can depend on all [x1, ..., xn]. *)

  | Type
  (** term denoting the type of types *)
  | Name of Common.name
  (** a free variable *)
  | Bound of Common.bound
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

and ('a, 'b) abstraction = (Common.name * 'a) list * 'b
(** The auxiliary type of abstractions discussed above. *)

type value =
(** A value is obtained by successfully evaluating a computation. *)
  term * ty
  (** A judgement [e : t] where [e] is guaranteed to have the type [t]. *)

type result =
(** Possible results of evaluating a computation. *)
  | Return of value

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)
let mk_name ~loc x = Name x, loc
let mk_bound ~loc k = Bound k, loc
let mk_lambda ~loc xts e t = Lambda (xts, (e, t)), loc
let mk_prod ~loc xts t = Prod (xts, t), loc
let mk_spine ~loc e xets t = Spine (e, (xets, t)), loc
let mk_type ~loc = Type, loc
let mk_eq ~loc t e1 e2 = Eq (t, e1, e2), loc
let mk_refl ~loc t e = Refl (t, e), loc

(** Convert a term to a type. *)
let ty e = Ty e

let mk_eq_ty ~loc t e1 e2 = ty (mk_eq ~loc t e1 e2)
let mk_prod_ty ~loc xts t = ty (mk_prod ~loc xts t)


(** The [Type] constant, without a location. *)
let typ = Ty (mk_type ~loc:Position.nowhere)

(** Alpha equality *)
(* Currently, the only difference between alpha and structural equality is that
   the names of variables in abstractions are ignored. *)

let equal_abstraction equal_u equal_v (xus, v) (xus', v') =
  let rec eq xus xus' =
    match xus, xus' with
    | [], [] -> true
    | (_, u) :: xus, (_, u') :: xus' ->
        equal_u u u' &&
        eq xus xus'
    | [], _::_ | _::_, [] -> false
  in
  eq xus xus' &&
  equal_v v v'

let rec equal (e1,_) (e2,_) =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | Name x, Name y -> Common.eqname x y

    | Bound i, Bound j -> i = j

    | Lambda abs, Lambda abs' ->
      equal_abstraction equal_ty equal_term_ty abs abs'

    | Spine (e, abs), Spine (e', abs') ->
      equal e e' &&
      equal_abstraction equal_term_ty equal_ty abs abs'

    | Type, Type -> true

    | Prod abs, Prod abs' ->
      equal_abstraction equal_ty equal_ty abs abs'

    | Eq (t, e1, e2), Eq (t', e1', e2') ->
      equal_ty t t' && 
      equal e1 e1' &&
      equal e2 e2'

    | Refl (t, e), Refl (t', e') ->
      equal_ty t t' && 
      equal e e'

    | (Name _ | Bound _ | Lambda _ | Spine _ |
        Type | Prod _ | Eq _ | Refl _), _ ->
      false
  end

and equal_ty (Ty t1) (Ty t2) = equal t1 t2

and equal_term_ty (e, t) (e', t') = equal e e' && equal_ty t t'

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
  let es = List.map (mk_name ~loc:Position.nowhere) xs
  in instantiate es depth e  

let unabstract_ty xs depth (Ty t) =
  let t = unabstract xs depth t
  in Ty t 

let occurs _ = true

let occurs_ty _ = true
