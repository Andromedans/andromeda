(** The abstract syntax of Andromedan type theory. *)

(** The type of terms. We use locally nameless syntax: names for free variables and de
    Bruijn indices for bound variables. The type [term] is for terms in which a bound
    variable is not allowed to appear "bare", i.e., without an associated binder.

    We use spines everywhere. Thus instead of a nested application [e1 (e2 (... en))] we
    have a spine [e1 [e2; ...; en]], and similarly for lambda abstractions and product
    types. The reason for this is one of efficiency: because we need to tag every
    application with a type, nested applications use quadratic space (in the number of the
    application) whereas spines use linear space.
*)
type term = term' * Position.t
and term' =
  | Type
  | Name of Common.name (** a free variable *)
  | Bound of Common.bound (** a bound variable *)
  | Lambda of (ty, term * ty) abstraction
    (** a lambda abstraction [fun (x1:A1) ... (xn:An) -> e : A] where
        [Ak] depends on [x1, ..., x{k-1}], while [e] and [A] depends on
        [x1, ..., xn] *)
  | Spine of term * (term * ty, ty) abstraction
    (** a spine [e [(x1,(e1,A1)); ..., (xn,(en,An))] : A] means that
        [e] is applied to [e1, ..., en], and that the type of [e] has type
        [forall (x1:A1) ... (xn:An), A]. Here again [Ak] depends on
        [x1, ..., x{k-1}] and [A] depends on [x1, ..., xn]. *)
  | Prod of (ty, ty) abstraction
    (** dependent product [forall (x1:A1) ... (xn:An), A], where [Ak] depends on
        [x1, ..., x{k-1}] and [A] depends on [x1, ..., xn]. *)
  | Eq of ty * term * term
    (** strict equality type [e1 == e2] where [e1] and [e2] have type [A]. *)
  | Refl of ty * term (** reflexivity [refl e] where [e] has type [A]. *)

(** Since we have [Type : Type] we do not distinguish terms from types,
    so the type of type [ty] is just a synonym for the type of terms. 
    However, we tag types with the [Ty] constructor to avoid nasty bugs. *)
and ty = Ty of term

(** An [(A,B) abstraction] is a [B] bound by [x1:a1, ..., xn:an] where
    the [a1, ..., an] have type [A]. *)
and ('a, 'b) abstraction = (Common.name * 'a) list * 'b

(** A value is the result of a computation. *)
type value = term * ty

type result =
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
       else 
         if k < depth + n
         then List.nth es (k - depth)
         else Bound (k - n), loc

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
