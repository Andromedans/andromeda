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
let mk_lambda ~loc x t1 t2 e = Lambda ([x, t1], (t2, e)), loc
let mk_prod ~loc x t1 t2 = Prod ([x, t1], t2), loc
let mk_spine ~loc e exts t = Spine (e, (exts, t)), loc
let mk_app ~loc x t1 t2 e1 e2 = mk_spine ~loc e1 [(x, (e2, t1))] t2
let mk_type ~loc = Type, loc
let mk_eq ~loc t e1 e2 = Eq (t, e1, e2), loc
let mk_refl ~loc t e = Refl (t, e), loc

(** Convert a term to a type. *)
let ty e = Ty e

let mk_eq_ty ~loc t e1 e2 = Ty (Eq (t, e1, e2), loc)


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

let instantiate_abs instantiate_u instantiate_v shift es (xus, v) =
  let rec instantiate shift = function
    | [] -> shift, []
    | (x, u) :: xus ->
        let u = instantiate_u shift es u in
        let shift, xus = instantiate (shift + 1) xus in
        shift, (x, u) :: xus
  in
  let shift, xus = instantiate shift xus in
  let v = instantiate_v shift es v in
  (xus, v)

let instantiate ets (xts, et) =
  let num_terms = List.length ets
  and num_args = List.length xts in

  let rec instantiate shift ets ((e', loc) as e) =
    begin match e' with

      | Name _ -> e

      | Bound index ->
          if index < shift then
            (* this is a variable bound in an abstraction inside the
               instantiated term, so we leave it as it is *)
            e
          else if shift <= index && index < shift + num_terms then
            (* this is a variable that corresponds to a substituted term,
               so we replace it *)
            List.nth ets (index - shift)
          else (* if shift + num_terms <= index *)
            (* this is a variable bound in an abstraction outside the
               instantiated term, so it remains bound, but its index decreases
               by the number of bound variables replaced by terms *)
            Bound (index - num_terms), loc

      | Lambda abs' ->
        let abs' = instantiate_abs instantiate_ty instantiate_term_ty shift ets abs'
        in Lambda abs', loc

      | Spine (e, abs') ->
        let e = instantiate shift ets e
        and abs' = instantiate_abs instantiate_term_ty instantiate_ty shift ets abs'
        in Spine (e, abs'), loc

      | Type -> e

      | Prod abs' ->
        let abs' = instantiate_abs instantiate_ty instantiate_ty shift ets abs'
        in Prod abs', loc

      | Eq (t, e1, e2) ->
        let t = instantiate_ty shift ets t
        and e1 = instantiate shift ets e1
        and e2 = instantiate shift ets e2
        in Eq (t, e1, e2), loc

      | Refl (t, e) ->
        let t = instantiate_ty shift ets t
        and e = instantiate shift ets e
        in Refl (t, e), loc
    end

  and instantiate_ty shift ets (Ty t) = Ty (instantiate shift ets t)

  and instantiate_term_ty shift ets (e, t) =
    let e = instantiate shift ets e
    and t = instantiate_ty shift ets t
    in (e, t)
  in

  if num_terms <= num_args then
    let rec drop k = function
    | xs when k = 0 -> xs
    | x :: xs -> drop (k - 1) xs
    | [] -> assert false (* why doesn't OCaml accept "assert (num_terms <= num_args)" *)
    in
    let remaining_xts = drop num_terms xts in
    let abs = instantiate_abs instantiate_ty instantiate_term_ty 0 ets (remaining_xts, et)
    in abs, []

  else (* if num_terms > num_args *)
    let rec split ets1 k = function
    | ets2 when k = 0 -> (List.rev ets1, ets2)
    | et :: ets -> split (et :: ets1) (k - 1) ets
    | [] -> assert false (* why doesn't OCaml accept "assert (num_terms >= num_args)" *)
    in
    let (ets1, ets2) = split [] num_args ets in
    let e, t = instantiate_term_ty 0 ets1 et in
    ([], (e, t)), ets2


let occurs _ = true

let occurs_ty _ = true
