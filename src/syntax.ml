(** The abstract syntax of Andromedan type theory. *)

(** The type of terms. We use locally nameless syntax: names for
    free variables and de Bruijn indices for bound variables.
    The type [term] is for terms in which a bound variable is
    not allowed to appear "bare", i.e., without an associated
    binder. *)
type term = term' * Position.t
and term' =
  | Name of Common.name (* free variable *)
  | Bound of Common.bound (* bound variable *)
  (* fun (x_1 : A_1) (x_2 : A_2(x_1)) ... (x_n : A_n(x_1,...,x_n-1)) => e(x_1,...,x_n) : A(x_1,...,x_n) *)
  | Lambda of (ty, term * ty) abstraction
  (* e : (x_1 : A_1) (x_2 : A_2(x_1)) ... (x_n : A_n(x_1,...,x_n-1)), A(x_1,...,x_n)
     (e_1 : A_1) (e_2 : A_2(e_1)) ... (e_n : A_n(e_1,...,e_n-1))
     e [e_1, e_2, ..., e_n] : A(e_1,...,e_n) *)
  | Spine of term * (term * ty, ty) abstraction
  | Type
  (* forall (x_1 : A_1) (x_2 : A_2(x_1)) ... (x_n : A_n(x_1,...,x_n-1)), A(x_1,...,x_n) *)
  | Prod of (ty, ty) abstraction
  | Eq of ty * term * term
  | Refl of ty * term

(** Since we have [Type : Type] we do not distinguish terms from types,
    so the type of type [ty] is just a synonym for the type of terms. *)
and ty = Ty of term

and ('a, 'b) abstraction = Abs of (Common.name * 'a) list * 'b

(** We disallow direct creation of terms (using the [private] qualifier in the interface
    file), so we provide these constructors instead. *)
let mk_name ~loc x = Name x, loc
let mk_bound ~loc k = Bound k, loc
let mk_lambda ~loc x t1 t2 e = Lambda (Abs ([x, t1], (t2, e))), loc
let mk_prod ~loc x t1 t2 = Prod (Abs ([x, t1], t2)), loc
let mk_spine ~loc e exts t = Spine (e, Abs (exts, t)), loc
let mk_app ~loc x t1 t2 e1 e2 = mk_spine ~loc e1 [(x, (e2, t1))] t2

let mk_type ~loc = Type, loc
let mk_eq ~loc t e1 e2 = Eq (t, e1, e2), loc
let mk_refl ~loc t e = Refl (t, e), loc

let typ = mk_type ~loc:Position.nowhere

(** A value is the result of a computation. *)
type value =
  | IsTerm of term * ty
  | IsType of ty

(** Alpha equality *)

let equal_abstraction equal_u equal_v (Abs (xus, v)) (Abs (xus', v')) =
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

let abstract_abstraction abstract_u abstract_v shift (Abs (xus, v)) =
  let rec abs shift = function
    | [] -> shift, []
    | (x, u) :: xus ->
        let u = abstract_u shift u
        and shift, xus = abs (shift + 1) xus
        in shift, (x, u) :: xus
  in
  let shift, xus = abs shift xus
  and v = abstract_v shift v
  in Abs (xus, v)


let instantiate e0 (Bare e) =
  let rec instantiate k e0 ((e',loc) as e) =
    begin match e' with

      | Name _ -> e

      | Bound m -> if k = m then e0 else e

      | Ascribe (e, t) ->
        let e = instantiate k e0 e 
        and t = instantiate_ty k e0 t
        in Ascribe (e, t), loc

      | Lambda (y, t1, t2, e) ->
        let t1 = instantiate_ty k e0 t1
        and t2 = instantiate_bare_ty k e0 t2
        and e = instantiate_bare k e0 e
        in Lambda (y, t1, t2, e), loc

      | Spine (t, e, es) ->
        let t = instantiate_ty k e0 t
        and e = instantiate k e0 e
        and es = List.map (instantiate k e0) es
        in Spine (t, e, es), loc

      | Type -> e

      | Prod (y, t1, t2) ->
        let t1 = instantiate_ty k e0 t1
        and t2 = instantiate_bare_ty k e0 t2
        in Prod (y, t1, t2), loc

      | Eq (t, e1, e2) ->
        let t = instantiate_ty k e0 t
        and e1 = instantiate k e0 e1
        and e2 = instantiate k e0 e2
        in Eq (t, e1, e2), loc

      | Refl (t, e) ->
        let t = instantiate_ty k e0 t
        and e = instantiate k e0 e
        in Refl (t, e), loc

    end

  and instantiate_ty k e0 t = instantiate k e0 t
  
  and instantiate_bare k e0 (Bare e) = Bare (instantiate (k+1) e0 e)

  and instantiate_bare_ty k e0 (Bare t) = Bare (instantiate_ty (k+1) e0 t)

  in instantiate 0 e0 e

let instantiate_ty = instantiate

let occurs (Bare e) =
  let rec occurs k (e, loc) =
    begin match e with

      | Name _ -> false
        
      | Bound m -> k = m
        
      | Ascribe (e, t) -> occurs k e || occurs_ty k t
        
      | Lambda (_, t1, t2, e) ->
        occurs_ty k t1 || occurs_bare_ty k t2 || occurs_bare k e
          
      | Spine (t, e, es) ->
        occurs_ty k e || occurs k e || List.exists (occurs k) es
          
      | Type -> false
        
      | Prod (_, t1, t2) ->
        occurs_ty k t1 || occurs_bare_ty k t2

      | Eq (t, e1, e2) ->
        occurs_ty k t || occurs k e1 || occurs k e2

      | Refl (t, e) ->
        occurs_ty k t || occurs k e
    end

  and occurs_ty k t = occurs k t

  and occurs_bare k (Bare e) = occurs (k+1) e

  and occurs_bare_ty k (Bare t) = occurs_ty (k+1) t

  in occurs 0 e

let occurs_ty = occurs
