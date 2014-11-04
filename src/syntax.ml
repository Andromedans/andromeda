(** The abstract syntax of Andromedan type theory. *)

type term = term' * Position.t
and term' =
  | Name of Common.name
  | Bound of Common.bound
  | Ascribe of term * ty
  | Lambda of Common.name * ty * bare_ty * bare_term
  | App of (Common.name * ty * bare_ty) * term * term
  | Type
  | Prod of Common.name * ty * bare_ty
  | Eq of ty * term * term
  | Refl of ty * term

and ty = term

and bare_term = Bare of term

and bare_ty = bare_term

let mk_name ~loc x = Name x, loc
let mk_bound ~loc k = Bound k, loc
let mk_ascribe ~loc e t = Ascribe (e, t), loc
let mk_lambda ~loc x t1 t2 e = Lambda (x, t1, t2, e), loc
let mk_app ~loc x t1 t2 e1 e2 = App ((x, t1, t2), e1, e2), loc
let mk_type ~loc = Type, loc
let mk_prod ~loc x t1 t2 = Prod (x, t1, t2), loc
let mk_eq ~loc t e1 e2 = Eq (t, e1, e2), loc
let mk_refl ~loc t e = Refl (t, e), loc

let typ = mk_type ~loc:Position.Nowhere

(** Values *)
type value =
  | Judge of term * ty
  | String of string (* this is here just so that we anticipate other locsibilities *)

(** Alpha equality *)

let rec equal (e1,_) (e2,_) =
  begin match e1, e2 with

    | Name x, Name y -> Common.eqname x y

    | Bound i, Bound j -> i = j

    | Ascribe (e1,_), Ascribe (e2,_) -> 
        equal e1 e2 (* XXX Can we ignore the types? *)

    | Lambda (_, t1, t2, e), Lambda (_, t1', t2', e') ->
      equal_ty t1 t1' && 
      equal_bare_ty t2 t2' &&
      equal_bare e e'

    | App ((_, t1, t2), e1, e2), App ((_, t1', t2'), e1', e2') ->
      equal_ty t1 t1' && 
      equal_bare_ty t2 t2' &&
      equal e1 e1' && 
      equal e2 e2'

    | Type, Type -> true

    | Prod (_, t1, t2), Prod (_, t1', t2') ->
      equal_ty t1 t1' && 
      equal_bare_ty t2 t2'

    | Eq (t, e1, e2), Eq (t', e1', e2') ->
      equal_ty t t' && 
      equal e1 e1' &&
      equal e2 e2'

    | Refl (t, e), Refl (t', e') ->
      equal_ty t t' && 
      equal e e'

    | (Name _ | Bound _ | Ascribe _ | Lambda _ | App _ | Type | Prod _ | Eq _ | Refl _), _ ->
      false
  end

and equal_ty t1 t2 = equal t1 t2

and equal_bare (Bare e1) (Bare e2) = equal e1 e2

and equal_bare_ty (Bare t1) (Bare t2) = equal_ty t1 t2

(** Manipulation of variables *)

let abstract x e =
  let rec abstract k x ((e',loc) as e) =
    begin match e' with

      | Name y ->
        if Common.eqname x y then (Bound k, loc) else e

      | Bound _ -> e

      | Ascribe (e, t) ->
        let e = abstract k x e
        and t = abstract_ty k x t
        in Ascribe (e, t), loc

      | Lambda (y, t1, t2, e) ->
        let t1 = abstract_ty k x t1
        and t2 = abstract_bare_ty k x t2
        and e = abstract_bare k x e
        in Lambda (y, t1, t2, e), loc

      | App ((y, t1, t2), e1, e2) ->
        let t1 = abstract_ty k x t1
        and t2 = abstract_bare_ty k x t2
        and e1 = abstract k x e1
        and e2 = abstract k x e2
        in App ((y, t1, t2), e1, e2), loc

      | Type -> e

      | Prod (y, t1, t2) ->
        let t1 = abstract_ty k x t1
        and t2 = abstract_bare_ty k x t2
        in Prod (y, t1, t2), loc

      | Eq (t, e1, e2) ->
        let t = abstract_ty k x t
        and e1 = abstract k x e1
        and e2 = abstract k x e2
        in Eq (t, e1, e2), loc

      | Refl (t, e) ->
        let t = abstract_ty k x t
        and e = abstract k x e
        in Refl (t, e), loc
    end

  and abstract_ty k x t = abstract k x t

  and abstract_bare k x (Bare e) = Bare (abstract (k+1) x e)

  and abstract_bare_ty k x (Bare t) = Bare (abstract_ty (k+1) x t)

  in
    Bare (abstract 0 x e)

let abstract_ty = abstract


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

      | App ((y, t1, t2), e1, e2) ->
        let t1 = instantiate_ty k e0 t1
        and t2 = instantiate_bare_ty k e0 t2
        and e1 = instantiate k e0 e1
        and e2 = instantiate k e0 e2
        in App ((y, t1, t2), e1, e2), loc

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
          
      | App ((_, t1, t2), e1, e2) ->
        occurs_ty k t1 || occurs_bare_ty k t2 || occurs k e1 || occurs k e2
          
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
