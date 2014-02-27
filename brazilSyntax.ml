(** Abstract syntax of internal expressions. *)

module D = BrazilInput

(** Abstract syntax of expressions, where de Bruijn indices are used to represent
    variables. *)
type term =
  | Var    of int
  | Lambda of Common.variable * term * term
  | Pi     of Common.variable * term * term
  | App    of term * term
  | Sigma  of Common.variable * term * term
  | Pair   of term * term
  | Proj   of int * term                   (* 1 = fst, 2 = snd *)
  | Refl   of eqsort * term * term
  | Eq     of eqsort * term * term * term
  | J      of eqsort * term * term * term * term * term * term
  | U      of universe
  | Base   of basetype
  | Const  of constant

and universe = D.universe =
  | Type of int
  | Fib of int

and eqsort = D.eqsort =
  | Ju
  | Pr

and basetype =
  | TUnit

and constant =
  | Unit

(**************************************
   The Typing Rules. In all cases, the prior well-formedness of G is assumed


   -----------------
   G |- x : G(x)


   G |- t : U(u,i)   G, x:t |- e : t'
   -----------------------------------    [ annotate Lambda with t' too? ]
   G |- Lambda(x, t, e) : Pi(x, t, t')


   G |- t' : U(u,i)   G, x:t' |- t'' : U(u,i)
   ------------------------------------------
   G |- Pi(x, t', t'') : U(u,i)


   G |- e : Pi(x, t', t'')   G |- e' : t'
   --------------------------------------
   G |- e e' : [x->e']t''


   G |- t' : U(u,i)   G, x:t' |- t'' : U(u,i)
   ------------------------------------------
   G |- Sigma(x, t', t'') : U(u,i)


   G |- t' : U(u,i)   G , x:t' |- t'' : U(u,i)
   G |- e' : t'     G |- e'' : [x->e']t''
   -------------------------------------------   [ annotate Pair with the Sigma?]
   G |- <e', e''> :  Sigma(x, t', t'')


   G |- e : Sigma(x, t', t'')
   ---------------------------
   G |- e.1 : t'


   G |- e : Sigma(x, t', t'')
   ---------------------------
   G |- e.2 : [x->e.1]t''


   -----------------------
   G |- U(u,i) : U(u, i+1)


   G |- t :: U(u,i)   G |- e' : t    G |- e'' : t
   ----------------------------------------------
   G |- Id(u, e', e'', t) : U(u,i)


   G |- t :: U(u,i)   G |- e : t
   -----------------------------------
   G |- refl(o, e, t) : Id(o, e, e, t)


   G |- t : U(u,i)    G |- a : t    G |- b : t
   G |- q : Id(o, a, b, t)
   G, x:t, y:t, p:Id(o,a,b,t) |- c : U(u, j)                [ i & j independent? ]
   G, z : t |- w : [x,y,p->z,z,refl(o,z,t)]c
   if o = Ju then u = Fib
   ----------------------------------------------------
   G |- J(o, c, w, a, b, t, q) : [x,y,p->a,b,q]c


   -----------------
   G |- Unit : TUnit


   G |- e : t
   G |- t : U(u,i)   G |- u : U(u,i)   G |- t == u : U(u,i)
   --------------------------------------------------------
   G |- e : u


   G |- e : U(Fib, i)
   -------------------      [ An explicit coercion here seems painful ]
   G |- e : U(Type, i)


   G |- e : U(u, i)
   ------------------       [ Or do we want the explicit coercion? ]
   G |- e : U(u, i+1)

*)

(** [universe_join u1 u2] returns the universe that includes both [u1] and [u2]
*)
let universe_join u1 u2 =
  match u1, u2 with
  | Fib i, Fib j -> Fib (max i j)
  | Fib i, Type j
  | Type i, Fib j
  | Type i, Type j -> Type (max i j)

let universe_le u1 u2 =
  match u1, u2 with
  | Fib i, Fib j
  | Fib i, Type j
  | Type i, Type j -> i <= j
  | Type _, Fib _  -> false

(** [universe_classifier u] returns the universe classifying the given
 *  universe [u] *)
let universe_classifier = function
  | Fib i  -> Fib (i+1)
  | Type i -> Type (i+1)

(** [string_of_term term] creates an accurate but not-very-pretty textual
 * representation of the [term] datatype value.
*)
let rec string_of_term = function
  | Var i          -> string_of_int i
  | Lambda(x,t,e)  -> "Lambda(" ^ x ^ "," ^ string_of_terms [t;e] ^ ")"
  | Pi(x,t1,t2)    -> "Pi(" ^ x ^ "," ^ string_of_terms[t1;t2] ^ ")"
  | App(e1,e2)     -> "App(" ^ string_of_terms [e1;e2] ^ ")"
  | Sigma(x,t1,t2) -> "Sigma(" ^ x ^ "," ^ string_of_terms [t1;t2] ^ ")"
  | Pair(e1,e2)    -> "Pair(" ^ string_of_terms [e1;e2] ^ ")"
  | Proj(i1,e2)    -> "Proj(" ^ string_of_int i1 ^ "," ^ string_of_term e2 ^ ")"
  | Refl(o,e,t)    -> "Refl("  ^ string_of_eqsort o ^ "," ^ string_of_terms [e;t] ^ ")"
  | Eq(o,e1,e2,t)  -> "Eq(" ^ string_of_eqsort o ^ "," ^ string_of_terms [e1;e2] ^ ")"
  | J(o,c,w,a,b,t,q)
    -> "J(" ^ string_of_eqsort o ^ "," ^ string_of_terms [c;w;a;b;t;q] ^ ")"
  | U univ  -> "U(" ^ string_of_universe univ ^ ")"
  | Base b  -> string_of_basetype b
  | Const c -> string_of_constant c

(* comma-separated terms *)
and string_of_terms ts =
  String.concat "," (List.map string_of_term ts)

and string_of_eqsort = function
  | Ju -> "Ju"
  | Pr -> "Pr"

and string_of_universe = function
  | Type i -> "Type_" ^ string_of_int i
  | Fib i  -> "Fib_" ^ string_of_int i

and string_of_basetype = function
  | TUnit -> "TUnit"

and string_of_constant = function
  | Unit -> "Unit"


(** [shift cut delta] shifts the indices by [delta] with a cutoff of [cut]. *)
(* See, e.g., http://ecee.colorado.edu/~siek/ecen5013/spring10/lecture4.pdf
   The rule is: increase cut by one for each binder.
*)
let shift ?(cut=0) delta =
  let rec loop cut = function
    | Var m -> if (m < cut) then Var m else Var(m+delta)
    | Lambda (x, t, e)  -> Lambda (x, loop cut t, loop (cut+1) e)
    | App (e1, e2)      -> App(loop cut e1, loop cut e2)
    | Pi (x, t1, t2)    -> Pi(x, loop cut t1, loop (cut+1) t2)
    | Sigma (x, t1, t2) -> Sigma(x, loop cut t1, loop (cut+1) t2)
    | Pair (e1, e2)     -> Pair(loop cut e1, loop cut e2)
    | Proj (i1, e2)     -> Proj(i1, loop cut e2)
    | Refl (o, e, t)    -> Refl(o, loop cut e, loop cut t)
    | Eq (o, e1, e2, t) -> Eq(o, loop cut e1, loop cut e2, loop cut t)
    | J (o, c, w, a, b, t, q) -> J(o, loop (cut+3) c, loop (cut+1) w,
                                   loop cut a, loop cut b,
                                   loop cut t, loop cut q)
    | (U _ | Base _ | Const _) as term -> term  in
  loop cut


(** [subst j e' e] replaces the free occurrences of variable [j] in [e] by [e'].  *)
(* The rule is: shift the substituted expression e' by one for each binder
*)
let rec subst j e' = function
  | Var m             -> if (j = m) then e' else Var m

  | Lambda (x,t,e)    -> Lambda(x, subst j e' t, subst (j+1) (shift 1 e') e)
  | App(e1, e2)       -> App(subst j e' e1, subst j e' e2)
  | Pair(e1, e2)      -> Pair(subst j e' e1, subst j e' e2)
  | Proj(i1, e2)      -> Proj(i1, subst j e' e2)
  | Pi (x, t1, t2)    -> Pi(x, subst j e' t1, subst (j+1) (shift 1 e') t2)
  | Sigma (x, t1, t2) -> Sigma(x, subst j e' t1, subst (j+1) (shift 1 e') t2)
  | Refl(o, e, t)     -> Refl(o, subst j e' e, subst j e' t)
  | Eq(o, e1, e2, t)  -> Eq(o, subst j e' e1, subst j e' e2, subst j e' t)
  | J(o, c, w, a, b, t, q) -> J(o, subst (j+3) (shift 2 e') c,
                                subst (j+1) (shift 1 e') w,
                                subst j e' a, subst j e' b,
                                subst j e' t, subst j e' q)
  | (U _ | Base _ | Const _) as term -> term


(** [beta body arg] substitutes [arg] in for variable [0] in [body].
 * This is exactly the substitution required, for example, to
 * beta-reduce a function application ([body] is the body of the lambda),
 * or to substitute away the parameter in a [Pi] or [Sigma] type ([body] is
 * the type of the codomain or second component, respectively).
*)
and beta eBody eArg =
  shift (-1) (subst 0 (shift 1 eArg) eBody)


(** [occurs v e] returns [true] when variable [Var v] occurs freely in [e]. *)
(* The rule is: increase the variable number by one (shift it)
   whenever we enter a binder *)
let rec occurs v e =
  match e with
  | Var m -> m = v

  | Lambda (_, t, e)       -> occurs v t  || occurs (v+1) e
  | App (e1, e2)           -> occurs v e1 || occurs v e2
  | Pair (e1, e2)          -> occurs v e1 || occurs v e2
  | Proj (_, e2)           -> occurs v e2
  | Refl (_, e, t)         -> occurs v e  || occurs v t
  | Pi (_, t1, t2)         -> occurs v t1 || occurs (v+1) t2
  | Sigma (_, t1, t2)      -> occurs v t1 || occurs (v+1) t2
  | Eq (_, e1, e2, t)      -> occurs v e1 || occurs v e2 || occurs v t
  | J(_, c, w, a, b, t, p) -> occurs (v+3) c || occurs (v+1) w ||
                              occurs v a || occurs v b ||
                              occurs v t || occurs v p

  | (U _ | Base _ | Const _) -> false


(** Compare two expressions using alpha-equivalence only. *)
(* You'd think that this is where de Bruijn indices pay off,
 * But since we're preserving variable names in our tree structure,
 * we can't just use ML structural equality :(
*)
let rec equal e1 e2 =
  match e1, e2 with
  | Var v1, Var v2     -> v1 = v2
  | U u1, U u2         -> u1 = u2
  | Base b1, Base b2   -> b1 = b2
  | Const c1, Const c2 -> c1 = c2

  | Lambda(_, t11, t12), Lambda(_, t21, t22)
  | Pi(_, t11, t12), Pi(_, t21, t22)
  | Sigma(_, t11, t12), Sigma(_, t21, t22)
  | Pair(t11, t12), Pair(t21, t22)
  | App(t11, t12), App(t21, t22) ->
      equal t11 t21 && equal t12 t22

  | Proj(i1, t1), Proj(i2, t2) ->
      i1 = i2 && equal t1 t2

  | Refl(o1, t11, t12), Refl(o2, t21, t22) ->
      o1 = o2 && equal t11 t21 && equal t12 t22

  | Eq(o1, t11, t12, t13), Eq(o2, t21, t22, t23) ->
      o1 = o2 && equal t11 t21 && equal t12 t22 && equal t13 t23

  | J(o1, t11, t12, t13, t14, t15, t16),
    J(o2, t21, t22, t23, t24, t25, t26) ->
      o1 = o2 && equal t11 t21 && equal t12 t22 && equal t13 t23
      && equal t14 t24 && equal t15 t25 && equal t16 t26

  | (Var _ | Lambda _ | Pi _ | App _ | Sigma _ | Pair _ | Proj _
      | Refl _ | Eq _ | J _ | U _ | Base _ | Const _), _ -> false

type operation =
  | Inhabit of term

and computation = Common.debruijn D.term

and handler = (operation * computation) list


let rec shiftOperation ?(cut=0) delta = function
  | Inhabit term -> Inhabit (shift ~cut delta term)

