(** Annotated abstract syntax for Brazilian type theory. *)

type name = string

(** We use de Bruijn indices *)
type variable = Common.debruijn

type universe = Universe.t * Position.t

type ty = ty' * Position.t
and ty' =
  | Universe of universe
  | El of universe * term
  | Unit
  | Prod of name * ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term = term' * Position.t
and term' =
  | Var of variable
  | Equation of term * (term * term) * term
  | Rewrite of term * (term * term) * term
  | Ascribe of term * ty
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | UnitTerm
  | Idpath of ty * term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of ty * term
  | Coerce of universe * universe * term
  | NameUnit
  | NameProd of universe * universe * name * term * term
  | NameUniverse of universe
  | NamePaths of universe * term * term * term
  | NameId of universe * term * term * term

(*********************)
(* Alpha-Equivalence *)
(*********************)

(** We cannot use ML's built-in = operator for alpha equivalence,
    because we maintain variable names and source locations (for debugging and
    error-reporting) in terms. So, we write the obvious recursive traversal
    code.

    Also, and more importantly, we need a traversal because we ignore magenta
    annotations, because they are deterministically constructed from non-magenta
    terms and types.

    We also ignore equation and rewrite hints, because they should be thought
    of as computations rather than expressions.
*)

let rec equal ((left',_) as left) ((right',_) as right) =
  match left', right' with

  | Var index1, Var index2 -> index1 = index2

  | Equation(_, _, term1), _ -> equal term1 right
  | _, Equation(_, _, term1) -> equal left  term1

  | Rewrite(_, _, term1), _ -> equal term1 right
  | _, Rewrite(_, _, term1) -> equal left  term1

  | NameProd(_universe1, _universe2, _, term3, term4),
    NameProd(_universe5, _universe6, _, term7, term8) ->
      (* universe1 = universe5 && universe2 == universe6 && *)
      equal term3 term7 && equal term4 term8

  | Ascribe(term1, ty2), Ascribe(term3, ty4) ->
      equal term1 term3 && equal_ty ty2 ty4

  | Lambda(_, ty1, _ty2, term3), Lambda(_, ty4, _ty5, term6) ->
      equal_ty ty1 ty4 (* && equal_ty ty2 ty5 *) && equal term3 term6

  | App((_,_ty1,_ty2),term3,term4), App((_,_ty5,_ty6),term7,term8) ->
      (* equal_ty ty1 ty5 && equal_ty ty2 ty6 && *)
      equal term3 term7 && equal term4 term8

  | UnitTerm, UnitTerm
  | NameUnit, NameUnit -> true

  | Idpath(_ty2, term3), Idpath(_ty5, term6)
  | Refl  (_ty2, term3), Refl  (_ty5, term6) ->
      (* equal_ty ty2 ty5 && *)
      equal term3 term6

  | J(ty1, (_, _, _, ty2), (_, term3), term4, _term5, _term6),
    J(ty7, (_, _, _, ty8), (_, term9), term10, _term11, _term12) ->
      (* equal_ty ty1 ty7 && *)
      equal_ty ty2 ty8 && equal term3 term9 && equal term4 term10
      (* && equal term5 term11 && equal term6 term12 *)

  | Coerce(_universe1, (universe2',_), term3), Coerce(_universe4, (universe5',_), term6) ->
      (* universe1 = universe4 && *)
      universe2' = universe5' && equal term3 term6

  | NameUniverse (universe1',_), NameUniverse (universe2',_) ->
      universe1' = universe2'

  | NamePaths(_universe1, term2, term3, term4), NamePaths(_universe5, term6, term7, term8)
  | NameId   (_universe1, term2, term3, term4), NameId   (_universe5, term6, term7, term8) ->
      (* universe1 = universe5 && *)
      equal term2 term6 && equal term3 term7 && equal term4 term8

  | (Var _ | Ascribe _ | Lambda _ | App _
     | UnitTerm | Idpath _ | J _ | Refl _ | Coerce _
     | NameUnit | NameProd _ | NameUniverse _ | NamePaths _| NameId _), _ ->
         false


and equal_ty (left_ty,_) (right_ty,_) =
  match left_ty, right_ty with

  | Universe (universe1',_), Universe (universe2',_) ->
      universe1' = universe2'

  | El((universe1',_), term2), El((universe3',_), term4) ->
      universe1' = universe3' && equal term2 term4

  | Unit, Unit -> true

  | Prod(_, ty1, ty2), Prod(_, ty3, ty4) ->
      equal_ty ty1 ty3 && equal_ty ty2 ty4

  | Paths(ty1, term2, term3), Paths(ty4, term5, term6)
  | Id   (ty1, term2, term3), Id   (ty4, term5, term6) ->
      equal_ty ty1 ty4 && equal term2 term5 && equal term3 term6

  | (Universe _ | El _ | Unit | Prod _ | Paths _ | Id _), _ ->
      false

(*******************)
(* Transformations *)
(*******************)

(** Shifting and substitution are almost exactly the same code. We
   factor out this common pattern into [transform], which rewrites an
   expression by recursively traversing the term and then applying
   a generic transformation function [ftrans].

   [transform] recursively maintains a count [bvs], the number of bound variables whose
   scope we are in, and provides that count to [ftrans] along with the
   recursively transformed term.
*)
let rec transform ftrans bvs (term', loc) =
  (* Shorthand for recursive calls *)
  let recurse    = transform ftrans bvs in
  let recurse_ty = transform_ty ftrans bvs in
  (* Shorthand for recursive calls on terms/types that are
     inside n new binders *)
  let recurse_in_binders    n = transform    ftrans (bvs+n) in
  let recurse_ty_in_binders n = transform_ty ftrans (bvs+n) in

  ftrans bvs
    ((match term' with

      | Var _index -> term'

      | Equation(term1, (term2,term3), term4) ->
          Equation(recurse term1, (recurse term2, recurse term3), recurse term4)

      | Rewrite(term1, (term2,term3), term4) ->
          Rewrite(recurse term1, (recurse term2, recurse term3), recurse term4)

      | Ascribe(term1, ty2)    -> Ascribe(recurse term1, recurse_ty ty2)

      | Lambda(name, ty1, ty2, term1) ->
          Lambda(name, recurse_ty ty1,
                   recurse_ty_in_binders 1 ty2, recurse_in_binders 1 term1)

      | App((name, ty1, ty2), term1, term2) ->

          App((name, recurse_ty ty1, recurse_ty_in_binders 1 ty2),
                recurse term1, recurse term2)

      | UnitTerm -> UnitTerm

      | Idpath(ty1, term2) -> Idpath(recurse_ty ty1, recurse term2)

      | J(ty1, (name1, name2, name3, ty2), (name4, term2), term3, term4, term5) ->
          J(recurse_ty ty1,
              (name1, name2, name3, recurse_ty_in_binders 3 ty2),
              (name4, recurse_in_binders 1 term2),
              recurse term3, recurse term4, recurse term5)

      | Refl(ty1, term2)  -> Refl (recurse_ty ty1, recurse term2)

      | Coerce(universe1, universe2, term1) -> Coerce(universe1, universe2, recurse term1)

      | NameUnit -> NameUnit

      | NameProd(universe1, universe2, name, term1, term2) ->
          NameProd(universe1, universe2, name, recurse term1, recurse_in_binders 1 term2)

      | NameUniverse universe1 -> NameUniverse universe1

      | NamePaths(universe1, term1, term2, term3) ->
          NamePaths(universe1, recurse term1, recurse term2, recurse term3)

      | NameId(universe1, term1, term2, term3) ->
          NameId(universe1, recurse term1, recurse term2, recurse term3)),
    loc)

and transform_ty ftrans bvs (ty', loc) =
  let recurse    = transform    ftrans bvs in
  let recurse_ty = transform_ty ftrans bvs in

  let recurse_ty_in_binders n = transform_ty ftrans (bvs+n)  in
  (match ty' with

  | Universe universe1 -> Universe universe1

  | El(universe1, term1) -> El (universe1, recurse term1)

  | Unit -> Unit

  | Prod(name, ty1, ty2) ->
      Prod(name, recurse_ty ty1, recurse_ty_in_binders 1 ty2)

  | Paths(ty1, term1, term2) ->
      Paths(recurse_ty ty1, recurse term1, recurse term2)

  | Id(ty1, term1, term2) ->
      Id(recurse_ty ty1, recurse term1, recurse term2)),
  loc

(** [shift delta e] is a transformation that adds [delta] to all
    free variable indices in [e].
*)

let ftrans_shift delta bvs = function
  | (Var index, loc) as var ->
      if (index < bvs) then
        (* This is a reference to a bound variable; don't transform *)
        var
      else
        begin
          (* Add delta to the index of this free variable *)
          assert (index + delta >= 0);
          (Var (index + delta), loc);
        end

  | nonvar -> nonvar

let shift'    bvs delta = transform    (ftrans_shift delta) bvs
let shift_ty' bvs delta = transform_ty (ftrans_shift delta) bvs

let shift delta    = shift' 0 delta
let shift_ty delta = shift_ty' 0 delta

let ftrans_subst free_index replacement_term bvs = function
  | (Var index, loc) as var ->
      if index - bvs = free_index then
        (* It's the variable we're looking for.
           Shift it to match the local context *)
        shift bvs replacement_term
      else
        var
  | nonvar -> nonvar

(** [subst j e' e] is a transformation that replaces free occurrences
    of variable [j] in [e] (relative to the "outside" of the term) by [e'].
*)
let subst    free_index replacement_term = transform    (ftrans_subst free_index replacement_term) 0
let subst_ty free_index replacement_term = transform_ty (ftrans_subst free_index replacement_term) 0


(**************************)

 (** [beta body arg] substitutes [arg] in for variable [0] in [body].

  So, if [G, x:t |- body : ...] and [G |- arg : t] then
  [beta body arg] is the term [body[x->arg]].

  This is exactly the substitution required, for example, to
  beta-reduce a function application ([body] is the body of the lambda),
  or to substitute away the parameter in a [Pi] or [Sigma] type ([body] is
  the type of the codomain or second component, respectively).
*)
let beta eBody eArg =
  shift (-1) (subst 0 (shift 1 eArg) eBody)

let beta_ty eBody eArg =
  shift_ty (-1) (subst_ty 0 (shift 1 eArg) eBody)

let make_arrow ?(loc=Position.nowhere) dom cod =
  Prod("_", dom, shift_ty 1 cod), loc

(*let make_star ?(loc=Position.nowhere) fst snd =*)
  (*Sum("_", fst, shift 1 snd), loc*)

(**
  Suppose we have [G, x_1:t_1, ..., x_n:t_n |- exp : ...] and the inhabitants
  [e_1; ...; e_n] all well-formed in [G] (!) with types [t_1] through [t_n]
  respectively. Then [strengthen exp [e_1,...,e_n]] is the result of
  substituting away the x_i's, resulting in a term well-formed in [G].

  In particular, [strengthen env eBody [eArg]] is just [beta eBody
 *)
let strengthen exp inhabitants =
  let rec loop n accum = function
    | [] -> accum
    | inhabitant :: inhabitants ->
        begin
          let accum' = beta accum (shift (n-1) inhabitant)  in
          loop (n-1) accum' inhabitants
        end  in
  loop (List.length inhabitants) exp (List.rev inhabitants)

let strengthen_ty ty inhabitants =
  let rec loop n accum = function
    | [] -> accum
    | inhabitant :: inhabitants ->
        begin
          let accum' = beta_ty accum (shift (n-1) inhabitant)  in
          loop (n-1) accum' inhabitants
        end  in
  loop (List.length inhabitants) ty (List.rev inhabitants)

(** If [G |- exp] then [G' |- weaken i exp] where [G'] has an extra (unused)
     variable inserted at position [i]. This is just a simple renumbering, with
     all free variables [< i] unchanged, and all [>= i] incremented (because
     there's a new variable in front of them). *)
let weaken new_var_pos exp =
  shift' new_var_pos 1 exp

let weaken_ty new_var_pos ty =
  shift_ty' new_var_pos 1 ty



(* Try to find the (candidate) name and universe of a given type.
   If the type is well-formed, then this will be the name
   and the universe of that name *)

let rec name_of (ty', loc) =

  (* Compute the name term and the universe, without the outermost loc *)
  let answer' =

    match ty' with

    | Universe ((alpha',_) as alpha) ->
        Some( NameUniverse alpha, Universe.succ alpha' )

    | El ((alpha,_), (e', _)) ->
        Some( e', alpha )

    | Unit ->
        Some( NameUnit, Universe.zero )

    | Prod(x,t,u) ->
        begin
          match name_of t, name_of u with
          | Some (name_t, ((alpha',_) as alpha)), Some (name_u, ((beta',_) as beta)) ->
              Some( NameProd(alpha, beta, x, name_t, name_u),
                    Universe.max alpha' beta' )
          | _ -> None
        end

    | Paths(t,e2,e3) ->
        begin
          match name_of t with
          | Some (name_t, ((alpha',_) as alpha)) ->
              Some ( NamePaths(alpha, name_t, e2, e3), alpha')
          | None -> None
        end

    | Id(t,e2,e3) ->
        begin
          match name_of t with
          | Some (name_t, ((alpha',_) as alpha)) ->
              Some ( NameId(alpha, name_t, e2, e3), alpha')
          | None -> None
        end

  in
     (* Reattach the location, if we succeeded *)
     match answer' with
     | None -> None
     | Some (name', universe') -> Some ((name', loc), (universe', loc))



(***************)
(* Occurrences *)
(***************)

(** Does DeBruijn index occur in a term? *)
let rec occurs k (e, _) =
  match e with
    | Var m -> k = m
    | Equation (e1, (e2, e3), e4) -> occurs k e1 || occurs k e2 || occurs k e3 || occurs k e4
    | Rewrite (e1, (e2, e3), e4) -> occurs k e1 || occurs k e2 || occurs k e3 || occurs k e4
    | Ascribe (e, t) -> occurs k e || occurs_ty k t
    | Lambda (_, t, u, e) -> occurs_ty k t || occurs_ty (k+1) u || occurs (k+1) e
    | App ((_, t, u), e1, e2) -> occurs_ty k t || occurs_ty (k+1) u || occurs k e1 || occurs k e2
    | UnitTerm -> false
    | Idpath (t, e) -> occurs_ty k t || occurs k e
    | J (t, (_, _, _, u), (_, e1), e2, e3, e4) ->
      occurs_ty k t || occurs_ty (k+3) u || occurs (k+1) e1 ||
        occurs k e2 || occurs k e3 || occurs k e4
    | Refl (t, e) -> occurs_ty k t || occurs k e
    | Coerce (_, _, e) -> occurs k e
    | NameUnit -> false
    | NameProd (_, _, _, e1, e2) -> occurs k e1 || occurs (k+1) e2
    | NameUniverse _ -> false
    | NamePaths (_, e1, e2, e3) -> occurs k e1 || occurs k e2 || occurs k e3
    | NameId (_, e1, e2, e3) -> occurs k e1 || occurs k e2 || occurs k e3

(** Does DeBruijn index occur in a type? *)
and occurs_ty k (t, _) =
  match t with
    | Universe _ -> false
    | El (_, e) -> occurs k e
    | Unit -> false
    | Prod (_, t1, t2) -> occurs_ty k t1 || occurs_ty (k+1) t2
    | Paths (t, e1, e2) -> occurs_ty k t || occurs k e1 || occurs k e2
    | Id (t, e1, e2) -> occurs_ty k t || occurs k e1 || occurs k e2

(* Counting Occurrences *)

(** Count occurrences of DeBruijn index in a term? *)
let rec occurrences k (e, _) =
  match e with

    | Var m -> if k = m then 1 else 0

    | Equation (e1, (e2, e3), e4) ->
      occurrences k e1 + occurrences k e2 + occurrences k e3 + occurrences k e4

    | Rewrite (e1, (e2, e3), e4) ->
      occurrences k e1 + occurrences k e2 + occurrences k e3 + occurrences k e4

    | Ascribe (e, t) ->
      occurrences k e + occurrences_ty k t

    | Lambda (_, t, u, e) ->
      occurrences_ty k t + occurrences_ty (k+1) u + occurrences (k+1) e

    | App ((_, t, u), e1, e2) ->
      occurrences_ty k t + occurrences_ty (k+1) u + occurrences k e1 + occurrences k e2

    | UnitTerm -> 0

    | Idpath (t, e) ->
      occurrences_ty k t + occurrences k e

    | J (t, (_, _, _, u), (_, e1), e2, e3, e4) ->
      occurrences_ty k t + occurrences_ty (k+3) u + occurrences (k+1) e1 +
        occurrences k e2 + occurrences k e3 + occurrences k e4

    | Refl (t, e) -> occurrences_ty k t + occurrences k e

    | Coerce (_, _, e) -> occurrences k e

    | NameUnit -> 0

    | NameProd (_, _, _, e1, e2) ->
      occurrences k e1 + occurrences (k+1) e2

    | NameUniverse _ -> 0

    | NamePaths (_, e1, e2, e3) ->
      occurrences k e1 + occurrences k e2 + occurrences k e3

    | NameId (_, e1, e2, e3) ->
      occurrences k e1 + occurrences k e2 + occurrences k e3

(** Count occurrences of DeBruijn index in a type? *)
and occurrences_ty k (t, _) =
  match t with
    | Universe _ -> 0
    | El (_, e) -> occurrences k e
    | Unit -> 0
    | Prod (_, t1, t2) -> occurrences_ty k t1 + occurrences_ty (k+1) t2
    | Paths (t, e1, e2) -> occurrences_ty k t + occurrences k e1 + occurrences k e2
    | Id (t, e1, e2) -> occurrences_ty k t + occurrences k e1 + occurrences k e2

(******************)
(* Simplification *)
(******************)

(* Reduce very simple (almost administrative) lambdas *)

(** Is this argument simple enought to be worth plugging into an
   arbitrary lambda?
*)
let rec simple_term term =
  match fst term with
  | UnitTerm       -> true
  | Var _          -> true
  | App(_, e1, e2) -> simple_term e1 && simple_term e2
  | NameUnit       -> true
  | NameUniverse _ -> true
  | Refl (t,e)     -> simple_term e
  | Idpath (t,e)   -> simple_term e
  | _              -> false

let ftrans_simplify bvs term =
  match fst term with
  | App((x1,ty2,ty3), (Lambda(x4,ty5,ty6,e7),_), e8) when equal_ty ty2 ty5
                                                       && equal_ty ty3 ty6 ->
      (* Reduce if the type annotations match literally,
       * and either the argument is very simple or the
       * lambda ignores its term or is linear.
       *)
      if simple_term e8 || (occurrences 0 e7 <= 1) then
        beta e7 e8
      else
        term

  | _ -> term

let simplify = transform ftrans_simplify 0
let simplify_ty = transform_ty ftrans_simplify 0
