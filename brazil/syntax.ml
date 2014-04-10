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
  | Equation of term * term
  | Rewrite of term * term
  | Ascribe of term * ty
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | UnitTerm
  | Idpath of ty * term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of ty * term
  | Coerce of universe * universe * term
  | NameUnit
  | NameProd of name * term * term
  | NameUniverse of universe
  | NamePaths of term * term * term
  | NameId of term * term * term

(*********************)
(* Alpha-Equivalence *)
(*********************)

(** Unfortunately, we cannot use ML's built-in = operator for alpha equivalence,
    because we maintain variable names and source locations (for debugging and
    error-reporting) in terms.
*)

let rec equal (left,_) (right,_) =
  match left, right with

  | Var index1, Var index2 -> index1 = index2

  | Equation(   term1, term2), Equation(   term3, term4)
  | Rewrite (   term1, term2), Rewrite (   term3, term4)
  | NameProd(_, term1, term2), NameProd(_, term3, term4) ->
      equal term1 term3 && equal term2 term4

  | Ascribe(term1, ty2), Ascribe(term3, ty4) ->
      equal term1 term3 && equal_ty ty2 ty4

  | Lambda(_, ty1, ty2, term3), Lambda(_, ty4, ty5, term6) ->
      equal_ty ty1 ty4 && equal_ty ty2 ty5 && equal term3 term6

  | App((_,ty1,ty2),term3,term4), App((_,ty5,ty6),term7,term8) ->
      equal_ty ty1 ty5 && equal_ty ty2 ty6
      && equal term3 term7 && equal term4 term8

  | UnitTerm, UnitTerm
  | NameUnit, NameUnit -> true

  | Idpath(ty1, term2), Idpath(ty3, term4)
  | Refl  (ty1, term2), Refl  (ty3, term4) ->
      equal_ty ty1 ty3 && equal term2 term4

  | J(ty1, (_, _, _, ty2), (_, term3), term4, term5, term6),
    J(ty7, (_, _, _, ty8), (_, term9), term10, term11, term12) ->
      equal_ty ty1 ty7 && equal_ty ty2 ty8 && equal term3 term9
      && equal term4 term10 && equal term5 term11 && equal term6 term12

  | Coerce(universe1, universe2, term3), Coerce(universe4, universe5, term6) ->
      universe1 = universe4 && universe2 = universe5 && equal term3 term6

  | NameUniverse universe1, NameUniverse universe2 ->
      universe1 = universe2

  | NamePaths(term1, term2, term3), NamePaths(term4, term5, term6)
  | NameId   (term1, term2, term3), NameId   (term4, term5, term6) ->
      equal term1 term4 && equal term2 term5 && equal term3 term6

  | (Var _ | Equation _ | Rewrite _ | Ascribe _ | Lambda _ | App _
     | UnitTerm | Idpath _ | J _ | Refl _ | Coerce _
     | NameUnit | NameProd _ | NameUniverse _ | NamePaths _| NameId _), _ ->
         false


and equal_ty (left_ty,_) (right_ty,_) =
  match left_ty, right_ty with

  | Universe universe1, Universe universe2 ->
      universe1 = universe2

  | El(universe1, term2), El(universe3, term4) ->
      universe1 = universe3 && equal term2 term4

  | Unit, Unit -> true

  | Prod(_, ty1, ty2), Prod(_, ty3, ty4) ->
      equal_ty ty1 ty3 && equal_ty ty2 ty4

  | Paths(ty1, term2, term3), Paths(ty4, term5, term6)
  | Id   (ty1, term2, term3), Id   (ty4, term5, term6) ->
      equal_ty ty1 ty4 && equal term2 term5 && equal term3 term6

  | (Universe _ | El _ | Unit | Prod _ | Paths _ | Id _), _ ->
      false


(** Shifting and substitution are almost exactly the same code. We
   factor out this common pattern into [transform], which rewrites all the
   *free* variables of a term using a generic transformation function [ftrans].
   [transform] recursively maintains a count [bvs], the number of bound variables whose
   scope we are in, and provides that count to [ftrans] along with the raw
   (local) index of the free variable.
*)
let rec transform ftrans bvs (term', loc) =
  (* Shorthand for recursive calls *)
  let recurse    = transform ftrans bvs in
  let recurse_ty = transform_ty ftrans bvs in
  (* Shorthand for recursive calls on terms/types that are
     inside n new binders *)
  let recurse_in_binders    n = transform    ftrans (bvs+n) in
  let recurse_ty_in_binders n = transform_ty ftrans (bvs+n) in

  (match term' with

  | Var index ->
      if (index < bvs) then
        (* This is a reference to a bound variable; don't transform *)
        Var index
      else
        (* This is a free variable; transform *)
        ftrans bvs index

  | Equation(term1, term2) -> Equation(recurse term1, recurse term2)

  | Rewrite(term1, term2)  -> Rewrite(recurse term1, recurse term2)

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

  | NameProd(name, term1, term2) ->
      NameProd(name, recurse term1, recurse_in_binders 1 term2)

  | NameUniverse universe1 -> NameUniverse universe1

  | NamePaths(term1, term2, term3) ->
      NamePaths(recurse term1, recurse term2, recurse term3)

  | NameId(term1, term2, term3) ->
      NameId(recurse term1, recurse term2, recurse term3)),
  loc

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

let ftrans_shift delta _ index =
  begin
    (* Add delta to the index of this free variable *)
    assert (index + delta >= 0);
    Var (index + delta);
  end

let shift    ?(bvs=0) delta = transform    (ftrans_shift delta) bvs
let shift_ty ?(bvs=0) delta = transform_ty (ftrans_shift delta) bvs

let ftrans_subst free_index replacement_term bvs index =
  if index - bvs = free_index then
    (* It's the variable we're looking for. *)
    replacement_term
  else
    Var index

(** [subst j e' e] is a transformation that replaces free occurrences
    of variable [j] in [e] (relative to the "outside" of the term) by [e'].
*)
let subst    free_index replacement_term = transform    (ftrans_subst free_index replacement_term) 0
let subst_ty free_index replacement_term = transform_ty (ftrans_subst free_index replacement_term) 0




