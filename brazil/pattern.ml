(** Lazy pattern matching, to figure out which rewrite rules apply. *)

type name = string

type universe = Universe.t

type ty =
  | Ty of Syntax.ty
  | El of universe * term
  | Prod of name * ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term =
  | Term of Syntax.term
  | PVar of int
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | Idpath of ty * term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of ty * term
  | Coerce of universe * universe * term
  | NameProd of universe * universe * name * term * term
  | NamePaths of universe * term * term * term
  | NameId of universe * term * term * term

let rec of_ty' k l ((t', loc) as t) =
  match t' with

    | Syntax.Universe _ ->
      Ty t

    | Syntax.El (alpha, e) ->
      let e = of_term' k l e in
      begin match e with
        | Term e -> Ty (Syntax.El (alpha, e), loc)
        | _ -> El (alpha, e)
      end

    | Syntax.Unit ->
      Ty t

    | Syntax.Prod (x, t1, t2) ->
      let t1 = of_ty' k l t1
      and t2 = of_ty' k (l+1) t2
      in
        begin match t1, t2 with
          | Ty t1, Ty t2 -> Ty (Syntax.Prod (x, t1, t2), loc)
          | _ -> Prod (x, t1, t2)
        end

    | Syntax.Paths (t, e1, e2) ->
      let t = of_ty' k l t
      and e1 = of_term' k l e1
      and e2 = of_term' k l e2
      in
        begin match t, e1, e2 with
          | Ty t, Term e1, Term e2 -> Ty (Syntax.Paths (t, e1, e2), loc)
          | _ -> Paths (t, e1, e2)
        end

    | Syntax.Id (t, e1, e2) ->
      let t = of_ty' k l t
      and e1 = of_term' k l e1
      and e2 = of_term' k l e2
      in
        begin match t, e1, e2 with
          | Ty t, Term e1, Term e2 -> Ty (Syntax.Id (t, e1, e2), loc)
          | _ -> Id (t, e1, e2)
        end

and of_term' k l ((e', loc) as e) =
  match e' with

    | Syntax.Var j ->
      if j < l then Term (Syntax.Var j, loc) (* bound variable *)
      else if j < k + l then PVar (j - l) (* pattern variable *)
      else Term (Syntax.Var (j - k), loc) (* other variable *)

    | Syntax.Equation (_, _, e2) ->
      of_term' k l e

    | Syntax.Rewrite (_, _, e) ->
      of_term' k l e

    | Syntax.Ascribe (e, _) ->
      of_term' k l e

    | Syntax.Lambda (x, t1, t2, e) ->
      let t1 = of_ty' k l t1
      and t2 = of_ty' k (l+1) t2
      and e = of_term' k l e
      in
        begin match t1, t2, e with
          | Ty t1, Ty t2, Term e -> Term (Syntax.Lambda (x, t1, t2, e), loc)
          | _ -> Lambda (x, t1, t2, e)
        end

    | Syntax.App ((x, t1, t2), e1, e2) ->
      let e1 = of_term' k l  e1
      and e2 = of_term' k l e2
      and t2 = of_ty' k (l+1) t2
      and t1 = of_ty' k l t1
      in
        begin match t1, t2, e1, e2 with
          | Ty t1, Ty t2, Term e1, Term e2 ->
            Term (Syntax.App ((x, t1, t2), e1, e2), loc)
          | _ -> App ((x, t1, t2), e1, e2)
        end

    | Syntax.UnitTerm ->
      Term e

    | Syntax.Idpath (t, e) ->
      let t = of_ty' k l t
      and e = of_term' k l e
      in
        begin match t, e with
          | Ty t, Term e -> Term (Syntax.Idpath (t, e), loc)
          | _ -> Idpath (t, e)
        end

    | Syntax.J (t, (x,y,p,u), (z,e1), e2, e3, e4) ->
      let t = of_ty' k l t
      and u = of_ty' k (l+3) u
      and e1 = of_term' k (l+1) e1
      and e2 = of_term' k l e2
      and e3 = of_term' k l e3
      and e4 = of_term' k l e4
      in
        begin match t, u, e1, e2, e3, e4 with
          | Ty t, Ty u, Term e1, Term e2, Term e3, Term e4 ->
            Term (Syntax.J (t, (x,y,p,u), (z,e1), e2, e3, e4), loc)
          | _ -> J (t, (x,y,p,u), (z,e1), e2, e3, e4)
        end

    | Syntax.Refl (t, e) ->
      let t = of_ty' k l t
      and e = of_term' k l e
      in
        begin match t, e with
          | Ty t, Term e -> Term (Syntax.Idpath (t, e), loc)
          | _ -> Idpath (t, e)
        end

    | Syntax.Coerce (alpha, beta, e) ->
      let e = of_term' k l e
      in
        begin match e with
          | Term e -> Term (Syntax.Coerce (alpha, beta, e), loc)
          | _ -> Coerce (alpha, beta, e)
        end

    | Syntax.NameUnit ->
      Term e

    | Syntax.NameProd (alpha, beta, x, e1, e2) ->
      let e1 = of_term' k l e1
      and e2 = of_term' k (l+1) e2
      in
        begin match e1, e2 with
          | Term e1, Term e2 -> Term (Syntax.NameProd (alpha, beta, x, e1, e2), loc)
          | _ -> NameProd (alpha, beta, x, e1, e2)
        end

    | Syntax.NameUniverse _ ->
      Term e

    | Syntax.NamePaths (alpha, e1, e2, e3) ->
      let e1 = of_term' k l e1
      and e2 = of_term' k l e2
      and e3 = of_term' k l e3
      in
        begin match e1, e2, e3 with
          | Term e1, Term e2, Term e3 -> Term (Syntax.NamePaths (alpha, e1, e2, e3), loc)
          | _ -> NamePaths (alpha, e1, e2, e3)
        end

    | Syntax.NameId (alpha, e1, e2, e3) ->
      let e1 = of_term' k l e1
      and e2 = of_term' k l e2
      and e3 = of_term' k l e3
      in
        begin match e1, e2, e3 with
          | Term e1, Term e2, Term e3 -> Term (Syntax.NameId (alpha, e1, e2, e3), loc)
          | _ -> NameId (alpha, e1, e2, e3)
        end

let of_term k e = of_term' k 0 e

let of_ty k t = of_ty' k 0 t

(** Substitute terms for pattern variables in the given pattern, coalescing resulting
    types and terms that are free of pattern variables. *)
let rec subst_ty inst k = function

  | Ty _ as t -> t

  | El (alpha, e) ->
    let e = subst_term inst k e in
      begin match e with
        | Term e -> Ty (Syntax.El (alpha, e), Position.nowhere)
        | _ -> El (alpha, e)
      end

  | Prod (x, t1, t2) ->
    let t1 = subst_ty inst k t1
    and t2 = subst_ty inst (k+1) t2
    in
      begin match t1, t2 with
        | Ty t1, Ty t2 -> Ty (Syntax.Prod (x, t1, t2), Position.nowhere)
        | _ -> Prod (x, t1, t2)
      end

  | Paths (t, e1, e2) ->
    let t = subst_ty inst k t
    and e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    in
      begin match t, e1, e2 with
        | Ty t, Term e1, Term e2 -> Ty (Syntax.Paths (t, e1, e2), Position.nowhere)
        | _ -> Paths (t, e1, e2)
      end

  | Id (t, e1, e2) ->
    let t = subst_ty inst k t
    and e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    in
      begin match t, e1, e2 with
        | Ty t, Term e1, Term e2 -> Ty (Syntax.Id (t, e1, e2), Position.nowhere)
        | _ -> Id (t, e1, e2)
      end

and subst_term inst k = function
  | Term _ as pe -> pe

  | (PVar i) as pe ->
    begin try
      let e = List.assoc i inst in
      let e = Syntax.shift k e in
        Term e
      with
        | Not_found -> pe
    end

  | Lambda (x, t1, t2, e) ->
    let t1 = subst_ty inst k t1
    and t2 = subst_ty inst (k+1) t2
    and e = subst_term inst (k+1) e
    in
      begin match t1, t2, e with
        | Ty t1, Ty t2, Term e -> Term (Syntax.Lambda (x, t1, t2, e), Position.nowhere)
        | _ -> Lambda (x, t1, t2, e)
      end

  | App ((x, t1, t2), e1, e2) ->
    let t1 = subst_ty inst k t1
    and t2 = subst_ty inst (k+1) t2
    and e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    in
      begin match t1, t2, e1, e2 with
        | Ty t1, Ty t2, Term e1, Term e2 ->
          Term (Syntax.App ((x, t1, t2), e1, e2), Position.nowhere)
        | _ -> App ((x, t1, t2), e1, e2)
      end

  | Idpath (t, e) ->
    let t = subst_ty inst k t
    and e = subst_term inst k e
    in
      begin match t, e with
        | Ty t, Term e -> Term (Syntax.Idpath (t, e), Position.nowhere)
        | _ -> Idpath (t, e)
      end

  | J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
    let t = subst_ty inst k t
    and u = subst_ty inst (k+3) u
    and e1 = subst_term inst (k+1) e1
    and e2 = subst_term inst k e2
    and e3 = subst_term inst k e3
    and e4 = subst_term inst k e4
    in
      begin match t, u, e1, e2, e3, e4 with
        | Ty t, Ty u, Term e1, Term e2, Term e3, Term e4 ->
          Term (Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4), Position.nowhere)
        | _ -> J (t, (x, y, p, u), (z, e1), e2, e3, e4)
      end

  | Refl (t, e) ->
    let t = subst_ty inst k t
    and e = subst_term inst k e
    in
      begin match t, e with
        | Ty t, Term e -> Term (Syntax.Refl (t, e), Position.nowhere)
        | _ -> Refl (t, e)
      end

  | Coerce (alpha, beta, e) ->
    let e = subst_term inst k e
    in
      begin match e with
        | Term e -> Term (Syntax.Coerce (alpha, beta, e), Position.nowhere)
        | _ -> Coerce (alpha, beta, e)
      end

  | NameProd (alpha, beta, x, e1, e2) ->
    let e1 = subst_term inst k e1
    and e2 = subst_term inst (k+1) e2
    in
      begin match e1, e2 with
        | Term e1, Term e2 ->
          Term (Syntax.NameProd (alpha, beta, x, e1, e2), Position.nowhere)
        | _ -> NameProd (alpha, beta, x, e1, e2)
      end

  | NamePaths (alpha, e1, e2, e3) ->
    let e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    and e3 = subst_term inst k e3
    in
      begin match e1, e2, e3 with
        | Term e1, Term e2, Term e3 ->
          Term (Syntax.NamePaths (alpha, e1, e2, e3), Position.nowhere)
        | _ -> NamePaths (alpha, e1, e2, e3)
      end

  | NameId (alpha, e1, e2, e3) ->
    let e1 = subst_term inst k e1
    and e2 = subst_term inst k e2
    and e3 = subst_term inst k e3
    in
      begin match e1, e2, e3 with
        | Term e1, Term e2, Term e3 ->
          Term (Syntax.NameId (alpha, e1, e2, e3), Position.nowhere)
        | _ -> NameId (alpha, e1, e2, e3)
      end

let rec shift_ty k l = function

  | Ty t -> Ty (Syntax.shift_ty ~bound:l k t)

  | El (alpha, e) ->
    let e = shift k l e in
      El (alpha, e)

  | Prod (x, t1, t2) ->
    let t1 = shift_ty k l t1
    and t2 = shift_ty k (l+1) t2
    in
      Prod (x, t1, t2)

  | Paths (t, e1, e2) ->
    let t = shift_ty k l t
    and e1 = shift k l e1
    and e2 = shift k l e2
    in
      Paths (t, e1, e2)

  | Id (t, e1, e2) ->
    let t = shift_ty k l t
    and e1 = shift k l e1
    and e2 = shift k l e2
    in
      Id (t, e1, e2)

and shift k l = function

  | Term e ->
    let e = Syntax.shift ~bound:l k e
    in
      Term e

  | PVar i ->
    PVar i

  | Lambda (x, t1, t2, e) ->
    let t1 = shift_ty k l t1
    and t2 = shift_ty k (l+1) t2
    and e = shift k l e
    in
      Lambda (x, t1, t2, e)

  | App ((x, t1, t2), e1, e2) ->
    let t1 = shift_ty k l t1
    and t2 = shift_ty k (l+1) t2
    and e1 = shift k l e1
    and e2 = shift k l e2
    in
      App ((x, t1, t2), e1, e2)

  | Idpath (t, e) ->
    let t = shift_ty k l t
    and e = shift k l e
    in
      Idpath (t, e)

  | J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
    let t = shift_ty k l t
    and u = shift_ty k (l+3) u
    and e1 = shift k (l+1) e1
    and e2 = shift k l e2
    and e3 = shift k l e3
    and e4 = shift k l e4
    in
      J (t, (x, y, p, u), (z, e1), e2, e3, e4)

  | Refl (t, e) ->
    let t = shift_ty k l t
    and e = shift k l e
    in
      Refl (t, e)

  | Coerce (alpha, beta, e) ->
    let e = shift k l e
    in
      Coerce (alpha, beta, e)

  | NameProd (alpha, beta, x, e1, e2) ->
    let e1 = shift k l e1
    and e2 = shift k (l+1) e2
    in
      NameProd (alpha, beta, x, e1, e2)

  | NamePaths (alpha, e1, e2, e3) ->
    let e1 = shift k l e1
    and e2 = shift k l e2
    and e3 = shift k l e3
    in
      NamePaths (alpha, e1, e2, e3)

  | NameId (alpha, e1, e2, e3) ->
    let e1 = shift k l e1
    and e2 = shift k l e2
    and e3 = shift k l e3
    in
      NameId (alpha, e1, e2, e3)


(**********)
(* Spines *)
(**********)

(** The [NoSpine] is raised when we cannot convert a term or a term pattern to a spine
 *)
exception NoSpine

(* A [spine] consists of a head followed by a series of applications.
 * Each application includes the Pi type where the application is occuring,
 * as in the magenta annotation in Syntax.App.
 *
 * We parameterize the type so that we can talk about spints where the
 * parameters involve Syntax terms and types, or Pattern terms and types.
 *)
type ('y,'r) spine = head * ((name * 'y * 'y) * 'r) list

(* The head of a spine never involves pattern variables.
 *)
and head =
  | HVar of int   (* Brazil variable, not a pattern variable! *)
  | HNameProd of Universe.t * Universe.t
  | HNamePaths of Universe.t
  | HNameId of Universe.t
  | HNameUniverse of Universe.t
  | HCoerce of Universe.t * Universe.t
  | HRefl of Syntax.ty
  | HIdpath of Syntax.ty
  | HUnitTerm
  | HNameUnit

(* Compares two heads for equality.
 *
 * Syntax.ty parameters [which by definition contain no pattern variables] are
 * compared using the [eqTy] parameter.
 *)
let eq_head eqTy head1 head2 =
  match head1, head2 with
  | HVar n, HVar n' -> n = n'

  | HNameProd(alpha, beta), HNameProd(alpha',beta')
  | HCoerce(alpha, beta), HCoerce(alpha',beta') ->
      Universe.eq alpha alpha' && Universe.eq beta beta'

  | HNamePaths alpha, HNamePaths alpha'
  | HNameId alpha, HNameId alpha'
  | HNameUniverse alpha, HNameUniverse alpha' ->
      Universe.eq alpha alpha'

  | HRefl t, HRefl t'
  | HIdpath t, HIdpath t' -> eqTy t t'

  | HUnitTerm, HUnitTerm
  | HNameUnit, HNameUnit -> true

  | (HVar _ | HNameProd _ | HNamePaths _ | HNameId _
      | HCoerce _ | HRefl _ | HIdpath _
      | HUnitTerm | HNameUniverse _ | HNameUnit ), _ -> false


(* Helper functions for conversion of [Syntax.term]s to spines.
 *
 * We use the same functions to convert to terms to term spines
 * and patterns to pattern spines.
 *
 * We assume that input type are always [Syntax.ty] form (with no pattern
 * variables), but that other inputs are terms or term patterns as appropriate.
 * So, we take a wrapper function doTy that converts types to type patterns
 * (if we're processing a pattern) or that leaves types unchanged (if we're
 * processing a term).
 *
 * For generality, we permit a wrapper function for the non-type arguments,
 * but so far it's always the identity function in practice.
 *)

(* Given wrapper functions [doTy] and [doTerm] as described above,
 * a type [t], and a term/pattern p, construct the appropriate IdPath spine.
 *
 * The [HIdpath t] head can be viewed as having type
 *    ( x : t ) -> Paths(t,x,x)
 *)
let spine_of_idpath doTy doTerm t p =
    HIdpath t,
    [ ( "idpath-arg",
        doTy t,
        doTy (Syntax.mkPaths (Syntax.weaken_ty 0 t) (Syntax.mkVar 0) (Syntax.mkVar 0)) ),
      doTerm p]

(* Given wrapper functions [doTy] and [doTerm] as described above,
 * a type [t], and a term/pattern p, construct the appropriate Refl spine.
 *
 * The [HRefl t] head can be viewed as having type
 *    ( x : t ) -> Id(t,x,x)
 *)
let spine_of_refl doTy doTerm t p =
    HRefl t,
    [ ( "refl-arg",
        doTy t,
        doTy (Syntax.mkId (Syntax.weaken_ty 0 t) (Syntax.mkVar 0) (Syntax.mkVar 0)) ),
      doTerm p]
(* Given wrapper functions [doTy] and [doTerm] as described above,
 * universes [alpha] and [beta] and a term/pattern p, construct the appropriate
 * [Coerce] spine.
 *
 * The [HCoerce (alpha,beta)] head can be viewed as having type
 *    Universe alpha -> Universe beta
 *)
let spine_of_coerce doTy doTerm alpha beta p =
    HCoerce (alpha, beta),
    [("_", doTy (Syntax.mkUniverse alpha), doTy (Syntax.mkUniverse beta)), doTerm p]


(* Factored out because spine_of_idpath and spine_of_namepaths were
 * nearly identical. They take the same arguments; the only difference
 * is the head, [HNameId alpha] or [HNamePaths alpha].
 *
 * In either case the head has type
 *    (x : Universe alpha) -> El[alpha](x) -> El[alpha](x) -> Universe alpha
 * and we annotate the applications below accordingly.
 *)
let spine_of_pathlike head doTy doTerm alpha e1 e2 e3 =
  let u_alpha = Syntax.mkUniverse alpha  in
  let el_v0 = Syntax.mkEl alpha (Syntax.mkVar 0)  in
  let el_v1 = Syntax.mkEl alpha (Syntax.mkVar 1)  in

  head,
  [ ( "nameid-arg", doTy u_alpha, doTy (Syntax.make_arrow el_v0 (Syntax.make_arrow el_v0 u_alpha)) ),
    doTerm e1;

   ( "_", doTy el_v0, doTy (Syntax.make_arrow el_v1 u_alpha) ),  (* We're in the scope of "_" var, so shift 0->1 *)
   doTerm e2;

   ( "_", doTy el_v1, doTy u_alpha ),
   doTerm e3;
  ]

let spine_of_nameid doTy doTerm alpha e1 e2 e3 =
  spine_of_pathlike (HNameId alpha) doTy doTerm alpha e1 e2 e3

let spine_of_namepaths doTy doTerm alpha e1 e2 e3 =
  spine_of_pathlike (HNamePaths alpha) doTy doTerm alpha e1 e2 e3


(* [spine_of_syntax] converts a [Syntax.term] into either a pattern spine or a
 * term spine, as desired. The difference is determined by the wrapper
 * functions [doTy] and [doTerm], that either coerce Syntax types and terms
 * into Patterns, or else act as identity functions.
 *)
let rec spine_of_syntax doTy doTerm term =
  let recur = spine_of_syntax doTy doTerm in
  match fst term with
  | Syntax.Var v ->
      HVar v, []

  | Syntax.App ((x,t1,t2), e1, e2) ->
        let (h, args) = recur e1  in
        h, (args @ [(x,doTy t1,doTy t2), doTerm e2])

  | Syntax.Coerce(alpha, beta, e) -> spine_of_coerce doTy doTerm alpha beta e

  | Syntax.UnitTerm -> HUnitTerm, []

  | Syntax.Idpath(t, p) -> spine_of_idpath doTy doTerm t p

  | Syntax.Refl(t, p) -> spine_of_refl doTy doTerm t p

  | Syntax.NameId(alpha, e1, e2, e3) -> spine_of_nameid doTy doTerm alpha e1 e2 e3

  | Syntax.NamePaths(alpha, e1, e2, e3) -> spine_of_namepaths doTy doTerm alpha e1 e2 e3

  | Syntax.NameUniverse alpha -> HNameUniverse alpha, []

  | Syntax.NameUnit -> HNameUnit, []

  | Syntax.NameProd (_alpha, _beta, _x, _e1, _e2) ->
      (* XXX We don't try to handle matches against nameProds *)
      raise NoSpine

  | Syntax.Lambda _ ->
      (* XXX We don't try to handle matches against lambdas *)
      raise NoSpine

  | Syntax.Equation (_, _, e)
  | Syntax.Rewrite (_, _, e)
  | Syntax.Ascribe (e, _) ->
      recur e

  | Syntax.J _ ->
      (* XXX We don't try to handle matches against J *)
      raise NoSpine

let id x = x

(* [spine_of_term] converts a *pattern* term into a pattern spine.
 * We assume that the "head" of the input pattern is not a pattern variable.
 *)
let rec spine_of_term =
  let wrapTy t = Ty t  in
  let wrapTerm e = Term e  in
  let warn s = Print.warning "spine_of_term: %s" s  in
  function
  | Term e -> spine_of_syntax wrapTy wrapTerm e

  | PVar i ->
      (* We should have handled this separately. *)
      Error.impossible "spine_of_term: top-level pattern variable cannot be a spine"

  | App ((x,t1,t2), p1, p2) ->
        let (h, args) = spine_of_term p1  in
        h, (args @ [(x,t1,t2), p2])

  | Idpath(typat, p) ->
      begin
        match typat with
        | Ty t -> spine_of_idpath wrapTy id t p
        | _ -> warn "can't handle type patterns in top-level Idpath; skipping";
               raise NoSpine
      end

  | J _ ->
      begin
        warn "We don't currently handle patterns with top-level J";
        raise NoSpine
      end

  | Refl(typat, p) ->
      begin
        match typat with
        | Ty t -> spine_of_refl wrapTy id t p
        | _ -> warn "can't handle type patterns in top-level Refl; skipping";
               raise NoSpine
      end

  | Coerce(alpha, beta, p) -> spine_of_coerce wrapTy id alpha beta p

  | NameId(alpha, p1, p2, p3) -> spine_of_nameid wrapTy id alpha p1 p2 p3

  | NamePaths(alpha, p1, p2, p3) -> spine_of_namepaths wrapTy id alpha p1 p2 p3

  | NameProd _ ->
      begin
        warn "we don't currently handle patterns with top-level NameProd";
        raise NoSpine
      end


  | Lambda _ ->
      begin
        warn "we don't currently handle patterns with top-level Lambda";
        raise NoSpine
      end


(* [spine_of_brazil] converts a *Brazil* term into a term spine.
 *)
let spine_of_brazil  = spine_of_syntax id id


(* Apply a pattern-variable substitution to the argument list in a pattern
 * spine.
 *
 * [bvs] is the initial count of bound variables (how much to shift the
 * instantiation), but due to the flat nature of spines it's probably
 * always zero in practice.
 *)

let subst_pattern_args inst bvs =
  List.map
    (fun ((x,t1,t2),e) ->
      ((x, subst_ty inst bvs t1,
           subst_ty inst (bvs+1) t2),
           subst_term inst bvs e))

