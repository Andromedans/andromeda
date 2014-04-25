(** Abstract syntax of internal expressions. *)

(** Abstract syntax of expressions, where de Bruijn indices are used to represent
    variables. *)
type term =
  | Var    of int
  | Lambda of Common.variable * term * term * term  (* Pi type + body *)
  | Pi     of Common.variable * term * term
  | App    of term * term
  | Sigma  of Common.variable * term * term
  | Pair   of term * term * Common.variable * term * term
         (* pack e1, e2 at Sigma x : t1. t2 *)
  | Proj   of int * term                   (* 1 = fst, 2 = snd *)
  | Refl   of eqsort * term * term
  | Eq     of eqsort * term * term * term
  | Ind_eq of eqsort * term * (Common.variable * Common.variable * Common.variable * term) *
                              (Common.variable * term) * term * term * term
  | U      of universe
  | Base   of basetype
  | Const  of constant
  | Handle of term * term list
  | MetavarApp of metavarapp

and universe = Input.universe =
  | NonFib of int
  | Fib of int

and eqsort = Input.eqsort =
  | Ju
  | Pr

and basetype =
  | TUnit

and constant =
  | Unit

and metavarapp = { mv_def  : term option ref;
                   mv_args : term list;
                   mv_ty   : term;
                   mv_loc  : Common.position;
                   mv_sort : metavar_sort;
                 }

and metavar_sort =
  | MV_wildcard
  | MV_admit


(**************************************
   The Typing Rules. In all cases, the prior well-formedness of G is assumed


   -----------------
   G |- x : G(x)


   G |- t : U(u,i)   G, x:t |- e : t'
   ---------------------------------------
   G |- Lambda(x, t, t', e) : Pi(x, t, t')


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
   -------------------------------------------
   G |- <e', e'', x, t', t''> :  Sigma(x, t', t'')


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


   G |- t : U(u,i)
   G , x:t, y:t, z:Id(o,x,y,t) |- c(x,y,z) : U(u, j)    [ i & j independent? ]
   G , z:t |- w(z) : c z z (refl(o, z, t))
   G |- a : t    G |- b : t    G |- q : Id(o, a, b, t)
   if o = Pr then u = Fib
   ----------------------------------------------------
   G |- Ind_eq(o, t, (_,_,_,c), (_,w), a, b, q) : c a b q

        NB: at the TT level it's just  G |- Ind_eq(o, (_,_,_,c), (_,w), q) : c a b q


   -----------------
   G |- Unit : TUnit


   G |- e : t
   G |- t : U(u,i)   G |- u : U(u,i)   G |- t == u : U(u,i)
   --------------------------------------------------------
   G |- e : u


   G |- e : U(Fib, i)
   -------------------      [ An explicit coercion here seems painful ]
   G |- e : U(NonFib, i)


   G |- e : U(u, i)
   ------------------       [ Or do we want the explicit coercion? ]
   G |- e : U(u, i+1)

*)

module TermSet = Set.Make(struct
                             type t = term
                             let compare = compare
                          end)

(** [universe_classifier u] returns the universe classifying the given
 *  universe [u] *)
let universe_classifier = function
  | Fib i    -> Fib (i+1)
  | NonFib i -> Fib (i+1)   (* Surprise! *)


(* Careful! Just because
     NonFib(i) : Fib(i+1)
   does *not* mean that every type in NonFib(i) is also in Fib(i+1).
 *)

(** [universe_join u1 u2] returns the (least) universe that includes
    all the memebers of [u1] and all the members of [u2]
*)
let universe_join u1 u2 =
  match u1, u2 with
  | Fib    i, NonFib j
  | NonFib i, Fib    j
  | NonFib i, NonFib j -> NonFib (max i j)
  | Fib    i, Fib    j -> Fib (max i j)

(** Is every value of type [u1] also a value of [u2] ? *)
let universe_le u1 u2 =
  match u1, u2 with
  | Fib    i, Fib    j
  | Fib    i, NonFib j
  | NonFib i, NonFib j  ->  i <= j
  | NonFib _, Fib    _  ->  false



(** [string_of_term term] creates an accurate but not-very-pretty textual
 * representation of the [term] datatype value.
*)
let rec string_of_term ?(show_meta=false) = function
  | Var i          -> "var[" ^ string_of_int i ^ "]"
  | Lambda(x,t1,t2,e)  -> "Lambda(" ^ x ^ "," ^ string_of_terms ~show_meta [t1;t2;e] ^ ")"
  | Pi(x,t1,t2)    -> "Pi(" ^ x ^ "," ^ string_of_terms ~show_meta [t1;t2] ^ ")"
  | App(e1,e2)     -> "App(" ^ string_of_terms ~show_meta [e1;e2] ^ ")"
  | Sigma(x,t1,t2) -> "Sigma(" ^ x ^ "," ^ string_of_terms ~show_meta [t1;t2] ^ ")"
  | Pair(e1,e2,x,t1,t2)  -> "Pair(" ^ string_of_terms ~show_meta [e1;e2] ^ ","
                               ^ x ^ string_of_terms ~show_meta [t1;t2] ^ ")"
  | Proj(i1,e2)    -> "Proj(" ^ string_of_int i1 ^ ","
                         ^ string_of_term ~show_meta e2 ^ ")"
  | Refl(o,e,t)    -> "Refl("  ^ string_of_eqsort o ^ ","
                         ^ string_of_terms ~show_meta [e;t] ^ ")"
  | Eq(o,e1,e2,t)  -> "Eq(" ^ string_of_eqsort o ^ ","
                         ^ string_of_terms ~show_meta [e1;e2;t] ^ ")"
  | Ind_eq(o,t,(x,y,p,c),(z,w),a,b,q) ->
      "J(" ^ string_of_eqsort o ^ ","
        ^ string_of_term ~show_meta t ^  ", ("
        ^ String.concat "," [x;y;p] ^ ","
        ^ string_of_term ~show_meta c ^ "), ("
        ^ z ^ "," ^ string_of_term ~show_meta w ^ "), "
        ^ string_of_terms ~show_meta [a;b;q] ^ ")"
  | Handle(e,es)   -> "Handle(" ^ string_of_terms ~show_meta (e::es) ^ ")"
  | U univ  -> "U(" ^ string_of_universe univ ^ ")"
  | Base b  -> string_of_basetype b
  | Const c -> string_of_constant c
  | MetavarApp mva -> string_of_mva ~show_meta mva

(* comma-separated terms *)
and string_of_terms ?(show_meta=false) ts =
  String.concat "," (List.map (string_of_term ~show_meta) ts)

and string_of_eqsort = function
  | Ju -> "Ju"
  | Pr -> "Pr"

and string_of_universe = function
  | NonFib i -> "QuasiType " ^ string_of_int i
  | Fib i  -> "Type " ^ string_of_int i

and string_of_basetype = function
  | TUnit -> "TUnit"

and string_of_constant = function
  | Unit -> "Unit"

(** [shift cut delta] shifts the indices by [delta] with a cutoff of [cut]. *)
(* See, e.g., http://ecee.colorado.edu/~siek/ecen5013/spring10/lecture4.pdf
   The rule is: increase cut by one for each binder.
*)
and rewrite_vars ?(cut=0) ftrans =
  let rec loop cut = function
    | (U _ | Base _ | Const _) as term -> term
    | Var m -> ftrans cut m
    | Lambda (x, t1, t2, e)  -> Lambda (x, loop cut t1,
                                        loop (cut+1) t2, loop (cut+1) e)
    | App (e1, e2)      -> App(loop cut e1, loop cut e2)
    | Pi (x, t1, t2)    -> Pi(x, loop cut t1, loop (cut+1) t2)
    | Sigma (x, t1, t2) -> Sigma(x, loop cut t1, loop (cut+1) t2)
    | Pair (e1, e2, x, ty1, ty2) -> Pair(loop cut e1, loop cut e2, x,
                                         loop cut ty1, loop (cut+1) ty2)
    | Proj (i1, e2)     -> Proj(i1, loop cut e2)
    | Refl (o, e, t)    -> Refl(o, loop cut e, loop cut t)
    | Eq (o, e1, e2, t) -> Eq(o, loop cut e1, loop cut e2, loop cut t)
    | Ind_eq (o, t, (x,y,p,c), (z,w), a, b, q)
                        -> Ind_eq(o, loop cut t,
                                  (x,y,p,loop (cut+3) c),
                                  (z, loop (cut+1) w),
                                  loop cut a, loop cut b, loop cut q)
    | Handle (e, es)    -> Handle(loop cut e, List.map (loop cut) es)
    | MetavarApp mva
         -> MetavarApp { mv_def  = mva.mv_def;
                         mv_args = List.map (loop cut) mva.mv_args;
                         mv_ty   = loop cut mva.mv_ty;
                         mv_loc  = mva.mv_loc;
                         mv_sort = mva.mv_sort;
                       }  in
  loop cut

and shift ?(cut=0) delta =
  rewrite_vars ~cut (fun c m -> if (m < c) then
                                  Var m
                              else
                                  ( assert (m+delta >= 0);
                                    Var(m+delta) ) )

(** [subst j e' e] replaces the free occurrences of variable [j] in [e] by [e'].  *)
(* The rule is: shift the substituted expression e' by one for each binder
*)

and subst j e' =
  rewrite_vars (fun c m -> if (m = j + c) then
                             shift c e'
                           else
                             Var m)


(** [beta body arg] substitutes [arg] in for variable [0] in [body].

  So, if [G, x:t |- body : ...] and [G |- arg : t] then
  [beta body arg] is the term [body[x->arg]].

  This is exactly the substitution required, for example, to
  beta-reduce a function application ([body] is the body of the lambda),
  or to substitute away the parameter in a [Pi] or [Sigma] type ([body] is
  the type of the codomain or second component, respectively).
*)
and beta eBody eArg =
  (*let _ = Format.printf "beta: eBody = %s, eArg = %s@."*)
               (*(string_of_term eBody) (string_of_term eArg)  in*)
  let answer = shift (-1) (subst 0 (shift 1 eArg) eBody)  in
  (*let _ = Format.printf "      answer = %s@." (string_of_term answer)  in*)
  answer

and make_arrow dom cod =
  Pi("_", dom, shift 1 cod)

and make_star fst snd =
  Pi("_", fst, shift 1 snd)

(**
  Suppose we have [G, x_1:t_1, ..., x_n:t_n |- exp : ...] and the inhabitants
  [e_1; ...; e_n] all well-formed in [G] (!) with types [t_1] through [t_n]
  respectively. Then [strengthen exp [e_1,...,e_n]] is the result of
  substituting away the x_i's, resulting in a term well-formed in [G].

  In particular, [strengthen env eBody [eArg]] is just [beta eBody
 *)
and strengthen exp inhabitants =
  let rec loop n accum = function
    | [] ->
        begin
          assert (n = 0);
          accum
        end
    | inhabitant :: inhabitants ->
        begin
          let accum' = beta accum (shift (n-1) inhabitant)  in
          loop (n-1) accum' inhabitants
        end  in
  loop (List.length inhabitants) exp (List.rev inhabitants)

(** If [G |- exp] then [G' |- weaken i exp] where [G'] has an extra (unused)
     variable inserted at position [i]. This is just a simple renumbering, with
     all free variables [< i] unchanged, and all [>= i] incremented (because
     there's a new variable in front of them). *)
and weaken new_var_pos exp =
  shift ~cut:new_var_pos 1 exp

  (** [shift_to_depth (k,exp) l] moves the expression [exp] from a context
      with depth [k] to a context of depth [l >= k].

      Equivalently, weaken with [l - k] new variables at the end of the
      context. *)
and shift_to_depth (old_depth, exp) new_depth =
  assert (new_depth >= old_depth);
  shift (new_depth - old_depth) exp

and apply_list eFn eArgs =
  match eFn, eArgs with
  | _, [] -> eFn
  | Lambda(_, _, _, eBody), eArg :: eArgs -> apply_list (beta eBody eArg) eArgs
  | _, eArg :: eArgs -> apply_list (App (eFn, eArg)) eArgs

and fresh_mva context_length ty loc sort =
  let rec loop = function
    | 0 -> []
    | n -> Var (n-1) :: loop (n-1) in
  { mv_def = ref None;
    mv_args = loop context_length;
    mv_ty = ty;
    mv_loc = loc;
    mv_sort = sort;
  }

and derived_mva mva =
  { mv_def  = ref None;
    mv_args = mva.mv_args;
    mv_ty   = mva.mv_ty;
    mv_loc  = mva.mv_loc;
    mv_sort = mva.mv_sort;
  }


and get_mva {mv_def = r; mv_args = args} =
  match !r with
  | None -> None
  | Some body ->
      let lambda_wrapped_body =
           (* XXX: Not TUnit! *)
          List.fold_right (fun _ b -> Lambda ("???", Base TUnit, Base TUnit, b)) args body  in
      Some (apply_list lambda_wrapped_body args)

    and string_of_mva ?(show_meta=false) ({mv_def; mv_args; mv_loc} as mva) =
  (*let base_string = "M-" ^ (Printf.sprintf "%x" (Obj.magic mv_def : int)) in*)
  let base_string = "M-" ^ (Common.string_of_position mv_loc) in
  match get_mva mva with
  | Some defn ->
      if show_meta then
        "{{" ^ base_string ^ " = " ^ string_of_term ~show_meta defn ^ "}}"
      else
        string_of_term ~show_meta defn
  | None -> "{{" ^ base_string ^ "}}[" ^
                    String.concat "," (List.map string_of_term mv_args) ^ "]"

(* This function does **not** check reasonableness, or make sure
 * it's referring to the right parameters. *)
and set_mva mva body =
  match ! (mva.mv_def) with
  | None -> mva.mv_def := Some body
  | Some _ -> Error.fatal "Re-setting metavariable %s" (string_of_mva mva)

let mva_is_set mva =
  match ! (mva.mv_def) with
  | None   -> false
  | Some _ -> true

let get_mva_sort {mv_sort} = mv_sort
let get_mva_pos {mv_loc} = mv_loc
let get_mva_ty {mv_ty} = mv_ty

(** [occurs v e] returns [true] when variable [Var v] occurs freely in [e]. *)
(* The rule is: increase the variable number by one (shift it)
   whenever we enter a binder *)
let rec occurs v e =
  match e with
  | Var m -> m = v

  | Lambda (_, t1, t2, e)  -> occurs v t1  || occurs (v+1) t2 || occurs (v+1) e
  | App (e1, e2)           -> occurs v e1 || occurs v e2
  | Pair (e1, e2, x, ty1, ty2) -> occurs v e1 || occurs v e2
                                    || occurs v ty1 || occurs (v+1) ty2
  | Proj (_, e2)           -> occurs v e2
  | Refl (_, e, t)         -> occurs v e  || occurs v t
  | Pi (_, t1, t2)         -> occurs v t1 || occurs (v+1) t2
  | Sigma (_, t1, t2)      -> occurs v t1 || occurs (v+1) t2
  | Eq (_, e1, e2, t)      -> occurs v e1 || occurs v e2 || occurs v t
  | Ind_eq(_, t, (_,_,_,c), (_,w), a, b, p)
                           -> occurs v t || occurs (v+3) c || occurs (v+1) w
                               || occurs v a || occurs v b || occurs v p
  | Handle (e, es)        -> occurs v e || List.exists (occurs v) es

  | MetavarApp mva ->
      begin
        match get_mva mva with
        | None      -> List.exists (occurs v) mva.mv_args
        | Some defn -> occurs v defn
      end

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

  | Pi(_, t11, t12), Pi(_, t21, t22)
  | Sigma(_, t11, t12), Sigma(_, t21, t22)
  | App(t11, t12), App(t21, t22) ->
      equal t11 t21 && equal t12 t22

  | Lambda(_, t11, t12, t13), Lambda(_, t21, t22, t23) ->
      equal t11 t21 && equal t12 t22 && equal t13 t23

  | Pair(e11, e12, _, ty11, ty12), Pair(e21, e22, _, ty21, ty22) ->
      equal e11 e21 && equal e12 e22
       && equal ty11 ty21 && equal ty12 ty22

  | Proj(i1, t1), Proj(i2, t2) ->
      i1 = i2 && equal t1 t2

  | Refl(o1, t11, t12), Refl(o2, t21, t22) ->
      o1 = o2 && equal t11 t21 && equal t12 t22

  | Eq(o1, t11, t12, t13), Eq(o2, t21, t22, t23) ->
      o1 = o2 && equal t11 t21 && equal t12 t22 && equal t13 t23

  | Ind_eq(o1, t11, (_,_,_,t12), (_,t13), t14, t15, t16),
    Ind_eq(o2, t21, (_,_,_,t22), (_,t23), t24, t25, t26) ->
      o1 = o2 && equal t11 t21 && equal t12 t22 && equal t13 t23
      && equal t14 t24 && equal t15 t25 && equal t16 t26

    (* XXX: We ignore handlers w.r.t. alpha equivalence, because they
     * don't "really" exist in the term! *)
  | Handle(e1', _), _ -> equal e1' e2
  | _, Handle(e2', _) -> equal e1 e2'

  | MetavarApp mva, _   when mva_is_set mva ->
      begin
        match get_mva mva with
        | None -> Error.fatal "impossible. mva is set but empty"
        | Some defn -> equal defn e2
      end

  | _, MetavarApp mva   when mva_is_set mva ->
      begin
        match get_mva mva with
        | None -> Error.fatal "impossible. mva is set but empty"
        | Some defn -> equal e1 defn
      end

  | MetavarApp mva1, MetavarApp mva2 ->
      (* If we got this far, then both are unset *)
      List.for_all2 equal mva1.mv_args mva2.mv_args

  | (Var _ | Lambda _ | Pi _ | App _ | Sigma _ | Pair _ | Proj _
      | Refl _ | Eq _ | Ind_eq _ | U _ | Base _ | Const _ | MetavarApp _ ), _ -> false

    module VS = Set.Make(struct
                            type t = Common.debruijn
                            let compare = compare
                         end)

    module VM = Map.Make(struct
                            type t = Common.debruijn
                            let compare = compare
                         end)

  let union_list = List.fold_left VS.union VS.empty

  let rec free_vars =
    let rec loop cut = function
    | Var m -> if (m < cut) then VS.empty else VS.singleton (m - cut)
    | App (e1, e2)      -> VS.union (loop cut e1) (loop cut e2)
    | Pi (_, t1, t2)    -> VS.union (loop cut t1) (loop (cut+1) t2)
    | Sigma (_, t1, t2) -> VS.union (loop cut t1) (loop (cut+1) t2)
    | Pair (e1, e2, _, ty1, ty2)
                        -> union_list
                               [loop cut e1; loop cut e2;
                                loop cut ty1; loop (cut+1) ty2]
    | Proj (i1, e2)     -> loop cut e2
    | Lambda (_, t1, t2, e) -> union_list
                                  [loop cut t1; loop (cut+1) t2; loop (cut+1) e]
    | Refl (_, e, t)    -> VS.union (loop cut e) (loop cut t)
    | Eq (_, e1, e2, t) -> union_list
                               [loop cut e1; loop cut e2; loop cut t]
    | Ind_eq (o, t, (x,y,p,c), (z,w), a, b, q)
                        -> union_list
                               [loop cut t; loop (cut+3) c; loop (cut+1) w;
                                loop cut a; loop cut b; loop cut q]
    | Handle (e, es)    -> union_list
                               ((loop cut e) :: List.map (loop cut) es)
    | (U _ | Base _ | Const _) -> VS.empty
    | MetavarApp mva ->
        begin
          match get_mva mva with
          | Some defn -> loop cut defn
          | None      -> union_list (List.map (loop cut) mva.mv_args)
        end  in
  loop 0



(*****************)

let create_ind_eq_envs add_parameters env o t (x,y,p) z =
  let env_xyp =
        (* Unfortunately, add_parameters only works when there are
           no dependencies between the variables, so we have to
           do it in two stages. First we add x and y.
         *)
        let env_xy =
              add_parameters [ (x, t); (y, t) ] env in
        (* Then add p, with a type indexed relative to tmp_env
         *)
        let xvar = Var 1  in
        let yvar = Var 0  in
        let t'   = shift 2 t  (* (env,x,y) - env = 2 *)  in
        add_parameters [ p, Eq(o, xvar, yvar, t') ] env_xy  in

  let env_z = add_parameters [z, t] env in

  (env_xyp, env_z)

let create_ind_eq_types env_xyp env_z o t (x,y,p,c) z a b q =

  (* [term2] will be our [w] input. We expect that
           [env, z:t |- w : c[x,y,p->z,z,refl z]],
     so we construct the type
           [env, z:t |- c[x,y,p->z,z,refl z]].
     We produce this type by weakening c into [env, z, x, y, p |- c']
     and construct the desired substitution instance of
     using strengthening.
   *)
  let w_ty_expected =

    (* [c] has indices relative to the context [env, x, y, p]
       but when working with [w] it would be more helpful to
       use the context [env, z, x, y, p] with z in position 3.
       We can adjust the indices to get a term [c'] by using weakening.
    *)
    let c' = weaken 3 c in

    (* We shift [env |- t] to get [env, z:t |- t']. *)
    let t' = shift 1 t in  (* (env,z) - env = 1 *)

    (* In the context [env, z:t], variable z is represented by 0. *)
    let zvar = Var 0   in

    strengthen c' [zvar; zvar; Refl(o, zvar, t')]  in

  (* Finally, we want to compute the whole expression's type, e.g.,
         c[x,y,p -> a,b,q].
     Since [env, x, y, p |- c], we can get this by strengthening.
   *)
  let ind_eq_type = strengthen c [a;b;q]  in

  (w_ty_expected, ind_eq_type)

