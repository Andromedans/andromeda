(** Attempt to remove [x] from list [xs]. *)
let rec remove_bound x xs =
  match xs with
  | [] -> None
  | y :: ys ->
    if x = y
    then Some ys
    else (match remove_bound x ys with None -> None | Some ys -> Some (y :: ys))

(** The name in the head position of a pattern *)
let has_head_name = function
  | None -> false
  | Some key ->
     begin match key with
           | Pattern.Key_Constant _
           | Pattern.Key_Atom _ -> true
           | Pattern.Key_Type
           | Pattern.Key_Lambda
           | Pattern.Key_Prod
           | Pattern.Key_Eq
           | Pattern.Key_Refl
           | Pattern.Key_Inhab
           | Pattern.Key_Bracket
           | Pattern.Key_Projection _
           | Pattern.Key_Signature _
           | Pattern.Key_Structure _ -> false
     end

(** Convert a term [e] of type [t] to a pattern with respect to the
    given bound variables [pvars]. That is, the bound variables from [pvars]
    are treated as pattern variables. Return the list of those [pvars] that
    were not encoutered, and the pattern generated. *)
let rec of_term env pvars ({Tt.term=e';loc;_} as e) t =
  let original = pvars, Pattern.Term (e,t) in
  match e' with

  | Tt.Type | Tt.Lambda _ | Tt.Prod _ -> original

  | Tt.Atom x -> pvars, Pattern.Atom x

  | Tt.Constant (x, es) ->
    (* A primitive application is always a pattern, never a term *)
    let rec fold pvars args_so_far pes xrts args_left =
      match xrts, args_left with
      | [], [] -> pvars, List.rev pes
      | (x, (r, t)) :: xrts, e :: args_left ->
        let t = Tt.instantiate_ty args_so_far t in
        let pvars, pe = of_term env pvars e t in
        fold pvars (e::args_so_far) (pe::pes) xrts args_left
      | ([],_::_) | (_::_,[]) ->
        Error.impossible ~loc "malformed primitive application in Pattern.of_term"
    in
    let xrts =
      begin match Value.Env.lookup_constant x env with
      | Some (xrts, _) -> xrts
      | None -> Error.impossible ~loc "Hint.of_term, unknown primitive operation %t" (Name.print_ident x)
      end in
    let pvars, pes = fold pvars [] [] xrts es in
    pvars, Pattern.Constant (x, pes)

  | Tt.Bound k ->
    begin match remove_bound k pvars with
      | None -> original
      | Some pvars -> pvars, Pattern.PVar k
    end

  | Tt.Spine (e, (xts, u), es) ->
    let rec fold pvars all_terms args_so_far ps xts args_left =
      match xts, args_left with
      | [], [] -> pvars, all_terms, List.rev ps
      | (x, t) :: xts, e :: args_left ->
        let t = Tt.instantiate_ty args_so_far t in
        let pvars, p = of_term env pvars e t in
        let all_terms = (match p with Pattern.Term _ -> all_terms | _ -> false) in
        fold pvars all_terms (e::args_so_far) (p::ps) xts args_left
      | ([],_::_) | (_::_,[]) ->
        Error.impossible ~loc "malformed Pattern.spine in Pattern.of_term"
    in

    let pvars, e = of_term env pvars e (Tt.mk_prod_ty ~loc xts u) in
    let pvars, all_terms, es = fold pvars true [] [] xts es in
    (* if [name_of_term] came back then e is a name and thus a Tt.term *)
    begin if all_terms
      then original
      else pvars, Pattern.Spine (e, (xts, u), es)
    end

  | Tt.Eq (t, e1, e2) ->
    let pvars, t' = of_ty env pvars t in
    let pvars, e1 = of_term env pvars e1 t in
    let pvars, e2 = of_term env pvars e2 t in
    begin match t', e1, e2 with
      | Pattern.Ty (Pattern.Term _), Pattern.Term _, Pattern.Term _ -> original
      | Pattern.Ty _, _, _ -> pvars, (Pattern.Eq (t', e1, e2))
    end

  | Tt.Refl (t, e) ->
    let pvars, t' = of_ty env pvars t in
    let pvars, e = of_term env pvars e t in
    begin match t', e with
      | Pattern.Ty (Pattern.Term _), Pattern.Term _ -> original
      | _, _ -> pvars, (Pattern.Refl (t', e))
    end

  | Tt.Signature _ -> original

  | Tt.Structure _ -> original

  | Tt.Projection _ -> original

and of_ty env pvars (Tt.Ty t) =
  let pvars, t = of_term env pvars t Tt.typ in
  pvars, (Pattern.Ty t)

(** given an abstraction [xts] with [n] elements, return the list [[0,...,{n-1}]]. *)
let pvars_of_binders xts =
  snd (List.fold_left (fun (k, pvars) _ -> (k+1), k :: pvars) (0, []) xts)

let mk_beta ~loc env ctx hyps (xts, (t, (e1 : Tt.term), e2)) =
  (* XXX here would be a good place to flatten beta patterns. *)
  let pvars = pvars_of_binders xts in
  let pvars, p = of_term env pvars e1 t in
    match pvars with
      | [] ->
        let key = Pattern.term_key_opt e1 in
        (* XXX should we allow to rewrite type-formers (other than Π)? *)

        begin match has_head_name key, key with
              | false, _
              | _, None -> Error.runtime ~loc "invalid beta hint"
              | true, Some key ->
                 let pattern =
                 begin
                   match p with
                   | Pattern.Atom x -> Pattern.BetaAtom x, e2
                   | Pattern.Constant (x, pes) -> Pattern.BetaConstant (x, pes), e2
                   | Pattern.Spine (pe, yus, pes) -> Pattern.BetaSpine (pe, yus, pes), e2
                   | Pattern.PVar _ | Pattern.Bracket _ | Pattern.Eq _ | Pattern.Refl _
                   | Pattern.Term _ ->
                      Error.runtime ~loc "invalid beta hint"
                 end in
                 key, (ctx, hyps, (xts, pattern))
        end

      | _ :: _ ->
        let xs = List.map (fun k -> fst (List.nth (List.rev xts) k)) pvars in
        Error.runtime ~loc "this beta hint leaves some variables unmatched (%t)"
          (Print.sequence Name.print_ident "," xs)

let mk_eta ~loc env ctx hyps (xts, (t, e1, e2)) =
  let pvars = pvars_of_binders xts in
  (** We should *first* turn [e1] and [e2] into patterns and only then [t]
      in case [e1] or [e2] is [pvar] which also appears in [t]. This is so because
      we want [e1] and [e2] to be distinct pattern variables.
   *)
  let pvars, p1 = of_term env pvars e1 t in
  let pvars, p2 = of_term env pvars e2 t in
  let pvars, ((Pattern.Ty pt') as pt) = of_ty env pvars t in
  let key = Pattern.ty_key_opt t in
  match has_head_name key, key, p1, p2 with
    | true, Some key, Pattern.PVar k1, Pattern.PVar k2 when k1 <> k2 ->
      key, (ctx, hyps, (xts, (pt, k1, k2)))
    | false, _, _, _ ->
        Error.runtime ~loc
          "the type of an eta hint must be a symbol@ or a symbol applied to arguments"
    | true, _, _, _ ->
        Error.runtime ~loc
          "the left- and right-hand side of an eta hint must be distinct variables"

let mk_general ~loc env ctx hyps (xts, ((t : Tt.ty), e1, e2)) =
  let pvars = pvars_of_binders xts in

  (* XXX when we try to apply a hint to a term, we whnf the term, so we ought
     to do the same with the hint *)
  (* XXX first instantiate with the abstraction. what to do wrt to the pvars?
     eventually, raise a `general_red' handler? *)
  (* let Tt.Ty (t, loc) = t in *)
  (* let t = Equal.whnf env (t, loc) *)
  (* and e1 = Equal.whnf env e1 *)
  (* and e2 = Equal.whnf env e2 in *)
  (* let t = Tt.ty t in *)

  let pvars, ((Pattern.Ty pt') as pt) = of_ty env pvars t in
  let pvars, pe1 = of_term env pvars e1 t in
  let pvars, pe2 = of_term env pvars e2 t in
  let key = Pattern.general_key e1 e2 t in
  key, (ctx, hyps, (xts, (pt, pe1, pe2)))


let mk_inhabit ~loc env ctx hyps (xts, t) =
  let pvars = pvars_of_binders xts in
  let pvars, ((Pattern.Ty pt') as pt) = of_ty env pvars t in
  match Pattern.ty_key_opt t with
  | Some key -> key, (ctx, hyps, (xts, pt))
  | None -> Error.runtime ~loc "invalid inhabit hint"
                          (* XXX is it necessary to fail here? *)
