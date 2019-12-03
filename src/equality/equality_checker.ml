(** Type-directed equality checking based on user-provided rules. *)

(** The types of beta rules. *)

type type_beta_rule =
  { type_beta_pattern : Rewrite.is_type (* the rewrite pattern to match the left-hand side *)
  ; type_beta_rule : Nucleus.eq_type Nucleus.rule (* the associated rule *)
  }

type term_beta_rule =
  { term_beta_pattern : Rewrite.is_term (* the rewrite pattern to match the left-hand side *)
  ; term_beta_rule : Nucleus.eq_term Nucleus.rule (* the associated rule *)
  }

(** The type of extensionality rules. *)
type extensionality_rule =
  { ext_pattern : Rewrite.is_type (* the rewrite pattern to match the type of equality *)
  ; ext_rule : Nucleus.eq_term Nucleus.rule (* the associated rule *)
  }

exception Equality_fail

exception Invalid_rule

(** Types and functions for manipulation of rules. *)

(** We index rules by the heads of expressions, which can be identifiers or meta-variables (nonces). *)
type symbol =
  | Ident of Ident.t
  | Nonce of Nonce.t

let compare_symbol x y =
  match x, y with
  | Ident _, Nonce _ -> -1
  | Ident i, Ident j -> Ident.compare i j
  | Nonce n, Nonce m -> Nonce.compare n m
  | Nonce _, Ident _ -> 1

module SymbolMap = Map.Make(
                   struct
                     type t = symbol
                     let compare = compare_symbol
                   end)

(* An equality checker is given by beta rules and extensionality rules. We organize them
   as maps taking a symbol to a list of rules which have that symbol at the head. This
   allows us to quickly determine which rules are potentially applicable. *)
type checker = {
   type_beta_rules : type_beta_rule list SymbolMap.t ;
   term_beta_rules : term_beta_rule list SymbolMap.t ;
   ext_rules : extensionality_rule list SymbolMap.t
  }

let empty_checker = {
    type_beta_rules = SymbolMap.empty ;
    term_beta_rules = SymbolMap.empty ;
    ext_rules = SymbolMap.empty
  }


(** The head symbol of a term. *)
let head_symbol_term e =
  let rec fold = function
    | Nucleus_types.TermBoundVar _ -> assert false
    | Nucleus_types.(TermAtom {atom_nonce=n; _}) -> Nonce n
    | Nucleus_types.TermConstructor (c, _) -> Ident c
    | Nucleus_types.(TermMeta (MetaFree {meta_nonce=n;_}, _)) -> Nonce n
    | Nucleus_types.(TermMeta (MetaBound _, _)) -> assert false
    | Nucleus_types.TermConvert (e, _, _) -> fold e
  in
  fold e


(** The head symbol of a type. *)
let head_symbol_type = function
  | Nucleus_types.TypeConstructor (c, _) -> Ident c
  | Nucleus_types.(TypeMeta (MetaFree {meta_nonce=n;_}, _)) -> Nonce n
  | Nucleus_types.(TypeMeta (MetaBound _, _)) -> assert false



(** Functions [make_XYZ_rule] convert a derivation to a rewrite rule, or raise
    the exception, or raise the exception [Invalid_rule] when the derivation
    has the wrong form. *)

let rec is_object_premise = function
  | Nucleus_types.(NotAbstract (BoundaryIsType _ | BoundaryIsTerm _)) -> true
  | Nucleus_types.(NotAbstract (BoundaryEqType _ | BoundaryEqTerm _)) -> false
  | Nucleus_types.Abstract (_, _, prem) -> is_object_premise prem


let make_type_beta_rule sgn drv =
  let rec fold k  = function

    | Nucleus_types.(Conclusion eq)  ->
       let (Nucleus_types.EqType (_asmp, t1, _t2)) = Nucleus.expose_eq_type eq in
       begin match Rewrite.make_is_type sgn k t1 with

       | Some patt ->
          let s = head_symbol_type t1 in
          (s, patt)

       | None -> raise Invalid_rule
       end

    | Nucleus_types.Premise (n, bdry, drv) ->
       if is_object_premise bdry then
         fold (k+1) drv
       else
         raise Invalid_rule
  in
  let drv =
    match Nucleus.as_eq_type_rule drv with
    | Some drv -> drv
    | None -> raise Invalid_rule
  in
  let (s, patt) = fold 0 (Nucleus.expose_rule drv) in
  s, { type_beta_pattern = patt; type_beta_rule = drv }


let make_term_beta_rule sgn drv =
  let rec fold k = function

    | Nucleus_types.(Conclusion eq) ->
       let (Nucleus_types.EqTerm (_asmp, e1, _e2, _t)) = Nucleus.expose_eq_term eq in
       begin match Rewrite.make_is_term sgn k e1 with

       | Some patt ->
          let s = head_symbol_term e1 in
          (s, patt)

       | None -> raise Invalid_rule
       end

    | Nucleus_types.Premise (n, bdry, drv) ->
       if is_object_premise bdry then
         fold (k+1) drv
       else
         raise Invalid_rule
  in
  let drv =
    match Nucleus.as_eq_term_rule drv with
    | Some drv -> drv
    | None -> raise Invalid_rule
  in
  let (s, patt) = fold 0 (Nucleus.expose_rule drv) in
  s, { term_beta_pattern = patt; term_beta_rule = drv }


let make_ext_rule sgn drv =

  (* Check that e is the bound meta-variable k *)
  let check_meta k = function
    | Nucleus_types.(TermMeta (MetaBound j, [])) -> if j <> k then raise Invalid_rule
    | Nucleus_types.(TermMeta (MetaFree _, _) | TermMeta (MetaBound _, _::_) | TermBoundVar _ | TermAtom _ |
                     TermConstructor _ | TermConvert _) ->
       raise Invalid_rule
  in

  (* Extract a type from an optional boundary *)
  let extract_type = function
    | Some (Nucleus_types.(NotAbstract (BoundaryIsTerm t))) -> t
    | Some (Nucleus_types.(NotAbstract (BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _) | Abstract _))
    | None ->
       raise Invalid_rule
  in

  (* do the main work where:
     n_ob counts leading object premises, n_eq counts trailing equality premises,
     (bdry1opt, bdry2opt) are the last two seen object premise boundaries
  *)
  let rec fold (bdry1opt, bdry2opt) n_ob n_eq = function

    | Nucleus_types.(Conclusion eq) ->
       let (Nucleus_types.EqTerm (_asmp, e1, e2, t)) = Nucleus.expose_eq_term eq in
       check_meta (n_ob-1) e1 ; (* check LHS *)
       check_meta n_ob e2 ; (* check RHS *)
       let t1 = extract_type bdry1opt in
       let t1' = Shift_meta.is_type (n_eq+1) t1
       and t2' = Shift_meta.is_type n_eq (extract_type bdry2opt) in
       (* check that types are equal *)
       if not (Alpha_equal.is_type t1' t) || not (Alpha_equal.is_type t2' t) then raise Invalid_rule ;
       begin match Rewrite.make_is_type sgn (n_ob-2) t1 with
       | Some patt ->
          let s = head_symbol_type t1 in
          (s, patt)
       | None -> raise Invalid_rule
       end

    | Nucleus_types.Premise (_, bdry, drv) ->
       if is_object_premise bdry then
         begin
           if n_eq > 0 then raise Invalid_rule ;
           fold (bdry2opt, Some bdry) (n_ob + 1) n_eq drv
         end
       else
         fold (bdry1opt, bdry2opt) n_ob (n_eq + 1) drv
  in

  (* Put the derivation into the required form *)
  let drv =
    match Nucleus.as_eq_term_rule drv with
    | Some drv -> drv
    | None -> raise Invalid_rule
  in
  (* Collect head symbol and pattern (and verify that drv has the correct form) *)
  let s, patt = fold (None, None) 0 0 (Nucleus.expose_rule drv) in
  s, { ext_pattern = patt; ext_rule = drv }


(** The [add_XYZ] functions add a new rule, computed from the given derivation, to the
   given checker, or raise [Invalid_rule] if not possible. *)

let add_type_beta checker sgn drv =
  let sym, bt = make_type_beta_rule sgn drv in
  let rls =
    match SymbolMap.find_opt sym checker.type_beta_rules with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  { checker with type_beta_rules = SymbolMap.add sym rls checker.type_beta_rules }


let add_term_beta checker sgn drv =
  let sym, bt = make_term_beta_rule sgn drv in
  let rls =
    match SymbolMap.find_opt sym checker.term_beta_rules with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  { checker with term_beta_rules = SymbolMap.add sym rls checker.term_beta_rules }


let add_extensionality checker sgn drv =
  let sym, bt = make_ext_rule sgn drv in
  let rls =
    match SymbolMap.find_opt sym checker.ext_rules with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  { checker with ext_rules = SymbolMap.add sym rls checker.ext_rules }


(** Apply rap to a list of arguments *)
let rap_apply_args rap args =
  let rec fold rap args =
  match rap, args with
  | rap, [] -> rap
  | Nucleus.RapMore (_bdry, f), arg :: args -> fold (f arg) args
  | Nucleus.RapDone _, _::_ -> assert false
  in
  try
    Some (fold rap args)
  with
  | Nucleus.Error _ -> None

(** Functions that apply rewrite rules *)

let apply_type_beta chk sgn t =
  let s = head_symbol_type (Nucleus.expose_is_type t) in
  match SymbolMap.find_opt s chk.type_beta_rules with

  | None -> None

  | Some lst ->
     let rec fold = function
       | [] -> None

       | {type_beta_pattern=patt; type_beta_rule=rl} :: lst ->
          (* XXX match_is_type should normalize parts of t as necessary *)
          begin match Rewrite.match_is_type sgn t patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_type_rap sgn rl in
             begin match rap_apply_args rap args with
             | Some (Nucleus.RapDone t_eq_t') -> Some t_eq_t'
             | None -> fold lst
             | Some (Nucleus.RapMore _) -> assert false
             end
          end
     in
     fold lst

(** Apply a beta rule to [e]. *)
let apply_term_beta chk sgn e =
  let s = head_symbol_term (Nucleus.expose_is_term e) in
  match SymbolMap.find_opt s chk.term_beta_rules with

  | None -> None

  | Some lst ->
     let rec fold = function
       | [] -> None

       | {term_beta_pattern=patt; term_beta_rule=rl} :: lst ->
          (* XXX match_is_type should normalize parts of t as necessary *)
          begin match Rewrite.match_is_term sgn e patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_term_rap sgn rl in
             begin match rap_apply_args rap args with
             | Some (Nucleus.RapDone e_eq_e') -> Some e_eq_e'
             | None -> fold lst
             | Some (Nucleus.RapMore _) -> assert false
             end
          end
     in
     fold lst


(** A tag to indicate that a term or a type is in whnf form *)
type 'a whnf = Whnf of 'a

(** Weak head-normal form normalization *)
let rec whnf_type' chk sgn ty =
  let rec fold ty_eq_ty' ty' =

    match apply_type_beta chk sgn ty' with

    | None -> ty_eq_ty', Whnf ty'

    | Some ty'_eq_ty'' ->
       let (Nucleus.Stump_EqType (_, _, ty'')) = Nucleus.invert_eq_type ty'_eq_ty'' in
       let ty_eq_ty'' = Nucleus.transitivity_type ty_eq_ty' ty'_eq_ty'' in
       fold ty_eq_ty'' ty''
  in
  fold (Nucleus.reflexivity_type ty) ty

and whnf_term' chk sgn e =
  let rec fold e_eq_e' e' =

    match apply_term_beta chk sgn e' with

    | None -> e_eq_e', Whnf e'

    | Some e'_eq_e'' ->
       let (Nucleus.Stump_EqTerm (_, _, e'', _)) = Nucleus.invert_eq_term sgn e'_eq_e'' in
       (* XXX this will fail because e_eq_e' and e'_eq_e'' may happen at different types *)
       (* XXX figure out how to convert e'_eq_e'' using Nucleus.convert_eq_term *)
       let e_eq_e'' = Nucleus.transitivity_term e_eq_e' e'_eq_e'' in
       fold e_eq_e'' e''
  in
  fold (Nucleus.reflexivity_term sgn e) e


(** General equality checking functions *)

(** An equality to be proved is given by a (possibly abstracted) equality boundary. The
   functions [prove_XYZ] receive such a boundary and attempt to prove the corresponding
   equality. *)

let rec prove_eq_type_abstraction chk sgn abstr =
  match Nucleus.invert_eq_type_boundary_abstraction abstr with

  | Nucleus.Stump_NotAbstract eq ->
     Nucleus.(abstract_not_abstract ((prove_eq_type chk sgn eq)))

  | Nucleus.Stump_Abstract (atm, abstr) ->
     let abstr = prove_eq_type_abstraction chk sgn abstr in
     Nucleus.abstract_eq_type atm abstr

and prove_eq_term_abstraction chk sgn abstr =
  match Nucleus.invert_eq_term_boundary_abstraction abstr with

  | Nucleus.Stump_NotAbstract bdry ->
     Nucleus.(abstract_not_abstract ((prove_eq_term chk sgn bdry)))

  | Nucleus.Stump_Abstract (atm, abstr) ->
     let abstr = prove_eq_term_abstraction chk sgn abstr in
     Nucleus.abstract_eq_term atm abstr

and prove_eq_type chk sgn (ty1, ty2) =
  let ty1_eq_ty1', ty1' = whnf_type' chk sgn ty1
  and ty2_eq_ty2', ty2' = whnf_type' chk sgn ty2 in
  let ty1'_eq_ty2' = check_whnf_type chk sgn ty1' ty2' in
  Nucleus.transitivity_type
    (Nucleus.transitivity_type ty1_eq_ty1' ty1'_eq_ty2')
    (Nucleus.symmetry_type ty2_eq_ty2')

and prove_eq_term chk sgn bdry =
  match find_extensionality chk sgn bdry with

  | Some rap ->
     (* reduce the problem to an application of an extensionality rule *)
     resolve_rap chk sgn rap

  | None ->
     let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
     (* normalization phase *)
     let e1_eq_e1', e1' = whnf_term' chk sgn e1
     and e2_eq_e2', e2' = whnf_term' chk sgn e2 in
     (* XXX convert e1_eq_e1' and e2_eq_e2' to be at type t *)
     let e1'_eq_e2' = check_whnf_term chk sgn e1' e2' in
     Nucleus.transitivity_term
       (Nucleus.transitivity_term e1_eq_e1' e1'_eq_e2')
       (Nucleus.symmetry_term e2_eq_e2')

and check_whnf_type chk sgn (Whnf ty1) (Whnf ty2) =
  match Nucleus.congruence_is_type sgn ty1 ty2 with

  | None -> raise Equality_fail

  | Some rap -> resolve_rap chk sgn rap

(* We assume that [e1] and [e2] have the same type. *)
and check_whnf_term chk sgn (Whnf e1) (Whnf e2) =
  match Nucleus.congruence_is_term sgn e1 e2 with

  | None -> raise Equality_fail

  | Some rap -> resolve_rap chk sgn rap


(** Given a rule application, fill in the missing premises, as long as they
    are equations. *)
and resolve_rap :
  'a . checker -> Nucleus.signature -> 'a Nucleus.rule_application -> 'a
  = fun chk sgn rap ->
  let rec fold = function

    | Nucleus.RapDone ty1_eq_ty2 -> ty1_eq_ty2

    | Nucleus.RapMore (bdry, rap) ->
       let eq = prove_boundary_abstraction chk sgn bdry in
       fold (rap eq)
  in
  fold rap

(** Find an extensionality rule for [e1 == e2 : t], if there is one, return a rule
   application that will prove it. *)
and find_extensionality chk sgn bdry =
  let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
  match SymbolMap.find_opt (head_symbol_type (Nucleus.expose_is_type t)) chk.ext_rules with
  | None -> None
  | Some lst ->
     let rec fold = function
       | [] -> None
       | {ext_pattern=patt; ext_rule=rl} :: lst ->
          begin match Rewrite.match_is_type sgn t patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_term_rap sgn rl in
             let arg1 = Nucleus.(abstract_not_abstract (JudgementIsTerm e1))
             and arg2 = Nucleus.(abstract_not_abstract (JudgementIsTerm e2)) in
             begin match rap_apply_args rap (args @ [arg1; arg2]) with
             | None -> fold lst
             | Some rap -> Some rap
             end
          end
     in
     fold lst

and prove_boundary_abstraction chk sgn bdry =
  let rec prove bdry =
  match Nucleus.invert_boundary_abstraction bdry with

  | Nucleus.(Stump_NotAbstract (BoundaryEqType eq)) ->
     Nucleus.(abstract_not_abstract (JudgementEqType (prove_eq_type chk sgn eq)))

  | Nucleus.(Stump_NotAbstract (BoundaryEqTerm eq)) ->
     Nucleus.(abstract_not_abstract (JudgementEqTerm (prove_eq_term chk sgn eq)))

  | Nucleus.Stump_Abstract (atm, bdry) ->
     let eq_abstr = prove bdry in
     Nucleus.abstract_judgement atm eq_abstr

  | Nucleus.(Stump_NotAbstract (BoundaryIsTerm _ | BoundaryIsType _)) ->
     assert false

  in
  prove bdry

(** The exported form of weak-head normalization for types *)
let whnf_type chk sgn t =
  let eq, Whnf t = whnf_type' chk sgn t in
  eq, t

(** The exported form of weak-head normalization for terms *)
let whnf_term chk sgn e =
  let eq, Whnf e = whnf_term' chk sgn e in
  (* XXX convert eq to be at the type of e *)
  eq, e
