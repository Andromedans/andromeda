(** Type-directed equality checking based on user-provided rules. *)

open Eqchk_common (* sorry *)

(** Types and functions for manipulation of rules. *)

(* An equality checker is given by beta rules and extensionality rules. We organize them
   as maps taking a symbol to a list of rules which have that symbol at the head. This
   allows us to quickly determine which rules are potentially applicable. *)
type checker = {
  type_normalizer : Eqchk_normalizer.type_normalizer ;
  term_normalizer : Eqchk_normalizer.term_normalizer ;
  ext_rules : Eqchk_ext.equation list SymbolMap.t ;
}

let empty_checker =
  { type_normalizer = Eqchk_normalizer.empty_type_normalizer ;
    term_normalizer = Eqchk_normalizer.empty_term_normalizer ;
    ext_rules = SymbolMap.empty}


(** The [add_XYZ] functions add a new rule, computed from the given derivation, to the
   given checker, or raise [Invalid_rule] if not possible. *)

let add_type_computation checker sgn drv =
  { checker with
    type_normalizer = Eqchk_normalizer.add_type_computation sgn checker.type_normalizer drv }

let add_term_computation checker sgn drv =
  { checker with
    term_normalizer = Eqchk_normalizer.add_term_computation sgn checker.term_normalizer drv }


let add_extensionality checker sgn drv =
  let sym, bt = Eqchk_ext.make_equation sgn drv in
  let rls =
    match SymbolMap.find_opt sym checker.ext_rules with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  { checker with ext_rules = SymbolMap.add sym rls checker.ext_rules }


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
  let ty1_eq_ty1', ty1' = Eqchk_normalizer.whnf_type chk.type_normalizer sgn ty1
  and ty2_eq_ty2', ty2' = Eqchk_normalizer.whnf_type chk.type_normalizer sgn ty2 in
  let ty1'_eq_ty2' = check_whnf_type chk sgn ty1' ty2' in
  Nucleus.transitivity_type
    (Nucleus.transitivity_type ty1_eq_ty1' ty1'_eq_ty2')
    (Nucleus.symmetry_type ty2_eq_ty2')

and prove_eq_term chk sgn bdry =
  match Eqchk_ext.find chk.ext_rules sgn bdry with

  | Some rap ->
     (* reduce the problem to an application of an extensionality rule *)
     resolve_rap chk sgn rap

  | None ->
     let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
     (* normalization phase *)
     let e1_eq_e1', e1' = Eqchk_normalizer.whnf_term chk.term_normalizer sgn e1
     and e2_eq_e2', e2' = Eqchk_normalizer.whnf_term chk.term_normalizer sgn e2 in
     (* XXX convert e1_eq_e1' and e2_eq_e2' to be at type t *)
     let e1'_eq_e2' = check_whnf_term chk sgn e1' e2' in
     Nucleus.transitivity_term
       (Nucleus.transitivity_term e1_eq_e1' e1'_eq_e2')
       (Nucleus.symmetry_term e2_eq_e2')

and check_whnf_type chk sgn (Whnf ty1) (Whnf ty2) =
  match Nucleus.congruence_is_type sgn ty1 ty2 with

  | None -> equality_fail ()

  | Some rap -> resolve_rap chk sgn rap

(* We assume that [e1] and [e2] have the same type. *)
and check_whnf_term chk sgn (Whnf e1) (Whnf e2) =
  match Nucleus.congruence_is_term sgn e1 e2 with

  | None -> equality_fail ()

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
  let eq, Whnf t = Eqchk_normalizer.whnf_type chk.type_normalizer sgn t in
  eq, t

(** The exported form of weak-head normalization for terms *)
let whnf_term chk sgn e =
  let eq, Whnf e = Eqchk_normalizer.whnf_term chk.term_normalizer sgn e in
  (* XXX convert eq to be at the type of e *)
  eq, e
