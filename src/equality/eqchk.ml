(** Type-directed equality checking based on user-provided rules. *)

open Eqchk_common

(** Types and functions for manipulation of rules. *)

(* An equality checker is given by beta rules and extensionality rules. We organize them
   as maps taking a symbol to a list of rules which have that symbol at the head. This
   allows us to quickly determine which rules are potentially applicable. *)
type checker = {
  normalizer : Eqchk_normalizer.normalizer ;
  ext_rules : Eqchk_extensionality.equation list SymbolMap.t ;
}

let empty_checker =
  { normalizer = Eqchk_normalizer.empty_normalizer ;
    ext_rules = SymbolMap.empty }


(** The [add_XYZ] functions add a new rule, computed from the given derivation, to the
   given checker, or raise [Invalid_rule] if not possible. *)

let add_type_computation' checker drv =
  let sym, bt, normalizer = Eqchk_normalizer.add_type_computation checker.normalizer drv in
   sym, bt, {checker with normalizer}

let add_type_computation checker drv =
  match add_type_computation' checker drv with
  | _, _, checker -> checker

let add_term_computation' checker drv =
  let sym, bt, normalizer = Eqchk_normalizer.add_term_computation checker.normalizer drv in
  sym, bt, {checker with normalizer}

let add_term_computation checker drv =
  match add_term_computation' checker drv with
  | (_, _, checker) -> checker

let add_extensionality' checker drv =
  let sym, bt = Eqchk_extensionality.make_equation drv in
  let rls =
    match SymbolMap.find_opt sym checker.ext_rules with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  (sym, {checker with ext_rules = SymbolMap.add sym rls checker.ext_rules})


let add_extensionality checker drv =
  match add_extensionality' checker drv with
  | (_, checker) -> checker

(** General equality checking functions *)

(** An equality to be proved is given by a (possibly abstracted) equality boundary. The
   functions [prove_XYZ] receive such a boundary and attempt to prove the corresponding
   equality. *)

let rec prove_eq_type_abstraction chk sgn abstr =
  let rec fold abstr =
    match Nucleus.invert_eq_type_boundary_abstraction abstr with

    | Nucleus.Stump_NotAbstract eq ->
       Nucleus.(abstract_not_abstract ((prove_eq_type chk sgn eq)))

    | Nucleus.Stump_Abstract (atm, abstr) ->
       let abstr = fold abstr in
       Nucleus.abstract_eq_type atm abstr
  in
  fold abstr

and prove_eq_term_abstraction chk sgn abstr =
  let rec fold abstr =
    match Nucleus.invert_eq_term_boundary_abstraction abstr with

    | Nucleus.Stump_NotAbstract bdry ->
       Nucleus.(abstract_not_abstract ((prove_eq_term ~ext:true chk sgn bdry)))

    | Nucleus.Stump_Abstract (atm, abstr) ->
       let abstr = fold abstr in
       Nucleus.abstract_eq_term atm abstr
  in
  fold abstr

and prove_eq_type chk sgn (ty1, ty2) =
  let ty1_eq_ty1', ty1' = Eqchk_normalizer.normalize_type ~strong:true sgn chk.normalizer ty1
  and ty2_eq_ty2', ty2' = Eqchk_normalizer.normalize_type ~strong:true sgn chk.normalizer ty2 in
  let ty1'_eq_ty2' = check_normal_type chk sgn ty1' ty2' in
  Nucleus.transitivity_type
    (Nucleus.transitivity_type ty1_eq_ty1' ty1'_eq_ty2')
    (Nucleus.symmetry_type ty2_eq_ty2')


and prove_eq_term ~ext chk sgn bdry =
  let normalization_phase bdry =
     let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
     let e1_eq_e1', Normal e1' = Eqchk_normalizer.normalize_term ~strong:true sgn chk.normalizer e1
     and e2_eq_e2', Normal e2' = Eqchk_normalizer.normalize_term ~strong:true sgn chk.normalizer e2 in
     let e1'_eq_e2' = check_normal_term chk sgn (Normal e1') (Normal e2') in
     Nucleus.transitivity_term
       (Nucleus.transitivity_term e1_eq_e1' e1'_eq_e2')
       (Nucleus.symmetry_term e2_eq_e2')
  in

  if not ext then
    normalization_phase bdry
  else
    let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
    let t_eq_t', Normal t' = Eqchk_normalizer.normalize_type ~strong:false sgn chk.normalizer t in
    let e1' = Nucleus.(form_is_term_convert sgn e1 t_eq_t')
    and e2' = Nucleus.(form_is_term_convert sgn e2 t_eq_t')in
    let bdry' = Nucleus.(form_eq_term_boundary sgn e1' e2') in
    let bdry =
    match Nucleus.(as_eq_term_boundary bdry' ) with
    | Some bdry -> bdry
    | None -> assert false
    in
    let eq_jdg =
    match Eqchk_extensionality.find chk.ext_rules sgn bdry with

    | Some rap ->
       (* reduce the problem to an application of an extensionality rule *)
       resolve_rap chk sgn IntSet.empty rap

    | None -> normalization_phase bdry

    in
    let t'_eq_t = Nucleus.(symmetry_type t_eq_t') in
    Nucleus.(form_eq_term_convert eq_jdg t'_eq_t)



and check_normal_type chk sgn (Normal ty1) (Normal ty2) =
  match Nucleus.congruence_is_type sgn ty1 ty2 with

  | None -> raise (Equality_fail ("cannot find a congruence rule for given types") )

  | Some rap ->
     let sym = head_symbol_type (Nucleus.expose_is_type ty1) in
     let hs = Eqchk_normalizer.get_type_heads chk.normalizer sym in
     resolve_rap chk sgn hs rap

(* We assume that [e1] and [e2] have the same type. *)
and check_normal_term chk sgn (Normal e1) (Normal e2) =
  match Nucleus.congruence_is_term sgn e1 e2 with

  | None -> raise (Equality_fail "cannot find a congruence rule for given terms")

  | Some rap ->
     let sym = head_symbol_term (Nucleus.expose_is_term e1) in
     let hs = Eqchk_normalizer.get_term_heads chk.normalizer sym in
     resolve_rap chk sgn hs rap


(** Given a rule application, fill in the missing premises, as long as they
    are equations. *)
and resolve_rap :
  'a . checker -> Nucleus.signature -> IntSet.t -> 'a Nucleus.rule_application -> 'a
  = fun chk sgn heads rap ->
  let rec fold k = function

    | Nucleus.RapDone ty1_eq_ty2 -> ty1_eq_ty2

    | Nucleus.RapMore (bdry, rap) ->
       let eq = prove_boundary_abstraction ~ext:(not (IntSet.mem k heads)) chk sgn bdry
       in
       fold (k+1) (rap eq)
  in
  fold 0 rap

(* Prove an abstracted equality boundary. The [ext] flag tells us whether
   we should proceed wither with the type-directed phase or or the normalization-phase. *)
and prove_boundary_abstraction ~ext chk sgn bdry =
  let rec prove bdry =
  match Nucleus.invert_boundary_abstraction bdry with

  | Nucleus.(Stump_NotAbstract (BoundaryEqType eq)) ->
     Nucleus.(abstract_not_abstract (JudgementEqType (prove_eq_type chk sgn eq)))

  | Nucleus.(Stump_NotAbstract (BoundaryEqTerm eq)) ->
     Nucleus.(abstract_not_abstract (JudgementEqTerm (prove_eq_term ~ext chk sgn eq)))

  | Nucleus.Stump_Abstract (atm, bdry) ->
     let eq_abstr = prove bdry in
     Nucleus.abstract_judgement atm eq_abstr

  | Nucleus.(Stump_NotAbstract (BoundaryIsTerm _ | BoundaryIsType _)) ->
     raise (Fatal_error "cannot prove an object boundary")

  in
  prove bdry

(** The exported form of normalization for types *)
let normalize_type ~strong chk sgn t =
  let eq, Normal t = Eqchk_normalizer.normalize_type ~strong sgn chk.normalizer t in
  eq, t

(** The exported form of normalization for terms *)
let normalize_term ~strong chk sgn e =
  let eq, Normal e = Eqchk_normalizer.normalize_term ~strong sgn chk.normalizer e in
  eq, e

let set_type_heads ({normalizer; _} as chk) s hs =
  { chk with normalizer = Eqchk_normalizer.set_type_heads normalizer (Ident s) (IntSet.of_list hs) }

let set_term_heads ({normalizer; _} as chk) s hs =
  { chk with normalizer = Eqchk_normalizer.set_term_heads normalizer (Ident s) (IntSet.of_list hs) }

let add ~quiet ~penv chk drv =
  try
    match add_extensionality' chk drv with
    | (sym, chk) ->
      if not quiet then
        Format.printf "Extensionality rule for %t:@ %t@."
          (print_symbol ~penv sym)
          (Nucleus.print_derivation ~penv drv) ;
      chk

  with
    | Invalid_rule _ ->
      try
        begin match add_type_computation' chk drv with

        |  (sym, ((patt, _), _), chk) ->
            let heads = heads_type patt in
            let chk = { chk with normalizer = Eqchk_normalizer.set_type_heads chk.normalizer sym heads } in
            if not quiet then
              Format.printf "@[<hov 2>Type computation rule for %t (heads at [%t]):@\n%t@.@]"
                (print_symbol ~penv sym)
                (Print.sequence (fun k ppf -> Format.fprintf ppf "%d" k) "," (IntSet.elements heads))
                (Nucleus.print_derivation ~penv drv) ;
            chk
        end

     with
      | Invalid_rule _ ->
          begin match add_term_computation' chk drv with
            | (sym, ((patt, _), _), chk) ->
              let heads = heads_term patt in
              let chk = { chk with normalizer = Eqchk_normalizer.set_term_heads chk.normalizer sym heads } in
              if not quiet then
                Format.printf "@[<hov 2>Term computation rule for %t (heads at [%t]):@\n%t\n@.@]"
                  (print_symbol ~penv sym)
                  (Print.sequence (fun k ppf -> Format.fprintf ppf "%d" k) "," (IntSet.elements heads))
                  (Nucleus.print_derivation ~penv drv) ;
              chk
          end
