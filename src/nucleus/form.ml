(** Formation of judgements from rules *)

open Nucleus_types

let form_alpha_equal_type t1 t2 =
  match Alpha_equal.is_type t1 t2 with
  | false -> None
  | true -> Some (Mk.eq_type Assumption.empty t1 t2)

(** Compare two terms for alpha equality. *)
let form_alpha_equal_term sgn e1 e2 =
  let t1 = Sanity.type_of_term sgn e1
  and t2 = Sanity.type_of_term sgn e2
  in
  (* XXX if e1 and e2 are α-equal, we may apply uniqueness of typing to
     conclude that their types are equal, so we don't have to compute t1, t2,
     and t1 =α= t2. *)
  match Alpha_equal.is_type t1 t2 with
  | false -> Error.raise (AlphaEqualTypeMismatch (t1, t2))
  | true ->
     begin match Alpha_equal.is_term e1 e2 with
     | false -> None
     | true ->
        (* We may keep the assumptions empty here. One might worry
           that the assumptions needed for [e2 : t2] have to be included,
           but this does not seem to be the case: we have [e2 : t2] and
           [t1 == t2] (without assumptions as they are alpha-equal!),
           hence by conversion [e2 : t1], and whatever assumptions are
           required for [e2 : t2], they're already present in [e2]. *)
        Some (Mk.eq_term Assumption.empty e1 e2 t1)
     end

let rec form_alpha_equal_abstraction equal_u abstr1 abstr2 =
  match abstr1, abstr2 with
  | NotAbstract u1, NotAbstract u2 ->
     begin match equal_u u1 u2 with
     | None -> None
     | Some eq -> Some (Mk.not_abstract eq)
     end
  | Abstract (x1, t1, abstr1), Abstract (x2, t2, abstr2) ->
     let x = Name.prefer x1 x2 in
     begin match Alpha_equal.is_type t1 t2 with
     | false -> None
     | true ->
        begin match form_alpha_equal_abstraction equal_u abstr1 abstr2 with
        | None -> None
        | Some eq -> Some (Mk.abstract x t1 eq)
        end
     end
  | (NotAbstract _, Abstract _)
  | (Abstract _, NotAbstract _) -> None


(** Partial rule applications *)

(* Form a rule application for the given constructor [c] *)
let form_constructor_rap sgn c =
  let prems, concl = Signature.lookup_rule c sgn in
  let constr =
    match concl with
    | Rule.BoundaryIsType _ ->
       (fun args -> JudgementIsType (Mk.type_constructor c (Indices.to_list args)))

    | Rule.BoundaryIsTerm _ ->
       (fun args -> JudgementIsTerm (Mk.term_constructor c (Indices.to_list args)))

    | Rule.BoundaryEqType (lhs_schema, rhs_schema) ->
       (fun args ->
         (* order of arguments not important in [Collect_assumptions.arguments],
            we could try avoiding a list reversal caused by [Indices.to_list]. *)
         let asmp = Collect_assumptions.arguments (Indices.to_list args)
         and lhs = Instantiate_meta.is_type ~lvl:0 args lhs_schema
         and rhs = Instantiate_meta.is_type ~lvl:0 args rhs_schema
         in
         JudgementEqType (Mk.eq_type asmp lhs rhs))

    | Rule.BoundaryEqTerm (e1_schema, e2_schema, t_schema) ->
       (fun args ->
         (* order of arguments not important in [Collect_assumptions.arguments],
            we could try avoiding a list reversal caused by [Indices.to_list]. *)
         let asmp = Collect_assumptions.arguments (Indices.to_list args)
         and e1 = Instantiate_meta.is_term ~lvl:0 args e1_schema
         and e2 = Instantiate_meta.is_term ~lvl:0 args e2_schema
         and t = Instantiate_meta.is_type ~lvl:0 args t_schema
         in
         JudgementEqTerm (Mk.eq_term asmp e1 e2 t))
  in
  match prems with
  | [] -> RapDone (constr [])
  | prem :: prems ->

     let rec rap_apply (args, bdry, prems) abstr =
       if not (Check.judgement_boundary_abstraction sgn abstr bdry)
       then Error.raise InvalidArgument ;
       let arg = Judgement.to_argument abstr in
       let args = arg :: args in
       match prems with
       | [] ->
          RapDone (constr args)
       | prem :: prems ->
          let bdry = (Instantiate_meta.abstraction Form_rule.instantiate_premise ~lvl:0 args prem) in
          RapMore (bdry, rap_apply (args, bdry, prems))
     in
     let bdry = Instantiate_meta.abstraction Form_rule.instantiate_premise ~lvl:0 [] prem in
     RapMore (bdry, rap_apply ([], bdry, prems))


let form_is_term_atom = Mk.atom

(** Conversion *)

let form_is_term_convert_opt sgn e (EqType (asmp, t1, t2)) =
  match e with
  | TermConvert (e, asmp0, t0) ->
     if Alpha_equal.is_type t0 t1 then
       (* here we rely on transitivity of equality *)
       let asmp = Assumption.union asmp0 (Assumption.union asmp (Collect_assumptions.is_type t1))
       (* we could have used the assumptions of [t0] instead, because [t0] and [t1] are
            alpha equal, and so either can derive the type. Possible optimizations:
              (i) pick the smaller of the assumptions of [t0] or of [t1],
             (ii) pick the asumptions that are included in [t2]
            (iii) remove assumptions already present in [t2] from the assumption set
       *)
       in
       (* [e] itself is not a [TermConvert] by the maintained invariant. *)
       Some (Mk.term_convert e asmp t2)
     else
       None

  | (TermAtom _ | TermBound _ | TermConstructor _ | TermMeta _) as e ->
     let t0 = Sanity.natural_type sgn e in
     if Alpha_equal.is_type t0 t1 then
       (* We need not include assumptions of [t1] because [t0] is alpha-equal
            to [t1] so we can use [t0] in place of [t1] if so desired. *)
       (* [e] is not a [TermConvert] by the above pattern-check *)
       Some (Mk.term_convert e asmp t2)
     else
       None

let form_is_term_convert sgn e (EqType (_, t1, _) as eq) =
  match form_is_term_convert_opt sgn e eq with
  | Some e -> e
  | None ->
     let t0 = Sanity.natural_type sgn e in
     Error.raise (InvalidConvert (t0, t1))

let form_eq_term_convert_opt (EqTerm (asmp1, e1, e2, t0)) (EqType (asmp2, t1, t2)) =
  if Alpha_equal.is_type t0 t1 then
    (* We could have used the assumptions of [t0] instead of [t1], see comments in [form_is_term]
       about possible optimizations. *)
    let asmp = Assumption.union asmp1 (Assumption.union asmp2 (Collect_assumptions.is_type t1)) in
    Some (Mk.eq_term asmp e1 e2 t2)
  else
    None

let form_eq_term_convert (EqTerm (_, _, _, t0) as eq1) (EqType (_, t1, _) as eq2) =
  match form_eq_term_convert_opt eq1 eq2 with
  | Some eq -> eq
  | None -> Error.raise (InvalidConvert (t0, t1))

let symmetry_term (EqTerm (asmp, e1, e2, t)) = Mk.eq_term asmp e2 e1 t

let symmetry_type (EqType (asmp, t1, t2)) = Mk.eq_type asmp t2 t1

let transitivity_term (EqTerm (asmp, e1, e2, t)) (EqTerm (asmp', e1', e2', t')) =
  match Alpha_equal.is_type t t' with
  | false -> Error.raise (AlphaEqualTypeMismatch (t, t'))
  | true ->
     begin match Alpha_equal.is_term e2 e1' with
     | false -> Error.raise (AlphaEqualTermMismatch (e2, e1'))
     | true ->
        (* XXX could use assumptions of [e1'] instead, or whichever is better. *)
        let asmp = Assumption.union asmp (Assumption.union asmp' (Collect_assumptions.is_term e2))
        in Mk.eq_term asmp e1 e2' t
     end

let transitivity_type (EqType (asmp1, t1, t2)) (EqType (asmp2, u1, u2)) =
  begin match Alpha_equal.is_type t2 u1 with
  | false -> Error.raise (AlphaEqualTypeMismatch (t2, u1))
  | true ->
     (* XXX could use assumptions of [u1] instead, or whichever is better. *)
     let asmp = Assumption.union asmp1 (Assumption.union asmp2 (Collect_assumptions.is_type t2))
     in Mk.eq_type asmp t1 u2
  end

(** Formation of boundaries *)

let form_is_type_boundary = BoundaryIsType ()

let form_is_term_boundary t = BoundaryIsTerm t

let form_eq_type_boundary t1 t2 = BoundaryEqType (t1, t2)

let form_eq_term_boundary sgn e1 e2 =
  let t1 = Sanity.type_of_term sgn e1
  and t2 = Sanity.type_of_term sgn e2 in
  if Alpha_equal.is_type t1 t2 then
    BoundaryEqTerm (e1, e2, t1)
  else
    Error.raise (AlphaEqualTypeMismatch (t1, t2))

let rec form_is_term_boundary_abstraction = function

  | NotAbstract t ->
     NotAbstract (form_is_term_boundary t)

  | Abstract (x, t, abstr) ->
     Abstract (x, t, form_is_term_boundary_abstraction abstr)
