(** Formation of conversions *)


open Nucleus_types

let is_term_convert_opt sgn e (EqType (asmp, t1, t2)) =
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

  | (TermAtom _ | TermBoundVar _ | TermConstructor _ | TermMeta _) as e ->
     let t0 = Sanity.natural_type sgn e in
     if Alpha_equal.is_type t0 t1 then
       (* We need not include assumptions of [t1] because [t0] is alpha-equal
            to [t1] so we can use [t0] in place of [t1] if so desired. *)
       (* [e] is not a [TermConvert] by the above pattern-check *)
       Some (Mk.term_convert e asmp t2)
     else
       None

let is_term_convert sgn e (EqType (_, t1, _) as eq) =
  match is_term_convert_opt sgn e eq with
  | Some e -> e
  | None ->
     let t0 = Sanity.natural_type sgn e in
     Error.raise (InvalidConvert (t0, t1))

let eq_term_convert_opt (EqTerm (asmp1, e1, e2, t0)) (EqType (asmp2, t1, t2)) =
  if Alpha_equal.is_type t0 t1 then
    (* We could have used the assumptions of [t0] instead of [t1], see comments in [form_is_term]
       about possible optimizations. *)
    let asmp = Assumption.union asmp1 (Assumption.union asmp2 (Collect_assumptions.is_type t1)) in
    Some (Mk.eq_term asmp e1 e2 t2)
  else
    None

let eq_term_convert (EqTerm (_, _, _, t0) as eq1) (EqType (_, t1, _) as eq2) =
  match eq_term_convert_opt eq1 eq2 with
  | Some eq -> eq
  | None -> Error.raise (InvalidConvert (t0, t1))