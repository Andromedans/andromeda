(** Equality checking and coercions *)

let return = Runtime.return
let (>>=) = Runtime.bind

(* Compare two types *)
let equal_type ~at t1 t2 =
  match Nucleus.form_alpha_equal_type t1 t2 with
    | Some eq -> return eq
    | None ->
       Reflect.operation_equal_type ~at t1 t2 >>= fun eq ->
       let (Nucleus.Stump_EqType (_asmp, t1', t2')) = Nucleus.invert_eq_type eq in
       if Nucleus.alpha_equal_type t1 t1' && Nucleus.alpha_equal_type t2 t2' then
         return eq
       else
         Runtime.(error ~at (InvalidEqualType (t1, t2)))

let coerce ~at sgn jdg bdry =
  if Nucleus.check_judgement_boundary_abstraction sgn jdg bdry then
    return jdg
  else
    Reflect.operation_coerce ~at jdg bdry >>= fun jdg ->
       if Nucleus.check_judgement_boundary_abstraction sgn jdg bdry then
         return jdg
       else
         Runtime.(error ~at (InvalidCoerce (jdg, bdry)))
