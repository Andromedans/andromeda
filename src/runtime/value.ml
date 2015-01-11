type value =
(** A value is obtained by successfully evaluating a computation. *)
  Tt.term * Tt.ty
  (** A judgement [e : t] where [e] is guaranteed to have the type [t]. *)

type result =
(** Possible results of evaluating a computation. *)
  | Return of value


let print ?max_level xs v ppf =
  let (e,t) = v in
    Print.print ~at_level:0 ppf "%t :@ %t"
          (Tt.print_term ~max_level:0 xs e)
          (Tt.print_ty ~max_level:0 xs t)

