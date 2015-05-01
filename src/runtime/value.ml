(** Runtime values and results *)

(** A value is obtained by successfully evaluating a computation. *)
type value =
  Tt.term * Tt.ty (** A judgement [e : t] where [e] is guaranteed to have the type [t]. *)

(** Possible results of evaluating a computation. *)
and result =
  | Return of value

let print ?max_level xs v ppf =
  let (e,t) = v in
    Print.print ~at_level:0 ppf "@[<hov 2>%t@\n    : %t@]"
          (Tt.print_term ~max_level:999 xs e)
          (Tt.print_ty ~max_level:999 xs t)

