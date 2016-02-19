
(** Parenthesis levels (low level means "less likely to need
    parentheses around itself") *)
type t

type infix =
  | Infix0
  | Infix1
  | Infix2
  | Infix3
  | Infix4

(** Highest level possible for a term *)
val highest : t

(** Under no circumstances will this be parenthesized *)
val least : t
val no_parens : t

val proj : t
val proj_left : t

(** Prefix operators *)
val prefix : t
val prefix_arg : t

(** Things that look like an application *)
val app : t
val app_left : t
val app_right : t

(** Infix operators *)
val infix : infix -> t * t * t

(** Equality type *)
val eq : t
val eq_left : t
val eq_right : t

(** Lambdas, products and arrows *)
val binder : t
val in_binder : t
val arr : t
val arr_left : t
val arr_right : t

(** A structure or a signature clause *)
val struct_clause : t
val sig_clause : t

(** Type ascription in a binding *)
val ascription : t

(** A judgement [ctx |- e : t] *)
val jdg : t

