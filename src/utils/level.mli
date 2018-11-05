(** Parenthesis levels. Low level means less likely to be parenthesized.
    The levels described here should strive to be compatible with parsing
    precedence. *)

(** The type of parentheses levels. *)
type t

(** Given a term [at_level] which appears as a subterm in a place that
    allows at most [max_level] terms to be printed without parentheses,
    should we print parentheses? (Essentially, [max_level < at_level].) *)
val parenthesize : at_level:t -> max_level:t -> bool

(* Levels of infix operators. *)
type infix =
  | Infix0
  | Infix1
  | InfixCons
  | Infix2
  | Infix3
  | Infix4

(** Highest level possible for a term *)
val highest : t

(** Lowest level possible for a term *)
val least : t

(** A level which guarantees that no parentheses will ever be printed. *)
val no_parens : t

(** The level of a prefix operator applied to an argument. *)
val prefix : t

(** The elvel of the argument to a prefix operator. *)
val prefix_arg : t

(** Things that look like an application *)
val app : t
val app_left : t
val app_right : t

(** Infix operators *)
val infix : infix -> t * t * t

(** Equality *)
val eq : t
val eq_left : t
val eq_right : t

(** Lambdas, products and arrows *)
val binder : t
val in_binder : t
val arr : t
val arr_left : t
val arr_right : t

(** A judgement [ctx |- e : t] *)
val jdg : t

(** ML product type *)
val ml_prod : t

(** ML product type, arguments *)
val ml_prod_arg : t

(** ML type arrow *)
val ml_arr : t

(** ML type arrow, left argument *)
val ml_arr_left : t

(** ML type arrow, right argument*)
val ml_arr_right : t

(** ML handler *)
val ml_handler : t

(** ML handler, left argument *)
val ml_handler_left : t

(** ML handler, righ argument*)
val ml_handler_right : t

(** ML type application *)
val ml_app : t

(** ML argument of a type application *)
val ml_app_arg : t

(** [t] in [forall a, t] *)
val ml_forall_r : t
