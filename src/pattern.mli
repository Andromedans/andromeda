(** Patterns are common to desugared syntax and runtime syntax. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int

(** Judgement pattern. *)
type judgement = judgement' located
and judgement' =
  | TTAnonymous
  | TTVar of Name.t    (* XXX are the names used anywhere? *)
  | TTAs of judgement * judgement
  | TTConstructor of Ident.t * argument list
  | TTGenAtom of is_term
  | TTIsType of is_type
  | TTIsTerm of is_term * is_type
  | TTEqType of is_type * is_type
  | TTEqTerm of is_term * is_term * is_type
  | TTAbstract of Name.t option * is_type * judgement

and is_type = judgement
and is_term = judgement
and argument = judgement

(** ML pattern *)
type aml = aml' located
and aml' =
  | Anonymous
  | Var of Name.t
  | As of aml * aml
  | Judgement of judgement
  | MLConstructor of Ident.t * aml list
  | Tuple of aml list
