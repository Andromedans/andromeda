(** Patterns are common to desugared syntax and runtime syntax. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int

(** Judgement pattern. *)
type judgement = judgement' located
and judgement' =
  | TTAnonymous
  | TTVar of Name.ident    (* XXX are the idents used anywhere? *)
(*   | TTInterpolate of bound *)
  | TTAs of judgement * judgement
  | TTConstructor of Name.constructor * argument list
  | TTGenAtom of is_term
  | TTIsTerm of is_term * is_type
  | TTEqType of is_type * is_type
  | TTEqTerm of is_term * is_term * is_type
  | TTAbstract of Name.ident * is_type * judgement

and is_type = judgement
and is_term = judgement
and argument = judgement

(** AML pattern *)
type aml = aml' located
and aml' =
  | Anonymous
  | Var of Name.ident
(*   | Interpolate of bound *)
  | As of aml * aml
  | Judgement of judgement
  | AMLConstructor of Name.ident * aml list
  | Tuple of aml list
