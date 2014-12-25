(** Abstract syntax of computations and expressions. *)

type expr = expr' * Position.t
 and expr' =
   | Free of Common.name
   | Bound of Common.bound
   | Meta of Common.bound
   | Type

and ty = expr

and comp = comp' * Position.t
and comp' = 
  | Return of expr
  | Let of (Common.name * comp) list * comp
  | Ascribe of comp * ty
  | Lambda of (Common.name * ty) list * comp
  | Spine of expr * expr list
  | Prod of (Common.name * ty) list * comp
  | Eq of expr * expr
  | Refl of expr
