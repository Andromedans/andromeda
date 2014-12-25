(** Abstract syntax of computations and expressions. *)

type expr = expr' * Position.loc
 and expr' =
   | Free of Common.name
   | Bound of Common.debruijn
   | Meta of Common.debruijn
   | Type

and ty = expr

and comp = comp' * Position.loc
and comp' = 
  | Return of expr
  | Let of (Common.name * comp) list * comp
  | Ascribe of comp * ty
  | Lambda of (Common.name * ty) list * comp
  | Spine of expr * expr list
  | Prod of (Common.name * ty) list * ty
  | Eq of expr * expr
  | Refl of expr
