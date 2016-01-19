(** Desugared input syntax *)

(** Bound variables - represented by de Bruijn indices *)
type bound = int

(** Patterns *)

type tt_pattern = tt_pattern' * Location.t
and tt_pattern' =
  | Tt_Anonymous
  | Tt_As of tt_pattern * bound
  | Tt_Bound of bound
  | Tt_Type
  | Tt_Constant of Name.ident
  | Tt_Lambda of Name.ident * bound option * tt_pattern option * tt_pattern
  | Tt_Apply of tt_pattern * tt_pattern
  | Tt_Prod of Name.ident * bound option * tt_pattern option * tt_pattern
  | Tt_Eq of tt_pattern * tt_pattern
  | Tt_Refl of tt_pattern
  | Tt_Signature of (Name.ident * Name.ident * bound option * tt_pattern) list
  | Tt_Structure of (Name.ident * Name.ident * bound option * tt_pattern) list
  | Tt_Projection of tt_pattern * Name.ident

type pattern = pattern' * Location.t
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * bound
  | Patt_Bound of bound
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Tag of Name.ident * pattern list
  | Patt_Nil
  | Patt_Cons of pattern * pattern

(** Desugared computations *)
type comp = comp' * Location.t
and comp' =
  | Type
  | Bound of bound
  | Function of Name.ident * comp
  | Rec of Name.ident * Name.ident * comp
  | Handler of handler
  | Tag of Name.ident * comp list
  | Nil
  | Cons of comp * comp
  | Perform of Name.ident * comp list
  | With of comp * comp
  | Let of (Name.ident * comp) list * comp
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Assume of (Name.ident * comp) * comp
  | Where of comp * comp * comp
  | Match of comp * match_case list
  | Ascribe of comp * comp
  | Reduce of comp
  | External of string
  | Typeof of comp
  | Constant of Name.ident * comp list
  | Lambda of Name.ident * comp option * comp
  | Apply of comp * comp
  | Prod of Name.ident * comp * comp
  | Eq of comp * comp
  | Refl of comp
  | Signature of (Name.ident * Name.ident * comp) list
  | Structure of (Name.ident * Name.ident * comp) list
  | Projection of comp * Name.ident
  | Yield of comp
  | Context
  | Congruence of comp * comp
  | String of string

and handler = {
  handler_val: match_case list;
  handler_ops: multimatch_case list Name.IdentMap.t;
  handler_finally : match_case list;
}

and match_case = Name.ident list * pattern * comp

(** Match multiple patterns at once, with shared pattern variables *)
and multimatch_case = Name.ident list * pattern list * comp

(** Desugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Operation of Name.ident * int
  | Data of Name.ident * int
  | Axiom of Name.ident * (Name.ident * comp) list * comp (** introduce a constant *)
  | TopHandle of (Name.ident * (Name.ident list * comp)) list
  | TopLet of Name.ident * comp (** global let binding *)
  | TopDo of comp (** evaluate a computation *)
  | TopFail of comp
  | Verbosity of int
  | Include of string list * bool (** the boolean is [true] if the files should be included only once *)
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)

