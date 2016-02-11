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
  | Tt_Signature of Name.signature (* TODO easy matching of signatures and structures with constraints *)
  | Tt_Structure of Name.signature * tt_pattern list 
  | Tt_Projection of tt_pattern * Name.ident
  (** Matching [Signature s={li as xi : Ai} with lj = ej] is matching [((s,[li,xi:Ai]),[either yk or ej])]
      where [yk] is used to instantiate non-constrained labels in later constraints. *)
  | Tt_GenSig of pattern
  (** Matching [Structure s, [es]] *)
  | Tt_GenStruct of tt_pattern * pattern
  (** Matching [Projection e, _, l] *)
  | Tt_GenProj of tt_pattern * pattern
  | Tt_GenAtom

and pattern = pattern' * Location.t
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * bound
  | Patt_Bound of bound
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Data of Name.ident * pattern list
  | Patt_Nil
  | Patt_Cons of pattern * pattern
  | Patt_Tuple of pattern list

(** Desugared computations *)
type comp = comp' * Location.t
and comp' =
  | Type
  | Bound of bound
  | Function of Name.ident * comp
  | Rec of Name.ident * Name.ident * comp
  | Handler of handler
  | Data of Name.ident * comp list
  | Nil
  | Cons of comp * comp
  | Tuple of comp list
  | Operation of Name.ident * comp list
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
  | External of string
  | Constant of Name.ident
  | Lambda of Name.ident * comp option * comp
  | Apply of comp * comp
  | Prod of Name.ident * comp * comp
  | Eq of comp * comp
  | Refl of comp
  (** [s with li as xi = maybe ci] with every previous [xj] bound in [ci] (including the constrained ones) *)
  | Signature of Name.signature * (Name.ident * comp option) list
  (** [{ li as xi = maybe ci } : s with lj = ej] with previous [xj] bound in [ci].
      Must be evaluated in checking mode unless fully explicit. *)
  | Structure of Name.signature * (Name.ident * comp option) list
  | Projection of comp * Name.label
  | Yield of comp
  | Hypotheses
  | Congruence of comp * comp
  | Extensionality of comp * comp
  | Reduction of comp
  | String of string
  (** Inverts matching, except with just the name and not the definition of the signature *)
  | GenSig of comp * comp
  | GenStruct of comp * comp
  | GenProj of comp * comp
  | Occurs of comp * comp
  | Context of comp

and handler = {
  handler_val: match_case list;
  handler_ops: match_op_case list Name.IdentMap.t;
  handler_finally : match_case list;
}

and match_case = Name.ident list * pattern * comp

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = Name.ident list * pattern list * tt_pattern option * comp

type top_op_case = Name.ident list * Name.ident option * comp

(** Desugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | DeclOperation of Name.ident * int
  | DeclData of Name.ident * int
  | DeclConstants of Name.ident list * comp (** introduce constants *)
  | DeclSignature of Name.signature * (Name.label * Name.ident * comp) list
  | TopHandle of (Name.ident * top_op_case) list
  | TopLet of Name.ident * comp (** global let binding *)
  | TopDo of comp (** evaluate a computation *)
  | TopFail of comp
  | Verbosity of int
  | Include of string list * bool (** the boolean is [true] if the files should be included only once *)
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)

