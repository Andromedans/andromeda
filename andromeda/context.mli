(* The representation type of typing contexts.
 *)
type t

type hint = int * Pattern.ty * Pattern.term * Pattern.term

(* The empty context
 *)
val empty : t

(* The list of names of variables in the context, not necessarily unique in the
 * presence of shadowing.
 *)
val names : t -> string list

(* Functionally extend the context with a new variable with the given name and
 * the given type. (This new variable will now be index 0, with all other
 * indices shifted up one.)
 *)
val add_var : Syntax.name -> Syntax.ty -> t -> t

(* Functionally extend the context with a series of variables with the given
 * names and types.
 *
 * Precondition: the types are well-formed (de Bruijn indexed) relative to
 * the *given* context, and hence the given types must not involve previous
 * variables being added at the same time.
 *)
val add_vars : (Syntax.name * Syntax.ty) list -> t -> t

val for_J : Syntax.ty -> Syntax.name -> Syntax.name -> Syntax.name -> Syntax.name -> t -> t * t

(* Add a variable with a definition to the context.  The type and definition
 * should be indexed relative to the given context.
 *)
val add_def : Syntax.name -> Syntax.ty -> Syntax.term -> t -> t

val add_equation : hint -> t -> t

val add_rewrite : hint -> t -> t

(* Look up the given name in the context. If found, return the type
 * (indexed relative to the given context) of the newest variable
 * of that name. If no such variable exists, throws an exception.
 *)
val lookup_var : Syntax.variable -> t -> Syntax.ty

(* Look up the given name in the context. If found, return the definition
 * (indexed relative to the given context) of the newest variable of that name.
 * If no such variable exists, throws an exception.
 *)
val lookup_def : Syntax.variable -> t -> Syntax.term option

(* Returns all the rewrite-rule hints in the given context.
 *)
val rewrites : t -> hint list

(* Returns all the equational hints in the given context.
 *)
val equations : t -> hint list

(* [append ctx1 ctx2] returns a context containing all the entries
 * in [ctx1] followed by the entries in [ctx2]. Note that it is
 * assumed that [ctx2] is already well-formed (shifted) with
 * respect to [ctx1]; this function does no further shifts of
 * de Bruijn indices.
 *)
val append : t -> t -> t

(* Display a context.
 *
 * The optional label is printed at the start and end of the context, which is
 * useful to identify the source of the context for debugging purposes
 *)
val print : ?label:string -> t -> unit

val pop_var : t -> t

val pop_vars: int -> t -> t

