(** Context management *)
module Make (X : sig
                   type term
                   val shift : ?cut:int -> int -> term -> term
                   val print : ?max_level:int -> string list -> term ->
                     Format.formatter -> unit
                 end) =
struct

  (** A context is represented as an associative list which maps a variable [x] to a pair
      [(t,e)] where [t] is its type and [e] is its value (optional).
  *)

  (** The entries in the context are declarations of parameters or definitions.
      A parameter declaration carries its type, while a definition carries the type and
      the defining expression. *)
  type declaration =
    | Parameter of X.term
    | Definition of X.term * X.term (* classifier, defn. *)

  (** A context consists of a list of names, used for pretty-printing and
      desugaring of variable names to de Bruijn indices, and a list of
      declarations. *)
  type context = {
    names : string list ;
    decls : declaration list
  }

  (** On the zeroth day there was the empty context. *)
  let empty_context = {
    names = [] ;
    decls = []
  }

  (** Drop the most recently added thing from the context. *)
  let drop {names = ns; decls = ds} = {names = List.tl ns; decls = List.tl ds}

  let shift_entry ?(cut=0) delta =
    let shift = X.shift ~cut delta in
    function
    | Parameter  t      -> Parameter  (shift t)
    | Definition (t, e) -> Definition (shift t, shift e)

  (** [lookup v ctx] returns the type or definition of [Var v] in context [ctx]. *)
  let lookup v {decls=lst} =
    shift_entry (v+1) (List.nth lst v)

  (** [lookup_ty v ctx] returns the type of [Var v] in context [ctx]. *)
  let lookup_classifier v ctx =
    let entry = lookup v ctx in
    match entry with
    | Parameter t | Definition (t, _) -> t

  (** [lookup_definition v ctx] returns the definition of [Var v] in context [ctx]. *)
  let lookup_definition v ctx =
    let entry = lookup v ctx in
    match entry with
    | Definition (_, e) -> Some e
    | Parameter _       -> None

  (** [add_parameter x t ctx] returns [ctx] with the parameter [x] of type [t]. *)
  let add_parameter x t ctx =
    { names = x :: ctx.names ;
      decls = Parameter t :: ctx.decls }

  (** [add_definition x t e ctx] returns [ctx] with [x] of type [t] defined as [e]. *)
  let add_definition x t e ctx =
    { names = x :: ctx.names ;
      decls = Definition (t, e) :: ctx.decls }

  let print ctx =
    let names = ctx.names in
    let decls = ctx.decls in
    ignore
      (List.fold_right2
         (fun  x d k ->
            (match (shift_entry k d) with
             | Parameter t ->
                 Format.printf "@[%s : %t@]@." x (X.print names t)
             | Definition (t, e) ->
               Format.printf "@[%s := %t@]@\n    : %t@." x (X.print names e)
                 (X.print names t));
            k - 1)
         names decls (List.length names))

end




