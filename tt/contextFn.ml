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
    decls : declaration list;
    ctx_depth : int;               (** Cached length of above lists *)
  }

  (** On the zeroth day there was the empty context. *)
  let empty_context = {
    names = [] ;
    decls = [] ;
    ctx_depth = 0;
  }

  (** Drop the most recently added thing from the context. *)
  let drop {names; decls; ctx_depth} =
    { names = List.tl names;
      decls = List.tl decls;
      ctx_depth = ctx_depth - 1;
    }

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
      decls = Parameter t :: ctx.decls;
      ctx_depth = ctx.ctx_depth + 1;
    }

  (** [add_parameters [(x1,t1); ...; (xn,tn)] ctx] returns [ctx] with the given
      parameters appended.

      Note that this is not the same as a nested series of calls to
      add_parameter, because we assume that all of t1, ..., tn are well-formed
      in (i.e., have de Bruijn indices relative to) ctx. For nested calls, we
      would need [ctx |- t1] but also [ctx, x1:t1 |- t2] and
      [ctx, x1:t1, x2:t2 |- t3] and so on.
   *)
  let add_parameters bnds ctx =
    let rec loop vars_added accum_ctx = function
      | []          -> accum_ctx
      | (x,t)::rest ->
          loop (vars_added+1)
               (add_parameter x (X.shift vars_added t) accum_ctx)
               rest
    in
       (loop 0 ctx bnds : context)



  (** [add_definition x t e ctx] returns [ctx] with [x] of type [t] defined as [e]. *)
  let add_definition x t e ctx =
    { names = x :: ctx.names ;
      decls = Definition (t, e) :: ctx.decls;
      ctx_depth = ctx.ctx_depth + 1;
    }

  let depth ctx = ctx.ctx_depth

  let print {names; decls; ctx_depth} =
    Format.printf "\n====vvv=====CONTEXT=====vvv====\n";
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
      names decls ctx_depth);
    Format.printf "----^^^===END CONTEXT===^^^====\n@.";
    ()

    (** [shift_to_ctx (gamma, term) delta] takes a term that
        is well-formed in context gamma, and shifts the indices
        so as to make it well-formed in context delta, which is
        assumed to be an extension of delta.
     *)
    let shift_to_ctx (ctx1, term) ctx2 =
      let depth1 = depth ctx1  in
      let depth2 = depth ctx2  in
      assert (depth1 <= depth2);
      X.shift (depth2 - depth1) term

end




