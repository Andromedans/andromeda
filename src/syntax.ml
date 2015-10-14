(** Desugared input syntax *)

(** Bound variables - represented by de Bruijn indices *)
type bound = int

(** Desugared expressions *)
type expr = expr' * Location.t
and expr' =
  | Type
  | Bound of bound
  | Function of Name.ident * comp
  | Handler of handler

(** Desugared types - indistinguishable from expressions *)
and ty = expr

(** Desugared computations *)
and comp = comp' * Location.t
and comp' =
  | Return of expr
  | Operation of string * expr
  | With of expr * comp
  | Let of (Name.ident * comp) list * comp
  | Assume of Name.ident option * comp
  | Apply of expr * expr
  | Beta of (string list * comp) list * comp
  | Eta of (string list * comp) list * comp
  | Hint of (string list * comp) list * comp
  | Inhabit of (string list * comp) list * comp
  | Unhint of string list * comp
  | Ascribe of comp * comp
  | Whnf of comp
  | Typeof of comp
  | Constant of Name.ident * comp list
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of expr * comp list (* spine arguments are computations because we want
                                 to evaluate in checking mode, once we know their types. *)
  | Prod of (Name.ident * comp) list * comp
  | Eq of comp * comp
  | Refl of comp
  | Bracket of comp
  | Inhab

and handler = {
  handler_val: (Name.ident * comp) option;
  handler_ops: (string * (Name.ident * Name.ident * comp)) list;
  handler_finally : (Name.ident * comp) option;
}

(** Desugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Axiom of Name.ident * (bool * (Name.ident * comp)) list * comp
  | TopLet of Name.ident * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | TopBeta of (string list * comp) list
  | TopEta of (string list * comp) list
  | TopHint of (string list * comp) list
  | TopInhabit of (string list * comp) list
  | TopUnhint of string list
  | Verbosity of int
  | Include of string list
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)

let rec shift_comp k lvl (c', loc) =
  let c' =
    match c' with

    | Return e ->
       let e = shift_expr k lvl e in
       Return e

    | Operation (op, e) ->
       let e = shift_expr k lvl e in
       Operation (op, e)

    | With (e, c) ->
       let c = shift_comp k lvl c
       and e = shift_expr k lvl e in
       With (e, c)

    | Let (xcs, c) ->
       let xcs = List.map (fun (x,c) -> (x, shift_comp k lvl c)) xcs
       and c = shift_comp k (lvl + List.length xcs) c in
       Let (xcs, c)

    | Assume (xopt, c) ->
       let c = shift_comp k lvl c in
       Assume (xopt, c)

    | Apply (e1, e2) ->
       let e1 = shift_expr k lvl e1
       and e2 = shift_expr k lvl e2 in
       Apply (e1, e2)

    | Beta (xscs, c) ->
       let xscs = List.map (fun (xs, c) -> (xs, shift_comp k lvl c)) xscs
       and c = shift_comp k lvl c in
       Beta (xscs, c)

    | Eta (xscs, c) ->
       let xscs = List.map (fun (xs, c) -> (xs, shift_comp k lvl c)) xscs
       and c = shift_comp k lvl c in
       Eta (xscs, c)

    | Hint (xscs, c) ->
       let xscs = List.map (fun (xs, c) -> (xs, shift_comp k lvl c)) xscs
       and c = shift_comp k lvl c in
       Hint (xscs, c)

    | Inhabit (xscs, c) ->
       let xscs = List.map (fun (xs, c) -> (xs, shift_comp k lvl c)) xscs
       and c = shift_comp k lvl c in
       Inhabit (xscs, c)

    | Unhint (xs, c) ->
       let c = shift_comp k lvl c in
       Unhint (xs, c)

    | Ascribe (c1, c2) ->
       let c1 = shift_comp k lvl c1
       and c2 = shift_comp k lvl c2 in
       Ascribe (c1, c2)

    | Whnf c -> Whnf (shift_comp k lvl c)

    | Typeof c -> Typeof (shift_comp k lvl c)

    | Constant (x, cs) ->
       let cs = List.map (shift_comp k lvl) cs in
       Constant (x, cs)

    | Lambda (xcs, c) ->
       let rec fold lvl xcs' = function
         | [] ->
            let xcs' = List.rev xcs'
            and c = shift_comp k lvl c in
            Lambda (xcs', c)
         | (x,copt) :: xcs ->
            let copt = (match copt with None -> None | Some c -> Some (shift_comp k lvl c)) in
            fold (lvl+1) ((x,copt) :: xcs') xcs
       in
       fold lvl [] xcs

    | Spine (e, cs) ->
       let e = shift_expr k lvl e
       and cs = List.map (shift_comp k lvl) cs in
       Spine (e, cs)

    | Prod (xes, c) ->
       let rec fold lvl xes' = function
         | [] ->
            let xes' = List.rev xes'
            and c = shift_comp k lvl c in
            Prod (xes', c)
         | (x,c) :: xes ->
            let c = shift_comp k lvl c in
            fold (lvl+1) ((x,c) :: xes') xes
       in
       fold lvl [] xes

    | Eq (c1, c2) ->
       let c1 = shift_comp k lvl c1
       and c2 = shift_comp k lvl c2 in
       Eq (c1, c2)

    | Refl c ->
        let c = shift_comp k lvl c in
        Refl c

    | Bracket c ->
        let c = shift_comp k lvl c in
        Bracket c

    | Inhab -> Inhab
  in
  c', loc

and shift_handler k lvl {handler_val; handler_ops; handler_finally} =
  { handler_val =
      (match handler_val with
       | None -> None
       | Some (x, c) -> let c = shift_comp k (lvl+1) c in Some (x, c)) ;
    handler_ops =
      List.map
        (fun (op, (x, y, c)) -> let c = shift_comp k (lvl+2) c in (op, (x, y, c)))
        handler_ops ;
    handler_finally =
      (match handler_finally with
       | None -> None
       | Some (x, c) -> let c = shift_comp k (lvl+1) c in Some (x, c)) ;
  }

and shift_expr k lvl ((e', loc) as e) =
  match e' with
  | Bound m -> if m >= lvl then (Bound (m + k), loc) else e
  | Function (x, c) -> Function (x, shift_comp k (lvl+1) c), loc
  | Handler h -> Handler (shift_handler k lvl h), loc
  | Type -> e
