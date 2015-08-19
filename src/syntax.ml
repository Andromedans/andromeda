(** Desugared input syntax *)

(** Bound variables - represented by de Bruijn indices *)
type bound = int

(** Desugared expressions *)
type expr = expr' * Location.t
and expr' =
  | Bound of bound
  | Function of Name.t * comp
  | Type

(** Desugared types - indistinguishable from expressions *)
and ty = expr

(** Desugared computations *)
and comp = comp' * Location.t
and comp' =
  | Return of expr
  | Operation of string * expr
  | Let of (Name.t * comp) list * comp
  | Apply of expr * expr
  | Beta of (string list * comp) list * comp
  | Eta of (string list * comp) list * comp
  | Hint of (string list * comp) list * comp
  | Inhabit of (string list * comp) list * comp
  | Unhint of string list * comp
  | Ascribe of comp * ty
  | Whnf of comp
  | PrimApp of Name.t * comp list
  | Lambda of (Name.t * comp option) list * comp
  | Spine of expr * comp list (* spine arguments are computations because we want
                                 to evaluate in checking mode, once we know their types. *)
  | Prod of (Name.t * ty) list * comp (* XXX turn the ty into comp *)
  | Eq of comp * comp
  | Refl of comp
  | Bracket of comp
  | Inhab

(** Desugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Primitive of Name.t list * (Name.t * bool * comp) list * comp (** introduce a primitive operation *)
  | TopLet of Name.t * comp (** global let binding *)
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
  | Context (** print the current context *)

let rec shift_comp k lvl (c', loc) =
  let c' =
    match c' with

    | Return e ->
       let e = shift_expr k lvl e in
       Return e

    | Operation (op, e) -> 
       let e = shift_expr k lvl e in
       Operation (op, e)

    | Let (xcs, c) ->
       let xcs = List.map (fun (x,c) -> (x, shift_comp k lvl c)) xcs
       and c = shift_comp k (lvl + List.length xcs) c in
       Let (xcs, c)
     
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

    | Ascribe (c, e) -> 
       let c = shift_comp k lvl c
       and e = shift_expr k lvl e in
       Ascribe (c, e)

    | Whnf c -> Whnf (shift_comp k lvl c)

    | PrimApp (x, cs) ->
       let cs = List.map (shift_comp k lvl) cs in
       PrimApp (x, cs)

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
         | (x,e) :: xes ->
            let e = shift_expr k lvl e in
            fold (lvl+1) ((x,e) :: xes') xes
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

and shift_expr k lvl ((e', loc) as e) =
  match e' with
  | Bound m -> if m >= lvl then (Bound (m + k), loc) else e
  | Function (x, c) -> Function (x, shift_comp k (lvl+1) c), loc
  | Type -> e
