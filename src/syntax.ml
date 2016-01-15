(** Desugared input syntax *)

(** Bound variables - represented by de Bruijn indices *)
type bound = int

(** Type-theory patterns *)
type tt_pattern = tt_pattern' * Location.t
and tt_pattern' =
  | Tt_Anonymous
  | Tt_As of tt_pattern * bound
  | Tt_Bound of bound
  | Tt_Type
  | Tt_Constant of Name.ident
  | Tt_Lambda of Name.ident * bound option * tt_pattern option * tt_pattern
  | Tt_App of tt_pattern * tt_pattern
  | Tt_Prod of Name.ident * bound option * tt_pattern option * tt_pattern
  | Tt_Eq of tt_pattern * tt_pattern
  | Tt_Refl of tt_pattern
  | Tt_Signature of (Name.ident * Name.ident * bound option * tt_pattern) list
  | Tt_Structure of (Name.ident * Name.ident * bound option * tt_pattern) list
  | Tt_Projection of tt_pattern * Name.ident

(** Programming-language patterns *)
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
and comp = comp' * Location.t
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
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of comp * comp list
  | Prod of (Name.ident * comp) list * comp
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
  | Axiom of Name.ident * (bool * (Name.ident * comp)) list * comp
  | TopHandle of (Name.ident * (Name.ident list * comp)) list
  | TopLet of Name.ident * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | Verbosity of int
  | Include of string list * bool (** the boolean is [true] if the files should be included only once *)
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)


let opt_map f = function
  | None -> None
  | Some x -> Some (f x)

let rec shift_tt_pattern k lvl ((p',loc) as p) =
  match p' with
    | Tt_Anonymous | Tt_Type | Tt_Constant _ -> p
    | Tt_As (p,k) ->
      let p = shift_tt_pattern k lvl p in
      Tt_As (p,k), loc
    | Tt_Bound m -> if m >= lvl then (Tt_Bound (m + k), loc) else p
    | Tt_Lambda (x,bopt,copt,c) ->
      let copt = opt_map (shift_tt_pattern k lvl) copt
      and c = shift_tt_pattern k (lvl+1) c in
      Tt_Lambda (x,bopt,copt,c), loc
    | Tt_App (c1,c2) ->
      let c1 = shift_tt_pattern k lvl c1
      and c2 = shift_tt_pattern k lvl c2 in
      Tt_App (c1,c2), loc
    | Tt_Prod (x,bopt,copt,c) ->
      let copt = opt_map (shift_tt_pattern k lvl) copt
      and c = shift_tt_pattern k (lvl+1) c in
      Tt_Prod (x,bopt,copt,c), loc
    | Tt_Eq (c1,c2) ->
      let c1 = shift_tt_pattern k lvl c1
      and c2 = shift_tt_pattern k lvl c2 in
      Tt_Eq (c1,c2), loc
    | Tt_Refl c ->
      let c = shift_tt_pattern k lvl c in
      Tt_Refl c, loc
    | Tt_Signature xcs ->
      let rec fold lvl xcs = function
        | [] ->
          let xcs = List.rev xcs in
          Tt_Signature xcs, loc
        | (l,x,bopt,c)::rem ->
          let c = shift_tt_pattern k lvl c in
          fold (lvl+1) ((l,x,bopt,c)::xcs) rem
        in
      fold lvl [] xcs
    | Tt_Structure xcs ->
      let rec fold lvl xcs = function
        | [] ->
          let xcs = List.rev xcs in
          Tt_Structure xcs, loc
        | (l,x,bopt,c)::rem ->
          let c = shift_tt_pattern k lvl c in
          fold (lvl+1) ((l,x,bopt,c)::xcs) rem
        in
      fold lvl [] xcs
    | Tt_Projection (c,l) ->
      let c = shift_tt_pattern k lvl c in
      Tt_Projection (c,l), loc

let rec shift_pattern k lvl ((p', loc) as p) =
  match p' with

    | Patt_Anonymous -> p

    | Patt_As (p, k) ->
      let p = shift_pattern k lvl p in
      Patt_As (p, k), loc

    | Patt_Bound m ->
       if m >= lvl then (Patt_Bound (m + k), loc) else p

    | Patt_Jdg (p1, p2) ->
      let p1 = shift_tt_pattern k lvl p1
      and p2 = shift_tt_pattern k lvl p2 in
      Patt_Jdg (p1, p2), loc

    | Patt_Tag (t, ps) ->
      let ps = List.map (shift_pattern k lvl) ps in
      Patt_Tag (t, ps), loc

    | Patt_Nil -> Patt_Nil, loc

    | Patt_Cons (p1, p2) ->
      let p1 = shift_pattern k lvl p1
      and p2 = shift_pattern k lvl p2 in
      Patt_Cons (p1, p2), loc


let rec shift_comp k lvl (c', loc) =
  let c' =
    match c' with

    | Bound m -> if m >= lvl then Bound (m + k) else c'

    | Function (x, c) -> Function (x, shift_comp k (lvl+1) c)

    | Rec (f, x, c) -> Rec (f, x, shift_comp k (lvl+2) c)

    | Handler h -> Handler (shift_handler k lvl h)

    | Tag (t, lst) -> Tag (t, List.map (shift_comp k lvl) lst)

    | Nil -> Nil

    | Cons (c1, c2) ->
       let c1 = shift_comp k lvl c1
       and c2 = shift_comp k lvl c2 in
       Cons (c1, c2)

    | Type -> c'

    | Perform (op, cs) ->
       let cs = List.map (shift_comp k lvl) cs in
       Perform (op, cs)

    | With (c1, c2) ->
       let c1 = shift_comp k lvl c1
       and c2 = shift_comp k lvl c2 in
       With (c1, c2)

    | Let (xcs, c) ->
       let xcs = List.map (fun (x,c) -> (x, shift_comp k lvl c)) xcs
       and c = shift_comp k (lvl + List.length xcs) c in
       Let (xcs, c)

    | Lookup c ->
       let c = shift_comp k lvl c in
       Lookup c

    | Update (c1, c2) ->
       let c1 = shift_comp k lvl c1
       and c2 = shift_comp k lvl c2 in
       Update (c1, c2)

    | Ref c ->
       let c = shift_comp k lvl c in
       Ref c

    | Sequence (c1, c2) ->
       let c1 = shift_comp k lvl c1
       and c2 = shift_comp k lvl c2 in
       Sequence (c1, c2)

    | Assume ((x, t), c) ->
       let t = shift_comp k lvl t
       and c = shift_comp k lvl c in
       Assume ((x, t), c)

    | Where (c1, c2, c3) ->
       let c1 = shift_comp k lvl c1
       and c2 = shift_comp k lvl c2
       and c3 = shift_comp k lvl c3 in
       Where (c1, c2, c3)

    | Match (c, lst) ->
      let c = shift_comp k lvl c
      and lst = List.map (shift_case k lvl) lst in
      Match (c, lst)

    | Ascribe (c1, c2) ->
       let c1 = shift_comp k lvl c1
       and c2 = shift_comp k lvl c2 in
       Ascribe (c1, c2)

    | Reduce c -> Reduce (shift_comp k lvl c)

    | External _ -> c'

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

    | Spine (c, cs) ->
       let c = shift_comp k lvl c
       and cs = List.map (shift_comp k lvl) cs in
       Spine (c, cs)

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

    | Signature lst ->
        let lst = List.map (fun (x,x',c) -> x, x', shift_comp k lvl c) lst in
        Signature lst

    | Structure lst ->
        let lst = List.map (fun (x, x',c) -> (x, x', shift_comp k lvl c)) lst in
        Structure lst

    | Projection (c,x) ->
        let c = shift_comp k lvl c in
        Projection (c,x)

    | Yield c ->
       let c = shift_comp k lvl c in
       Yield c

    | Context -> Context

    | Congruence (c1,c2) ->
      let c1 = shift_comp k lvl c1 in
      let c2 = shift_comp k lvl c2 in
      Congruence (c1,c2)

    | String s ->
      c'

  in
  c', loc

and shift_handler k lvl {handler_val; handler_ops; handler_finally} =
  { handler_val = List.map (shift_case k lvl) handler_val ;
    handler_ops = Name.IdentMap.map (List.map (shift_multicase k lvl)) handler_ops ;
    handler_finally = List.map (shift_case k lvl) handler_finally ;
  }

and shift_case k lvl (xs, p, c) =
  let p = shift_pattern k lvl p
  and c = shift_comp k (lvl + List.length xs) c in
  xs, p, c

and shift_multicase k lvl (xs, ps, c) =
  let ps = List.map (shift_pattern k lvl) ps
  and c = shift_comp k (lvl + List.length xs) c in
  xs, ps, c

