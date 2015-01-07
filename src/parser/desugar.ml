(** Conversion from the input syntax to the abstract syntax. *)

(** During the desugaring phase we need to keep track of free variables, bound variables,
    and computational variables. *)

type 'a ident = Bound of 'a | Meta of 'a

let rec string_of_ctx = function
  | [] -> ""
  | (Bound x) :: lst -> "Bound " ^ Common.to_string x ^ ", " ^ string_of_ctx lst
  | (Meta x) :: lst -> "Meta " ^ Common.to_string x ^ ", " ^ string_of_ctx lst


type ctx = (Common.name ident) list

let empty = []

let add_bound x ctx = Bound x :: ctx
let add_meta x ctx = Meta x :: ctx

let lookup x ctx =
  let rec lookup k_bound k_meta = function
    | [] -> None
    | Bound y :: lst ->
       if Common.eqname x y
       then Some (Bound k_bound)
       else lookup (k_bound+1) k_meta lst
    | Meta y :: lst ->
       if Common.eqname x y
       then Some (Meta k_bound)
       else lookup k_bound (k_meta+1) lst
  in
    lookup 0 0 ctx

let mk_lambda ys ((c',loc) as c) =
  match ys with
  | [] -> c'
  | _::_ -> Syntax.Lambda (ys, c)
                          
let prodify ys ((t',loc) as t) =
  match ys with
  | [] -> t'
  | _::_ -> Syntax.Prod (ys, t)

let letify ~loc w c' =
  match w with
  | [] -> c', loc
  | _::_ -> Syntax.Let (w, (c', loc)), loc

let rec comp ctx ((c',loc) as c) =
  let w, c =
    begin
      match c' with

      | Input.Let (ls, c2) ->
         let ls = List.map (fun (x,c) -> (x, comp ctx c)) ls in
         let ctx = List.fold_left (fun ctx (x,_) -> add_meta x ctx) ctx ls in
         let c2 = comp ctx c2
         in [], Syntax.Let (ls, c2)
                           
      | Input.Ascribe (c, t) ->
         let c = comp ctx c
         and w, t = expr ctx [] t
         in w, Syntax.Ascribe (c, t)

      | Input.Lambda (xs, c) ->
         let rec lambda ctx ys = function
           | [] -> 
              let c = comp ctx c in
                mk_lambda ys c
           | (x,t) :: xs ->
              begin
                match expr ctx [] t with
                | [], t ->
                   let ctx = add_bound x ctx
                   and ys =  ys @ [(x,t)]
                   in lambda ctx ys xs
                | w, ((_,loc) as t) ->
                   let c = lambda (add_bound x ctx) [] xs in
                   let c = Syntax.Lambda ([(x,t)], (c, loc)) in
                   let c = letify ~loc w c in
                     mk_lambda ys c
              end
         in
           [], lambda ctx [] xs

      | Input.Spine (e, es) ->
         let w, e = expr ctx [] e
         in let w, es =
              List.fold_left
                (fun (w,es) e -> let w, e = expr ctx w e
                                 in (w, e::es))
                (w, []) es
            in let es = List.rev es
               in w, Syntax.Spine (e, es)

      | Input.Prod (xs, c) ->
         let rec prod ctx ys = function
           | [] -> 
              let c = comp ctx c in
                prodify ys c
           | (x,t) :: xs ->
              begin
                match expr ctx [] t with
                | [], t ->
                   let ctx = add_bound x ctx
                   and ys = ys @ [(x,t)] in
                   prod ctx ys xs
                | w, ((_,loc) as t) ->
                   let c = prod (add_bound x ctx) [] xs in
                   let c = Syntax.Prod ([(x,t)], (c,loc)) in
                   let c = letify ~loc:(snd t) w c in
                     prodify ys c
              end
         in
           [], prod ctx [] xs

      | Input.Eq (e1, c2) ->
         let w, e1 = expr ctx [] e1
         in let c2 = comp ctx c2
            in w, Syntax.Eq (e1, c2)

      | Input.Refl e ->
         let w, e = expr ctx [] e
         in w, Syntax.Refl e

      | (Input.Var _ | Input.Type) ->
         let w, e = expr ctx [] c
         in w, Syntax.Return e                 
    end

    in letify ~loc w c

and expr ctx w ((e',loc) as e) =
  match e' with
    | Input.Var x ->
       begin
         match lookup x ctx with
         | None -> w, (Syntax.Name x, loc)
         | Some (Bound k) -> w, (Syntax.Bound k, loc)
         | Some (Meta k) -> w, (Syntax.Meta k, loc)
       end

    | Input.Type ->
       w, (Syntax.Type, loc)

    | (Input.Let _ | Input.Ascribe _ | Input.Lambda _ | Input.Spine _ |
       Input.Prod _ | Input.Eq _ | Input.Refl _) ->
       let x = Common.fresh Common.anonymous
       and c = comp ctx e
       and k = List.length w
       in w @ [(x,c)], (Syntax.Meta k, loc)

let toplevel metas (d, loc) =
  let ctx = List.map (fun x -> Meta x) metas in
  begin
    match d with

    | Input.Parameter (xs, t) ->
       let c = comp ctx t
       in Syntax.Parameter (xs, c)

    | Input.TopLet (x, c) ->
       let c = comp ctx c
       in Syntax.TopLet (x, c)

    | Input.TopCheck c ->
       let c = comp ctx c
       in Syntax.TopCheck c

    | Input.Quit -> Syntax.Quit

    | Input.Help -> Syntax.Help

    | Input.Context -> Syntax.Context
  end,
  loc

let computation = comp []

