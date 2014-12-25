(** Conversion from the input syntax to the abstract syntax. *)

(** During the desugaring phase we need to keep track of free variables, bound variables,
    and computational variables. *)

type 'a ident = Bound of 'a | Meta of 'a

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

let lambdify ~loc ys c =
  match ys with
  | [] -> c, loc
  | _::_ -> Syntax.Lambda (ys, (c, loc)), loc

let prodify ~loc ys t =
  match ys with
  | [] -> t, loc
  | _::_ -> Syntax.Prod (ys, (t, loc)), loc

let letify ~loc w c =
  match w with
  | [] -> c, loc
  | _::_ -> Syntax.Let (w, (c, loc)), loc


let rec comp ctx (c',loc) =
  let w, c with =
    begin
      match c' with

      | Input.Let (x, c1, c2) ->
         let c1 = comp ctx c1
         and c2 = comp ctx c2
         in [], Syntax.Let (x, c1, c2)
                                      
      | Input.Ascribe (c, t) ->
         let w, t = expr ctx [] t
         and c = comp ctx c
         in w, Syntax.Ascribe (c, t)

      | Input.Lambda (xs, c) ->
         lambda ctx [] c xs

      | Input.Spine (e, es) ->
         let w, e = expr ctx [] e
         in let w, es = List.fold_left (fun (w, e) -> expr ctx w e) (w, []) es
            in w, Syntax.Spine (e, es)

      | Input.Prod (xs, c) ->
         prod ctx [] c xs

      | Input.Eq (e1, e2) ->
         let w, e1 = expr ctx [] e1
         in let w, e2 = expr ctx w e2
            in w, Syntax.Eq (e1, e2)

      | Input.Refl e ->
         let w, e = expr ctx e
         in w, Syntax.Refl e

      | (Input.Var _ | Input.Type) ->
         let w, e = expr ctx e
         in w, Syntax.Return e                 
    end

  in letify ~loc w c


and lambda ctx ys c' = function
  | [] -> 
     let c' = comp ctx c'
     in lambdify ys c'
  | (x,t) :: xs ->
     begin
       match expr ctx [] t with
       | [], t ->
          let ctx = add_bound x ctx
          and ys = (x,t) :: ys
          in lambda ctx ys c' xs
       | w, t ->
          let c = lambda (add_bound x ctx) [] c' xs
          in let c = Syntax.Lambda ([(x,t)], c)
             in let c = letify ~loc:(snd t) w c
                in lambdify ys c
     end

and prod ctx ys c' = function
  | [] -> 
     let c' = comp ctx c'
     in prodify ys c'
  | (x,t) :: xs ->
     begin
       match expr ctx [] t with
       | [], t ->
          let ctx = add_bound x ctx
          and ys = (x,t) :: ys
          in prod ctx ys t' xs
       | w, t ->
          let c = prod (add_bound x ctx) [] c' xs
          in let c = Syntax.Prod ([(x,t)], c)
             in let c = letify ~loc:(snd t) w c
                in prodify ys c
     end

and expr ctx w ((e',loc) as e) =
  match e' with
    | Input.Var x ->
       begin
         match lookup x ctx with
         | None -> w, (Syntax.Free x, loc)
         | Some (Bound k) -> w, (Syntax.Bound k, loc)
         | Some (Meta k) -> w, (Syntax.Meta k, loc)
       end

    | Input.Type ->
       w, (Syntax.Type, loc)

    | (Input.Let _ | Input.Ascribe _ | Input.Lambda | Input.Spine _ |
       Input.Prod _ | Input.Eq _ | Input.Refl _) ->
       let c = comp ctx e
       and k = List.length w in
       in w @ [c], (Syntax.Meta k, loc)
