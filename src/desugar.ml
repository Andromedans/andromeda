(** Conversion from the input syntax to the abstract syntax. *)

(** During the desugaring phase we need to keep track of free variables, bound variables,
    and computational variables. *)

type 'a ident = Bound of 'a | Meta of 'a

type ctx = (Common.name ident) list

let empty = []

let add_bound x ctx = Bound x :: ctx
let add_meta x ctx = Met a :: ctx

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

let rec comp ctx (c',loc) =
  let w, c with =
    begin
      match c' with

      | Input.Let (x, c1, c2) ->
         let c1 = comp ctx c1
         and c2 = comp ctx c2
         in [], Syntax.Let (x, c1, c2)
                                      
      | Input.Ascribe (c, t) ->
         let w, t = expr t
         and c = comp c
         in w, Syntax.Ascribe (c, t)

      | (Input.Var _ | Input.Type) ->
         let w, e = expr ctx e
         in w, Syntax.Return e
                 
    end
  in match w with
     | [] -> c, loc
     | _ -> Syntax.Let (w, (c, loc)), loc

and expr ctx ((e',loc) as e) =
  match e' with
    | Input.Var x ->
       begin
         match lookup x ctx with
         | None -> [], (Syntax.Free x, loc)
         | Some (Bound k) -> [], (Syntax.Bound k, loc)
         | Some (Meta k) -> [], (Syntax.Meta k, loc)
       end

    | Input.Type ->
       [], (Syntax.Type, loc)

    | (Input.Let _ | Input.Ascribe _ | Input.Lambda | Input.Spine _ |
       Input.Prod _ | Input.Eq _ | Input.Refl _) ->
       let c = comp ctx e
       in [c], (fun k -> Syntax.Meta k, loc)
