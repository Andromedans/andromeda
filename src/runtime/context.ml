(** Typing context and runtime environment *)

(** A context holds free variables with their types and an
    environment of runtime bindings. *)
type t = {
  free : (Name.t * Tt.ty) list;
  bound : (Name.t * Value.value) list;
  beta : Hint.beta list ;
  eta : Hint.eta list
}

(** The empty context *)
let empty = { free = []; bound = [] ; beta = [] ; eta = [] }

let eta_hints {eta=lst} = lst

let beta_hints {beta=lst} = lst

let bound_names {bound=lst} = List.map fst lst

let used_names ctx = List.map fst ctx.free @ List.map fst ctx.bound

let lookup_free x {free=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq x y then Some v else lookup lst
  in
    lookup lst

let lookup_bound k {bound=lst} =
  try
    snd (List.nth lst k)
  with
  | Failure _ -> Error.runtime "invalid de Bruijn index %d" k

let is_bound x ctx =
  match lookup_free x ctx with
  | None -> false
  | Some _ -> true

let add_free x t ctx =
  if is_bound x ctx
  then Error.runtime "%t already exists" (Name.print x)
  else { ctx with free = (x,t) :: ctx.free }

let add_beta h ctx = { ctx with beta = h :: ctx.beta }

let add_eta h ctx = { ctx with eta = h :: ctx.eta }

let add_fresh x t ctx =
  let y = Name.fresh x
  in y, { ctx with free = (y,t) :: ctx.free }

let add_bound x v ctx =
  { ctx with bound = (x, v) :: ctx.bound }

let print ctx ppf =
  let forbidden_names = used_names ctx in
  Print.print ppf "---------@." ;
  List.iter
    (fun (x, t) ->
     Print.print ppf "@[<hov 4>Parameter %t@;<1 -2>: %t@]@\n" (Name.print x) (Tt.print_ty forbidden_names t))
    (List.rev ctx.free) ;
  Print.print ppf "---END---@."
