(** Typing context and runtime environment *)

(** A context holds free variables with their types and an
    environment of runtime bindings. Free variables are
    accessed by their names and bound variables by de Bruijn
    indices. *)
type t = {
  free : (Name.t * Tt.ty) list;
  bound : (Name.t * Value.value) list
}

(** The empty context *)
let empty = { free = []; bound = [] }

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

let add_fresh x t ctx =
  let y = Name.fresh x
  in y, { ctx with free = (y,t) :: ctx.free }

let add_bound x v ctx =
  { ctx with bound = (x, v) :: ctx.bound }

(** Given a variable [x] and a context [ctx], find a variant of [x] which
    does not appear in [ctx]. *)
let find_name x ctx =
  (** Split a variable name into base and numerical postfix, e.g.,
      ["x42"] is split into [("x", 42)]. *)
  let split s =
    let n = String.length s in
    let i = ref (n - 1) in
      while !i >= 0 && '0' <= s.[!i] && s.[!i] <= '9' do decr i done ;
      if !i < 0 || !i = n - 1
      then (s, None)
      else
        let k = int_of_string (String.sub s (!i+1) (n - !i - 1)) in
          (String.sub s 0 (!i+1), Some k)
  in
  if not (List.mem_assoc x ctx)
  then x
  else
    let (y, k) = split (Name.to_string x) in
    let k = ref (match k with Some k -> k | None -> 0) in
      while List.mem_assoc (Name.of_string (y ^ string_of_int !k)) ctx do incr k done ;
      Name.of_string (y ^ string_of_int !k)

let print ctx ppf =
  let forbidden_names = used_names ctx in
  Print.print ppf "---------@." ;
  List.iter
    (fun (x, t) ->
     Print.print ppf "@[<hov 4>Parameter %t@;<1 -2>: %t@]@\n" (Name.print x) (Tt.print_ty forbidden_names t))
    (List.rev ctx.free) ;
  Print.print ppf "---END---@."
