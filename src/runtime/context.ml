(** The type of contexts *)
type t = {
  free : (Common.name * Value.ty) list;
  meta : (Common.name * Value.value) list
}

(** The empty context *)
let empty = { free = []; meta = [] }

let metas {meta=lst} = List.map fst lst

let lookup_free x {free=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Common.eqname x y then Some v else lookup lst
  in
    lookup lst

let lookup_bound k {free=lst} =
  try
    List.nth lst k
  with
  | Failure _ -> Error.runtime "invalid de Bruijn index %d" k

let lookup_meta k {meta=lst} =
  let rec lookup = function
    | _, [] -> None
    | 0, (_, v) :: _ -> Some v
    | k, _ :: xvs -> lookup (k-1, xvs)
  in
    lookup (k, lst)

let is_bound x ctx =
  match lookup_free x ctx with
  | None -> false
  | Some _ -> true

let add_free x t ctx =
  if is_bound x ctx
  then Error.runtime "%s already exists" (Common.to_string x)
  else { ctx with free = (x,t) :: ctx.free }

let add_fresh x t ctx =
  let y = Common.fresh x
  in y, { ctx with free = (y,t) :: ctx.free }

let add_meta x v ctx =
  { ctx with meta = (x,v) :: ctx.meta }

(* Variables which have a value are never referenced from anything with
   a context (because the context only holds evaluated things). So it is
   safe for such a variables to be shadowed. But we must never ever shadow
   a free variable because other parts of the context may refer to it. *)

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
    let (y, k) = split (Common.to_string x) in
    let k = ref (match k with Some k -> k | None -> 0) in
      while List.mem_assoc (Common.to_name (y ^ string_of_int !k)) ctx do incr k done ;
      Common.to_name (y ^ string_of_int !k)

let free_list {free} = free

let print ctx ppf =
  Print.print ppf "---------@." ;
  List.iter
    (fun (x, t) ->
     Print.print ppf "@[<hov 4>Parameter %t@;<1 -2>: %t@]@\n" (Common.print_name x) (Value.print_ty t))
    (List.rev (free_list ctx)) ;
  Print.print ppf "---END---@."
