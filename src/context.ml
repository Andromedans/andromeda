type entry =
  | Entry_free of Syntax.ty        (* a free variable *)
  | Entry_value of Syntax.value    (* a variable bound by a [let] *)

(** The type of contexts *)
type t = (Common.name * entry) list

(** The empty context *)
let empty = []

let rec lookup x = function
  | [] -> None
  | (y,v) :: lst ->
    if Common.eqname x y then Some v else lookup x lst

let is_free x ctx =
  match lookup x ctx with
    | None -> false
    | Some (Entry_free _) -> true
    | Some (Entry_value _) -> false

let is_value x ctx =
  match lookup x ctx with
    | None -> false
    | Some (Entry_free _) -> false
    | Some (Entry_value _) -> true

let is_bound x ctx =
  match lookup x ctx with
    | None -> false
    | Some _ -> true

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

let add_free x ((_,loc) as t) ctx =
  let x = find_name x ctx in
  let ctx = (x, Entry_free t) :: ctx in
    x, ctx

let add_value x v ctx =
  if x = Common.anonymous
  then ctx
  else begin
    if is_free x ctx then Error.fatal "%s is already assumed" (Common.to_string x) ;
    (x, Entry_value v) :: ctx
  end
