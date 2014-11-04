type context_entry =
  | Entry_free of Syntax.ty        (* a free name *)
  | Entry_value of Syntax.value    (* a variable bound by a [let] *)

type t = (Common.name * context_entry) list

let empty = []

let names : t -> Common.name list = List.map fst

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

(* Variables which have a value are never referenced from anything with
   a context (because the context only holds evaluated things). So it is
   safe for such a variables to be shadowed. But we must never ever shadow
   a free variable because other parts of the context may refer to it. *)

let add_free x t ctx =
  if is_free x ctx then Error.fatal "%s is already assumed" x ;
  (x, Entry_free t) :: ctx

let add_fresh x t ctx =



let add_value x v ctx =
  if is_free x ctx then Error.fatal "%s is already assumed" x ;
  (x, Entry_value v) :: ctx

let print ctx =
  let xs = names ctx in
  Format.printf "---------@." ;
  List.iter (fun (x, entry) ->
    match entry with
      | Entry_free t ->
        Format.printf "@[<hov 4>Parameter %s@;<1 -2>: %t@]@\n" x (Print.ty xs t)
      | Entry_value v ->
        Format.printf "@[<hov 4>Let %s@;<1 -2>:= %t@]@\n" x (Print.value xs v)
  ) ctx ;
  Format.printf "---END---@."
