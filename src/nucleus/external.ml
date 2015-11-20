(** Predefined external values. *)

let externals = [
  ("print",
   Value.Closure (fun v ->
                  Format.printf "%t@\n" (Value.print_value [] v) ;
                  Value.return (Value.Tag (Name.make "tt", []))
                 ))
]


let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None
