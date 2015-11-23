(** Predefined external values. *)

let externals =
  [
    ("print",
     Value.Closure (fun v ->
         Format.printf "%t@\n" (Value.print_value [] v) ;
         Value.return (Value.Tag (Name.make "tt", []))
       )) ;
    ("time",
     let time = ref 0. in
     Value.Closure (fun _ ->
         time := Sys.time ();
         Value.return
           (Value.Closure
              (fun v ->
                 let t0 = !time in let t = Sys.time () in
                 Format.printf "Time used: %fs\n" (t -. t0) ;
                 Value.return v))
       ));
  ]


let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None
