(** Predefined external values. *)

(* An associative list mapping external names to their values.
   A typical external is a closure, which is made using [Value.mk_closure].
   A closure needs an environment, which for externals is the empty environment. *)
let externals =
  [
    ("print",
     Value.mk_closure Value.Env.empty (fun _ v ->
         Format.printf "%t@\n" (Value.print_value [] v) ;
         Value.return_unit
       )) ;
    ("time",
     Value.mk_closure Value.Env.empty (fun _ _ ->
         let time = ref 0. in
         time := Sys.time ();
         Value.return
           (Value.mk_closure Value.Env.empty
              (fun _ v ->
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
