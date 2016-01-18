(** Predefined external values. *)

let (>>=) = Value.bind

(* An associative list mapping external names to their values.
   A typical external is a closure, which is made using [Value.mk_closure].
   A closure needs an environment, which for externals is the empty environment. *)
let externals =
  [
    ("print",
      Value.return_closure (fun v ->
          Value.print_value >>= fun pval ->
          Format.printf "%t@." (pval v) ;
          Value.return_unit
        )) ;

    ("time",
      Value.return_closure (fun _ ->
        let time = ref 0. in
        time := Sys.time ();
        Value.return_closure
            (fun v ->
              let t0 = !time in let t = Sys.time () in
              Format.printf "Time used: %fs\n" (t -. t0) ;
              Value.return v)
        ));
  ]


let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None
