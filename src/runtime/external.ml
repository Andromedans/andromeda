(** Predefined external values. *)

let (>>=) = Runtime.bind

(* An associative list mapping external names to their values.
   A typical external is a closure, which is made using [Runtime.mk_closure].
   A closure needs an environment, which for externals is the empty environment. *)
let externals =
  [
    ("print", fun loc ->
      Runtime.return_closure (fun v ->
          Runtime.lookup_penv >>= fun penv ->
          Format.printf "%t@." (Runtime.print_value ~penv v) ;
          Runtime.return_unit
        )) ;

    ("print_json", fun loc ->
      Runtime.return_closure (fun v ->
          let j = Runtime.Json.value v in
          Format.printf "%t@." (Json.print j) ;
          Runtime.return_unit
        )) ;

    ("time", fun loc ->
      Runtime.return_closure (fun _ ->
        let time = ref 0. in
        time := Sys.time ();
        Runtime.return_closure
            (fun v ->
              let t0 = !time in let t = Sys.time () in
              Format.printf "Time used: %fs\n" (t -. t0) ;
              Runtime.return v)
        ));

    ("config", fun loc ->
      Runtime.return_closure (fun v ->
        let s = Runtime.as_string ~loc v in
        match s with
          | "ascii" ->
            Config.ascii := true;
            Runtime.return_unit
          | "no-ascii" ->
            Config.ascii := false;
            Runtime.return_unit

          | "debruijn" ->
            Config.debruijn := true;
            Runtime.return_unit
          | "no-debruijn" ->
            Config.debruijn := false;
            Runtime.return_unit

          | "annotate" ->
            Config.annotate := true;
            Runtime.return_unit
          | "no-annotate" ->
            Config.annotate := false;
            Runtime.return_unit

          | "dependencies" ->
            Config.print_dependencies := true;
            Runtime.return_unit
          | "no-dependencies" ->
            Config.print_dependencies := false;
            Runtime.return_unit

          | _ -> Runtime.(error ~loc (UnknownConfig s))
        ));

    ("exit", fun _ ->
      Runtime.return_closure (fun _ ->
        exit 0))
  ]


let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None

