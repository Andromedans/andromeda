(** Predefined external values. *)

let (>>=) = Runtime.bind

let externals =
  [
    ("print", (* forall a, a -> mlunit *)
     Runtime.mk_closure_external (fun v ->
         Runtime.lookup_penv >>= fun penv ->
         Format.printf "%t@." (Runtime.print_value ~penv v) ;
         Runtime.return_unit
    ));

    ("print_json", (* forall a, a -> mlunit *)
     Runtime.mk_closure_external (fun v ->
         let j = Runtime.Json.value v in
         (* Temporarily set printing depth to infinity *)
         let b = Format.get_max_boxes () in
         Format.set_max_boxes 0 ;
         Format.printf "%t@." (Json.print j) ;
         Format.set_max_boxes b ;
         Runtime.return_unit
    ));

    ("compare", (* forall a, a -> a -> ML.order *)
     Runtime.mk_closure_external (fun v ->
         Runtime.return_closure (fun w ->
             try
               let c = Stdlib.compare v w in
               Runtime.return
                 (if c < 0 then Reflect.mlless
                  else if c > 0 then Reflect.mlgreater
                  else Reflect.mlequal)
             with
             | Invalid_argument _ ->
                Runtime.(error ~at:Location.unknown InvalidComparison)
           )
    ));

    ("time", (* forall a, mlunit -> (a -> a) *)
     Runtime.mk_closure_external (fun _ ->
         let time0 = ref (Sys.time ()) in
         Runtime.return_closure
           (fun v ->
             let time1 = Sys.time () in
             Format.printf "Time used: %fs\n" (time1 -. !time0) ;
             Runtime.return v)
    ));

    ("config", (* mlstring -> mlunit *)
     Runtime.mk_closure_external (fun v ->
         let s = Runtime.as_string ~at:Location.unknown v in
         match s with
         | "ascii" ->
            Config.ascii := true;
            Runtime.return_unit

         | "no-ascii" ->
            Config.ascii := false;
            Runtime.return_unit

         | "json-location" ->
            Config.json_location := true;
            Runtime.return_unit

         | "no-json-location" ->
            Config.json_location := false;
            Runtime.return_unit

         | _ -> Runtime.(error ~at:Location.unknown (UnknownConfig s))
    ));

    ("eqchk_empty_checker", (* Eq.checker *)
     Runtime.(External (EqualityChecker Eqchk_equalizer.empty_checker)));

    ("exit", (* forall a, mlunit -> a *)
     Runtime.mk_closure_external (fun _ -> Stdlib.exit 0));

    ("magic", (* forall a b, a -> b *)
     Runtime.mk_closure_external (fun v -> Runtime.return v));
  ]

let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None
