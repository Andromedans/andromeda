(** Predefined external values. *)

let (>>=) = Runtime.bind

let externals =
  [
    ("print", (* forall a, a -> mlunit *)
     Runtime.mk_closure (fun v ->
         Runtime.lookup_penv >>= fun penv ->
         Format.printf "%t@." (Runtime.print_value ~penv v) ;
         Runtime.return_unit
    ));

    ("print_json", (* forall a, a -> mlunit *)
     Runtime.mk_closure (fun v ->
         let j = Runtime.Json.value v in
         (* Temporarily set printing depth to infinity *)
         let b = Format.get_max_boxes () in
         Format.set_max_boxes 0 ;
         Format.printf "%t@." (Json.print j) ;
         Format.set_max_boxes b ;
         Runtime.return_unit
    ));

    ("time", (* forall a, mlunit -> (a -> a) *)
     Runtime.mk_closure (fun _ ->
         let time0 = ref (Sys.time ()) in
         Runtime.return_closure
           (fun v ->
             let time1 = Sys.time () in
             Format.printf "Time used: %fs\n" (time1 -. !time0) ;
             Runtime.return v)
    ));

    ("config", (* mlstring -> mlunit *)
      Runtime.mk_closure (fun v ->
        let s = Runtime.as_string ~loc:Location.unknown v in
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

          | _ -> Runtime.(error ~loc:Location.unknown (UnknownConfig s))
        ));

    ("exit", (* forall a, mlunit -> a *)
      Runtime.mk_closure (fun _ -> Pervasives.exit 0));

    ("magic", (* forall a b, a -> b *)
      Runtime.mk_closure (fun v -> Runtime.return v));
  ]


let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None
