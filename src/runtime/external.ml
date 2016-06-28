(** Predefined external values. *)

let (>>=) = Runtime.bind

let print_ty =
  let a = Mlty.fresh_param () in
  ([a], Mlty.Arrow (Mlty.Param a, Mlty.unit_ty))

let json_ty = print_ty

let time_ty =
  let a = Mlty.fresh_param () in
  ([a], Mlty.Arrow (Mlty.unit_ty, Mlty.Arrow (Mlty.Param a, Mlty.Param a)))

let config_ty =
  ([], Mlty.Arrow (Mlty.String, Mlty.unit_ty))

let exit_ty =
  let a = Mlty.fresh_param ()
  and b = Mlty.fresh_param () in
  ([a;b], Mlty.Arrow (Mlty.Param a, Mlty.Param b))

let magic_ty =
  let a = Mlty.fresh_param ()
  and b = Mlty.fresh_param () in
  ([a;b], Mlty.Arrow (Mlty.Param a, Mlty.Param b))

(* An associative list mapping external names to their values.
   A typical external is a closure, which is made using [Runtime.mk_closure].
   A closure needs an environment, which for externals is the empty environment. *)
let externals =
  [
    ("print",
      ((fun loc ->
      Runtime.return_closure (fun v ->
          Runtime.lookup_penv >>= fun penv ->
          Format.printf "%t@." (Runtime.print_value ~penv v) ;
          Runtime.return_unit
        )),
       print_ty));

    ("print_json",
      ((fun loc ->
      Runtime.return_closure (fun v ->
          let j = Runtime.Json.value v in
          (* Temporarily set printing depth to infinity *)
          let b = Format.get_max_boxes () in
          Format.set_max_boxes 0 ;
          Format.printf "%t@." (Json.print j) ;
          Format.set_max_boxes b ;
          Runtime.return_unit
        )),
      json_ty));

    ("time",
      ((fun loc ->
      Runtime.return_closure (fun _ ->
        let time = ref 0. in
        time := Sys.time ();
        Runtime.return_closure
            (fun v ->
              let t0 = !time in let t = Sys.time () in
              Format.printf "Time used: %fs\n" (t -. t0) ;
              Runtime.return v)
        )),
       time_ty));

    ("config",
      ((fun loc ->
      Runtime.return_closure (fun v ->
        let s = Runtime.as_string ~loc v in
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

          | _ -> Runtime.(error ~loc (UnknownConfig s))
        )),
       config_ty));

    ("exit",
      ((fun _ ->
      Runtime.return_closure (fun _ ->
        exit 0)),
      exit_ty));

    ("magic",
      ((fun _ ->
      Runtime.return_closure (fun v ->
        Runtime.return v)),
      magic_ty))
  ]


let lookup s =
  try
    Some (fst (List.assoc s externals))
  with
    Not_found -> None

let lookup_ty s =
  try
    Some (snd (List.assoc s externals))
  with
    Not_found -> None

