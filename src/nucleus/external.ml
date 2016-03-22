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

    ("print_signature", fun loc ->
      Runtime.return_closure (fun v ->
          let Jdg.Term (_,e,_) = Runtime.as_term ~loc v in
          match e.Tt.term with
            | Tt.Signature (s,_) ->
              Runtime.lookup_signature ~loc s >>= fun s_def ->
              Runtime.lookup_penv >>= fun penv ->
              Format.printf "%t = {@[<hv>%t@]}@." (Name.print_ident s) (Tt.print_sig_def ~penv:penv.Runtime.base s_def) ;
              Runtime.return_unit
            | _ -> Error.runtime ~loc "this term should be a signature"
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

          | _ -> Error.runtime ~loc "unknown config %s" s
        ));

    ("simplify", fun loc ->
      Runtime.return_closure (fun v ->
          Runtime.get_env >>= fun env ->
          let v = Simplify.value env v in
          Runtime.return v
        ));
  ]


let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None

