(** Predefined external values. *)

let (>>=) = Value.bind

(* An associative list mapping external names to their values.
   A typical external is a closure, which is made using [Value.mk_closure].
   A closure needs an environment, which for externals is the empty environment. *)
let externals =
  [
    ("print", fun loc ->
      Value.return_closure (fun v ->
          Value.print_value >>= fun pval ->
          Format.printf "%t@." (pval v) ;
          Value.return_unit
        )) ;

    ("print_signature", fun loc ->
      Value.return_closure (fun v ->
          let Jdg.Term (_,e,_) = Value.as_term ~loc v in
          match e.Tt.term with
            | Tt.Signature (s,_) ->
              Value.lookup_signature ~loc s >>= fun s_def ->
              Value.lookup_penv >>= fun penv ->
              Format.printf "%t = {@[<hv>%t@]}@." (Name.print_ident s) (Tt.print_sig_def ~penv s_def) ;
              Value.return_unit
            | _ -> Error.runtime ~loc "this term should be a signature"
        )) ;

    ("time", fun loc ->
      Value.return_closure (fun _ ->
        let time = ref 0. in
        time := Sys.time ();
        Value.return_closure
            (fun v ->
              let t0 = !time in let t = Sys.time () in
              Format.printf "Time used: %fs\n" (t -. t0) ;
              Value.return v)
        ));

    ("config", fun loc ->
      Value.return_closure (fun v ->
        let s = Value.as_string ~loc v in
        match s with
          | "ascii" ->
            Config.ascii := true;
            Value.return_unit
          | "no-ascii" ->
            Config.ascii := false;
            Value.return_unit

          | "debruijn" ->
            Config.debruijn := true;
            Value.return_unit
          | "no-debruijn" ->
            Config.debruijn := false;
            Value.return_unit

          | "annotate" ->
            Config.annotate := true;
            Value.return_unit
          | "no-annotate" ->
            Config.annotate := false;
            Value.return_unit

          | "dependencies" ->
            Config.print_dependencies := true;
            Value.return_unit
          | "no-dependencies" ->
            Config.print_dependencies := false;
            Value.return_unit

          | "subscripts" ->
            Config.print_subscripts := true;
            Value.return_unit
          | "no-subscripts" ->
            Config.print_subscripts := false;
            Value.return_unit

          | _ -> Error.runtime ~loc "unknown config %s" s
        ));

    ("simplify", fun loc ->
      Value.return_closure (fun v ->
          Value.get_env >>= fun env ->
          let v = Simplify.value env v in
          Value.return v
        ));

    ("random_choice", fun loc ->
        Value.return_closure (fun v1 ->
            Value.return_closure (fun v2 ->
                if Random.bool ()
                then Value.return v1
                else Value.return v2))
    );

  ]

let () = Random.self_init ()

let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None

