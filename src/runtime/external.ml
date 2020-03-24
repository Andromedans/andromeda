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

    ("exit", (* forall a, mlunit -> a *)
     Runtime.mk_closure_external (fun _ -> Stdlib.exit 0));

    ("magic", (* forall a b, a -> b *)
     Runtime.mk_closure_external (fun v -> Runtime.return v));

    ("Eqchk.empty_checker",
     Runtime.(External (EqualityChecker Eqchk.empty_checker)));

    ("Eqchk.add_type_computation",
     Runtime.mk_closure_external (fun chk ->
         Runtime.return_closure (fun der ->
             let chk = Runtime.as_equality_checker ~at:Location.unknown chk
             and drv = Runtime.as_derivation ~at:Location.unknown der in
             try
               let chk = Eqchk.add_type_computation chk drv in
               Runtime.return (Runtime.(External (EqualityChecker chk)))
             with
               | Eqchk_common.Invalid_rule err
               | Eqchk_common.Equality_fail err
               | Eqchk_pattern.Form_fail err ->
                 Reflect.eqchk_exception ~at:Location.unknown err
           )));

    ("Eqchk.add_term_computation",
     Runtime.mk_closure_external (fun chk ->
         Runtime.return_closure (fun der ->
             let chk = Runtime.as_equality_checker ~at:Location.unknown chk
             and drv = Runtime.as_derivation ~at:Location.unknown der in
             try
               let chk =  Eqchk.add_term_computation chk drv in
               Runtime.return Runtime.(External (EqualityChecker chk))
              with
               | Eqchk_common.Invalid_rule err
               | Eqchk_common.Equality_fail err
               | Eqchk_pattern.Form_fail err ->
                 Reflect.eqchk_exception ~at:Location.unknown err
           )));

    ("Eqchk.normalize_type",
     Runtime.mk_closure_external (fun strong ->
     Runtime.return_closure (fun chk ->
     Runtime.return_closure (fun t ->
       Runtime.lookup_signature >>= fun sgn ->
       let strong = Runtime.as_bool ~at:Location.unknown strong
       and chk = Runtime.as_equality_checker ~at:Location.unknown chk
       and t = Runtime.as_is_type ~at:Location.unknown t in
       let (t_eq_t', t') = Eqchk.normalize_type ~strong chk sgn t in
       let t_eq_t' = Nucleus.(abstract_not_abstract (JudgementEqType t_eq_t'))
       and t' = Nucleus.(abstract_not_abstract (JudgementIsType t')) in
       Runtime.(return (Tuple [Judgement t_eq_t'; Judgement t']))
       ))));

    ("Eqchk.normalize_term",
     Runtime.mk_closure_external (fun strong ->
     Runtime.return_closure (fun chk ->
     Runtime.return_closure (fun e ->
       Runtime.lookup_signature >>= fun sgn ->
       let strong = Runtime.as_bool ~at:Location.unknown strong
       and chk = Runtime.as_equality_checker ~at:Location.unknown chk
       and e = Runtime.as_is_term ~at:Location.unknown e in
       let (e_eq_e', e') = Eqchk.normalize_term ~strong chk sgn e in
       let e_eq_e' = Nucleus.(abstract_not_abstract (JudgementEqTerm e_eq_e'))
       and e' = Nucleus.(abstract_not_abstract (JudgementIsTerm e')) in
       Runtime.(return (Tuple [Judgement e_eq_e'; Judgement e']))
    ))));

    ("Eqchk.add_extensionality",
     Runtime.mk_closure_external (fun chk ->
         Runtime.return_closure (fun der ->
             let chk = Runtime.as_equality_checker ~at:Location.unknown chk
             and drv = Runtime.as_derivation ~at:Location.unknown der in
             try
               let chk = Eqchk.add_extensionality chk drv in
               Runtime.return Runtime.(External (EqualityChecker chk))
             with
               | Eqchk_common.Invalid_rule err
               | Eqchk_common.Equality_fail err
               | Eqchk_pattern.Form_fail err ->
                 Reflect.eqchk_exception ~at:Location.unknown err
    )));

    ("Eqchk.add",
     Runtime.mk_closure_external (fun chk ->
         Runtime.return_closure (fun der ->
             Runtime.lookup_nucleus_penv >>= fun penv ->
             let chk = Runtime.as_equality_checker ~at:Location.unknown chk
             and drv = Runtime.as_derivation ~at:Location.unknown der in
             try
               let chk =  Eqchk.add ~quiet:false ~penv chk drv in
               Runtime.return Runtime.(External (EqualityChecker chk))
             with
               | Eqchk_common.Invalid_rule err
               | Eqchk_common.Equality_fail err
               | Eqchk_pattern.Form_fail err ->
                 Reflect.eqchk_exception ~at:Location.unknown err
    )));

    ("Eqchk.prove_eq_type_abstraction",
     Runtime.mk_closure_external (fun chk ->
         Runtime.return_closure (fun bdry ->
             Runtime.lookup_signature >>= fun sgn ->
             let chk = Runtime.as_equality_checker ~at:Location.unknown chk
             and bdry = Runtime.as_boundary_abstraction ~at:Location.unknown bdry in
             match Nucleus.as_eq_type_boundary_abstraction bdry with
             | None -> failwith "some error about wrong use of prove_eq_type_abstraction"
             | Some bdry ->
                try
                  let eq = Eqchk.prove_eq_type_abstraction chk sgn bdry in
                  let eq = Nucleus.from_eq_type_abstraction eq in
                  Runtime.return Runtime.(Judgement eq)
                with
                  | Eqchk_common.Invalid_rule err
                  | Eqchk_common.Equality_fail err
                  | Eqchk_pattern.Form_fail err ->
                    Reflect.eqchk_exception ~at:Location.unknown err
    )));

    ("Eqchk.prove_eq_term_abstraction",
     Runtime.mk_closure_external (fun chk ->
         Runtime.return_closure (fun bdry ->
             Runtime.lookup_signature >>= fun sgn ->
             let chk = Runtime.as_equality_checker ~at:Location.unknown chk
             and bdry = Runtime.as_boundary_abstraction ~at:Location.unknown bdry in
             match Nucleus.as_eq_term_boundary_abstraction bdry with
             | None -> failwith "some error about wrong use of prove_eq_term_abstraction"
             | Some bdry ->
                try
                  let eq = Eqchk.prove_eq_term_abstraction chk sgn bdry in
                  let eq = Nucleus.from_eq_term_abstraction eq in
                  Runtime.return Runtime.(Judgement eq)
                 with
                  | Eqchk_common.Invalid_rule err
                  | Eqchk_common.Equality_fail err
                  | Eqchk_pattern.Form_fail err ->
                    Reflect.eqchk_exception ~at:Location.unknown err
    )));
  ]

let lookup s =
  try
    Some (List.assoc s externals)
  with
    Not_found -> None
