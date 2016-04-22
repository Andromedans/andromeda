(** Equality checking and weak-head-normal-forms *)

(** An option monad on top of Runtime.comp, which only uses Runtime.bind when necessary. *)
module Opt = struct
  type 'a opt =
    { k : 'r. ('a -> 'r Runtime.comp) -> 'r Runtime.comp -> 'r Runtime.comp }

  let return x =
    { k = fun sk _ -> sk x }

  let (>?=) m f =
    { k = fun sk fk -> m.k (fun x -> (f x).k sk fk) fk }

  let lift (m : 'a Runtime.comp) : 'a opt =
    { k = fun sk _ -> Runtime.bind m sk }

  let fail =
    { k = fun _ fk -> fk }

  let add_abstracting v m =
    { k = fun sk fk ->
          Predefined.add_abstracting v (m.k sk fk) }

  let run m =
    m.k (fun x -> Runtime.return (Some x)) (Runtime.return None)
end

(*
let (>>=) = Runtime.bind
*)

let (>?=) = Opt.(>?=)

let (>!=) m f = (Opt.lift m) >?= f

module Internals = struct

(** Compare two types *)
let equal ~loc j1 j2 =
  match Jdg.alpha_equal_eq_term ~loc j1 j2 with
    | Some eq -> Opt.return eq
    | None ->
      Predefined.operation_equal ~loc j1 j2 >!= begin function
        | Some juser ->
          Runtime.lookup_typing_env >!= fun env ->
          let target = Jdg.form_ty ~loc env (Jdg.Eq (j1, j2)) in
          begin match Jdg.alpha_equal_eq_ty ~loc target (Jdg.typeof juser) with
            | Some _ -> 
              let eq = Jdg.reflect juser in
              Opt.return eq
            | None -> Opt.lift (Runtime.(error ~loc (InvalidEqual target)))
          end
        | None -> Opt.fail
      end

let equal_ty ~loc j1 j2 =
  equal ~loc (Jdg.term_of_ty j1) (Jdg.term_of_ty j2) >?= fun eq ->
  let eq = Jdg.is_type_equality eq in
  Opt.return eq

let coerce ~loc je jt =
  let je_ty = Jdg.typeof je in
  match Jdg.alpha_equal_eq_ty ~loc je_ty jt with

  | Some _ ->
     Opt.return je
                  
  | None ->
     Predefined.operation_coerce ~loc je jt >!=
       begin function

       | Predefined.NotCoercible -> Opt.fail

       | Predefined.Convertible eq ->
          let eq_lhs = Jdg.eq_ty_side Jdg.LEFT eq
          and eq_rhs = Jdg.eq_ty_side Jdg.RIGHT eq in
          begin
            match Jdg.alpha_equal_eq_ty ~loc je_ty eq_lhs,
                  Jdg.alpha_equal_eq_ty ~loc jt eq_rhs
            with
            | Some _, Some _ ->
               Opt.return (Jdg.convert ~loc je eq)
            | (None, Some _ | Some _, None | None, None) ->
               Runtime.(error ~loc (InvalidConvertible (je_ty, jt, eq)))
          end

       | Predefined.Coercible je ->
          begin
            match Jdg.alpha_equal_eq_ty ~loc (Jdg.typeof je) jt with
            | Some _ ->
               Opt.return je
            | None ->
               Runtime.(error ~loc (InvalidCoerce (jt, je)))
          end
       end
  

let coerce_fun ~loc je =
  let jt = Jdg.typeof je in
  match Jdg.shape_prod jt with

  | Some (a, b) -> Opt.return (je, a, b)

  | None ->
     Predefined.operation_coerce_fun ~loc je >!=
     begin function

       | Predefined.NotCoercible ->
          Opt.fail

       | Predefined.Convertible eq ->
          let eq_lhs = Jdg.eq_ty_side Jdg.LEFT eq
          and eq_rhs = Jdg.eq_ty_side Jdg.RIGHT eq in
          begin
            match Jdg.alpha_equal_eq_ty ~loc jt eq_lhs with
              | Some _ ->
                 begin
                   match Jdg.shape_prod eq_rhs with
                   | Some (a, b) ->
                      let je = Jdg.convert ~loc je eq in
                      Opt.return (je, a, b)
                   | None ->
                      Runtime.(error ~loc (InvalidFunConvertible (jt, eq)))
                 end
                 
              | None ->
                 Runtime.(error ~loc (InvalidFunConvertible (jt, eq)))
          end
          
       | Predefined.Coercible je ->
          begin
            let jt = Jdg.typeof je in
            match Jdg.shape_prod jt with
            | Some (a, b) ->
               Opt.return (je, a, b)
            | None ->
               Runtime.(error ~loc (InvalidFunCoerce je))
          end
          
     end
     

(** Apply the appropriate congruence rule *)
let congruence ~loc j1 j2 =
  Runtime.lookup_typing_env >!= fun env ->
  let at_ty = Jdg.natural_eq ~loc env j1 in
  begin match Jdg.shape j1, Jdg.shape j2 with

  | Jdg.Type, Jdg.Type | Jdg.Atom _, Jdg.Atom _ | Jdg.Constant _, Jdg.Constant _ ->
    begin match Jdg.alpha_equal_eq_term ~loc j1 j2 with
      | Some eq -> Opt.return eq
      | None -> Opt.fail
    end

  | Jdg.Prod (a1, b1), Jdg.Prod (a2, b2) ->
    let ta1 = Jdg.atom_ty a1
    and ta2 = Jdg.atom_ty a2 in
    equal_ty ~loc ta1 ta2 >?= fun eq_a ->
    let a1_ta2 = Jdg.convert ~loc (Jdg.atom_term ~loc a1) eq_a in
    let b2 = Jdg.substitute_ty ~loc b2 a2 a1_ta2 in
    Opt.add_abstracting (Jdg.atom_term ~loc a1)
    (equal_ty ~loc b1 b2 >?= fun eq_b ->
    let eq = Jdg.congr_prod ~loc ~at_ty eq_a a1 a2 eq_b in
    Opt.return eq)

  | Jdg.Lambda (a1, e1), Jdg.Lambda (a2, e2) ->
    let ta1 = Jdg.atom_ty a1
    and ta2 = Jdg.atom_ty a2 in
    equal_ty ~loc ta1 ta2 >?= fun eq_a ->
    let a1_ta2 = Jdg.convert ~loc (Jdg.atom_term ~loc a1) eq_a in
    let e2 = Jdg.substitute ~loc e2 a2 a1_ta2 in
    let b1 = Jdg.typeof e1
    and b2 = Jdg.typeof e2 in
    Opt.add_abstracting (Jdg.atom_term ~loc a1)
    (equal_ty ~loc b1 b2 >?= fun eq_b ->
    let e2 = Jdg.convert ~loc e2 (Jdg.symmetry_ty eq_b) in
    equal ~loc e1 e2 >?= fun eq_e ->
    let eq = Jdg.congr_lambda ~loc ~at_ty eq_a a1 a2 eq_b eq_e in
    Opt.return eq)

  | Jdg.Apply (h1, e1), Jdg.Apply (h2, e2) ->
    let a1, b1 = match Jdg.shape_ty (Jdg.typeof h1) with
      | Jdg.Prod (a, b) -> a, b
      | _ -> assert false
    and a2, b2 = match Jdg.shape_ty (Jdg.typeof h2) with
      | Jdg.Prod (a, b) -> a, b
      | _ -> assert false
    in
    let ta1 = Jdg.atom_ty a1
    and ta2 = Jdg.atom_ty a2 in
    equal_ty ~loc ta1 ta2 >?= fun eq_a ->
    let a1_ta2 = Jdg.convert ~loc (Jdg.atom_term ~loc a1) eq_a in
    let b2 = Jdg.substitute_ty ~loc b2 a2 a1_ta2 in
    Opt.add_abstracting (Jdg.atom_term ~loc a1)
    (equal_ty ~loc b1 b2) >?= fun eq_b ->
    let eq_prod = Jdg.congr_prod_ty ~loc eq_a a1 a2 eq_b in
    let h2 = Jdg.convert ~loc h2 (Jdg.symmetry_ty eq_prod) in
    equal ~loc h1 h2 >?= fun eq_h ->
    let e2 = Jdg.convert ~loc e2 (Jdg.symmetry_ty eq_a) in
    equal ~loc e1 e2 >?= fun eq_e ->
    let eq = Jdg.congr_apply ~loc ~at_ty eq_a a1 a2 eq_b eq_h eq_e in
    Opt.return eq

  | Jdg.Eq (lhs1, rhs1), Jdg.Eq (lhs2, rhs2) ->
    let ty1 = Jdg.typeof lhs1
    and ty2 = Jdg.typeof lhs2 in
    equal_ty ~loc ty1 ty2 >?= fun eq_ty ->
    let eq_ty_r = Jdg.symmetry_ty eq_ty in
    let lhs2 = Jdg.convert ~loc lhs2 eq_ty_r
    and rhs2 = Jdg.convert ~loc rhs2 eq_ty_r in
    equal ~loc lhs1 lhs2 >?= fun eq_l ->
    equal ~loc rhs1 rhs2 >?= fun eq_r ->
    let eq = Jdg.congr_eq ~loc ~at_ty eq_ty eq_l eq_r in
    Opt.return eq

  | Jdg.Refl e1, Jdg.Refl e2 ->
    let ty1 = Jdg.typeof e1
    and ty2 = Jdg.typeof e2 in
    equal_ty ~loc ty1 ty2 >?= fun eq_ty ->
    let e2 = Jdg.convert ~loc e2 (Jdg.symmetry_ty eq_ty) in
    equal ~loc e1 e2 >?= fun eq_e ->
    let eq = Jdg.congr_refl ~loc ~at_ty eq_ty eq_e in
    Opt.return eq

  | (Jdg.Type | Jdg.Atom _ | Jdg.Constant _
    | Jdg.Prod _ | Jdg.Lambda _ | Jdg.Apply _
    | Jdg.Eq _ | Jdg.Refl _), _ ->
    Opt.fail

  end


let extensionality ~loc j1 j2 =
  match Jdg.shape_ty (Jdg.typeof j1) with

    | Jdg.Prod (a, b) ->
      Runtime.lookup_typing_env >!= fun env ->
      let ja = Jdg.form ~loc env (Jdg.Atom a) in
      let lhs = Jdg.form ~loc env (Jdg.Apply (j1, ja))
      and rhs = Jdg.form ~loc env (Jdg.Apply (j2, ja)) in
      Opt.add_abstracting (Jdg.atom_term ~loc a)
      (equal ~loc lhs rhs) >?= fun eq ->
      let eq = Jdg.funext ~loc eq in
      Opt.return eq

    | Jdg.Eq _ ->
      let eq = Jdg.uip ~loc j1 j2 in
      Opt.return eq
    
    | Jdg.Type | Jdg.Atom _ | Jdg.Constant _ | Jdg.Lambda _ | Jdg.Apply _ | Jdg.Refl _ ->
      Opt.fail

let reduction_step ~loc j = match Jdg.shape j with
  | Jdg.Apply (j1, j2) ->
    begin match Jdg.shape j1 with
      | Jdg.Lambda (a, e) ->
        begin match Jdg.shape_ty (Jdg.typeof j1) with
          | Jdg.Prod (a', b') ->
            equal_ty ~loc (Jdg.atom_ty a) (Jdg.atom_ty a') >?= fun eq_a ->
            let b = Jdg.typeof e in
            let a_ty' = Jdg.convert ~loc (Jdg.atom_term ~loc a) eq_a in
            let b' = Jdg.substitute_ty ~loc b' a' a_ty' in
            Opt.add_abstracting (Jdg.atom_term ~loc a)
            (equal_ty ~loc b b') >?= fun eq_b ->
            let eq = Jdg.beta ~loc eq_a a a' eq_b e j2 in
            Runtime.lookup_typing_env >!= fun env ->
            let eqt = Jdg.natural_eq ~loc env j in
            let eq = Jdg.convert_eq ~loc eq eqt in
            Opt.return eq

          | _ -> assert false
        end

      | Jdg.Type | Jdg.Atom _ | Jdg.Constant _
      | Jdg.Prod _ | Jdg.Apply _
      | Jdg.Eq _ | Jdg.Refl _ ->
        Opt.fail
    end

  | Jdg.Type | Jdg.Atom _ | Jdg.Constant _
  | Jdg.Prod _ | Jdg.Lambda _
  | Jdg.Eq _ | Jdg.Refl _ ->
    Opt.fail


let as_eq_alpha t =
  match Jdg.shape_ty t with
    | Jdg.Eq (e1, e2) -> Some (e1, e2)
    | _ -> None

let as_eq ~loc t =
  match as_eq_alpha t with
    | Some (e1, e2) -> Opt.return (Jdg.reflexivity_ty t, e1, e2)
    | None ->
      Predefined.operation_as_eq ~loc (Jdg.term_of_ty t) >!=
      begin function
        | None ->
          Opt.fail
        | Some juser ->
          let jt = Jdg.typeof juser in
          begin match as_eq_alpha jt with
            | None ->
               Opt.lift Runtime.(error ~loc (InvalidAsEquality jt))
            | Some (e1, e2) ->
              begin match Jdg.alpha_equal_eq_ty ~loc Jdg.ty_ty (Jdg.typeof e1) with
                | None -> Opt.lift Runtime.(error ~loc (InvalidAsEquality jt))
                | Some _ ->
                  begin match Jdg.alpha_equal_eq_ty ~loc t (Jdg.is_ty ~loc e1) with
                    | None -> Opt.lift Runtime.(error ~loc (InvalidAsEquality jt))
                    | Some _ ->
                      begin match as_eq_alpha (Jdg.is_ty ~loc e2) with
                        | None -> 
                          Runtime.(error ~loc (InvalidAsEquality jt))

                        | Some (e1,e2) ->
                          let eq = Jdg.is_type_equality (Jdg.reflect juser) in
                          Opt.return (eq, e1, e2)
                      end
                  end
              end
          end
      end

let as_prod_alpha t =
  match Jdg.shape_ty t with
    | Jdg.Prod (a, b) -> Some (a, b)
    | _ -> None

let as_prod ~loc t =
  match as_prod_alpha t with
    | Some (a, b) -> Opt.return (Jdg.reflexivity_ty t, a, b)
    | None ->
      Predefined.operation_as_prod ~loc (Jdg.term_of_ty t) >!=
      begin function
        | None ->
          Opt.fail
        | Some juser ->
          let jt = Jdg.typeof juser in
          begin match as_eq_alpha jt with
            | None ->
               Opt.lift Runtime.(error ~loc (InvalidAsProduct jt))
            | Some (e1, e2) ->
              begin match Jdg.alpha_equal_eq_ty ~loc Jdg.ty_ty (Jdg.typeof e1) with
                | None -> Opt.lift Runtime.(error ~loc (InvalidAsProduct jt))
                | Some _ ->
                  begin match Jdg.alpha_equal_eq_ty ~loc t (Jdg.is_ty ~loc e1) with
                    | None -> Opt.lift Runtime.(error ~loc (InvalidAsProduct jt))
                    | Some _ ->
                      begin match as_prod_alpha (Jdg.is_ty ~loc e2) with
                        | None -> 
                          Runtime.(error ~loc (InvalidAsProduct jt))

                        | Some (a, b) ->
                          let eq = Jdg.is_type_equality (Jdg.reflect juser) in
                          Opt.return (eq, a, b)
                      end
                  end
              end
          end
      end

end

(** Expose without the monad stuff *)

let equal ~loc j1 j2 = Opt.run (Internals.equal ~loc j1 j2)

let equal_ty ~loc j1 j2 = Opt.run (Internals.equal_ty ~loc j1 j2)

let coerce ~loc je jt = Opt.run (Internals.coerce ~loc je jt)

let coerce_fun ~loc je = Opt.run (Internals.coerce_fun ~loc je)

let reduction_step ~loc j = Opt.run (Internals.reduction_step ~loc j)

let congruence ~loc j1 j2 = Opt.run (Internals.congruence ~loc j1 j2)

let extensionality ~loc j1 j2 = Opt.run (Internals.extensionality ~loc j1 j2)

let as_eq ~loc j = Opt.run (Internals.as_eq ~loc j)

let as_prod ~loc j = Opt.run (Internals.as_prod ~loc j)

