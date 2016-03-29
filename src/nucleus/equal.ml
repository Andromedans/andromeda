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

(* TODO
  let add_abstracting ~loc x j m =
    { k = fun sk fk ->
          Runtime.add_abstracting ~loc x j (fun jx -> (m jx).k sk fk) }
*)

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
  match Jdg.alpha_equal ~loc j1 j2 with
    | Some eq -> Opt.return eq
    | None ->
      Predefined.operation_equal ~loc j1 j2 >!= begin function
        | Some juser ->
          Runtime.lookup_typing_env >!= fun env ->
          let target = Jdg.form_ty ~loc env (Jdg.Eq (j1, j2)) in
          begin match Jdg.alpha_equal_ty ~loc target (Jdg.typeof juser) with
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

(** Apply the appropriate congruence rule *)
let congruence ~loc j1 j2 =
  begin match Jdg.shape j1, Jdg.shape j2 with

  | Jdg.Type, Jdg.Type | Jdg.Atom _, Jdg.Atom _ | Jdg.Constant _, Jdg.Constant _ ->
    begin match Jdg.alpha_equal ~loc j1 j2 with
      | Some eq -> Opt.return eq
      | None -> Opt.fail
    end

  | Jdg.Prod (a1, b1), Jdg.Prod (a2, b2) ->
    let ta1 = Jdg.atom_ty a1
    and ta2 = Jdg.atom_ty a2 in
    equal_ty ~loc ta1 ta2 >?= fun eq_a ->
    let a1_ta2 = Jdg.convert ~loc (Jdg.atom_term ~loc a1) eq_a in
    let b2 = Jdg.substitute_ty ~loc b2 a2 a1_ta2 in
    equal_ty ~loc b1 b2 >?= fun eq_b ->
    let eq = Jdg.congr_prod ~loc eq_a a1 a2 eq_b in
    Opt.return eq

  | Jdg.Lambda (a1, e1), Jdg.Lambda (a2, e2) ->
    let ta1 = Jdg.atom_ty a1
    and ta2 = Jdg.atom_ty a2 in
    equal_ty ~loc ta1 ta2 >?= fun eq_a ->
    let a1_ta2 = Jdg.convert ~loc (Jdg.atom_term ~loc a1) eq_a in
    let e2 = Jdg.substitute ~loc e2 a2 a1_ta2 in
    let b1 = Jdg.typeof e1
    and b2 = Jdg.typeof e2 in
    equal_ty ~loc b1 b2 >?= fun eq_b ->
    let e2 = Jdg.convert ~loc e2 (Jdg.symmetry_ty eq_b) in
    equal ~loc e1 e2 >?= fun eq_e ->
    let eq = Jdg.congr_lambda ~loc eq_a a1 a2 eq_b eq_e in
    Opt.return eq

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
    equal_ty ~loc b1 b2 >?= fun eq_b ->
    let eq_prod = Jdg.congr_prod_ty ~loc eq_a a1 a2 eq_b in
    let h2 = Jdg.convert ~loc h2 (Jdg.symmetry_ty eq_prod) in
    equal ~loc h1 h2 >?= fun eq_h ->
    let e2 = Jdg.convert ~loc e2 (Jdg.symmetry_ty eq_a) in
    equal ~loc e1 e2 >?= fun eq_e ->
    let eq = Jdg.congr_apply ~loc eq_a a1 a2 eq_b eq_h eq_e in
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
    let eq = Jdg.congr_eq ~loc eq_ty eq_l eq_r in
    Opt.return eq

  | Jdg.Refl e1, Jdg.Refl e2 ->
    let ty1 = Jdg.typeof e1
    and ty2 = Jdg.typeof e2 in
    equal_ty ~loc ty1 ty2 >?= fun eq_ty ->
    let e2 = Jdg.convert ~loc e2 (Jdg.symmetry_ty eq_ty) in
    equal ~loc e1 e2 >?= fun eq_e ->
    let eq = Jdg.congr_refl ~loc eq_ty eq_e in
    Opt.return eq

  | (Jdg.Type | Jdg.Atom _ | Jdg.Constant _
    | Jdg.Prod _ | Jdg.Lambda _ | Jdg.Apply _
    | Jdg.Eq _ | Jdg.Refl _), _ ->
    Opt.fail

  end >?= fun eq ->
  (* Ensure that the equality is at the right type. *)
  Runtime.lookup_typing_env >!= fun env ->
  let eqt = Jdg.natural_eq ~loc env j1 in
  let eq = Jdg.convert_eq ~loc eq eqt in
  Opt.return eq

let extensionality ~loc j1 j2 = assert false (* TODO *)


let reduction_step ~loc j = assert false (* TODO *)

let as_eq ~loc j = assert false (* TODO *)
let as_prod ~loc j = assert false (* TODO *)

(*
let as_eq_alpha t' =
  match t' with
    | Tt.Eq (t, e1, e2) -> Some (t, e1, e2)
    | _ -> None

let as_eq (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Eq (t, e1, e2) -> Monad.return (ctx, t, e1, e2)
    | _ ->
      Monad.lift (Predefined.operation_as_eq (Runtime.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Predefined.as_option ~loc v with
        | None ->
          Runtime.(error ~loc (EqualityTypeExpected jt))
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Runtime.as_term ~loc v in
          begin
            let j_tv = Jdg.mk_ty ctxv tv in
            match as_eq_alpha j_tv with
            | None ->
               Runtime.(error ~loc (InvalidAsEquality j_tv))
            | Some (tv, e1, e2) ->
               if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
               then
                 let j_e2 = Jdg.mk_ty ctxv (Tt.ty e2) in
                 begin
                   match as_eq_alpha j_e2 with
                   | None -> 
                      Runtime.(error ~loc (InvalidAsEquality j_tv))

                   | Some (t,e1,e2) ->
                      let ctx = Jdg.Ctx.join ~loc ctx ctxv in
                      let hyps = Tt.assumptions_term ev in
                      Monad.add_hyps hyps >>= fun () ->
                      Monad.return (ctx,t,e1,e2)
                 end
               else
                 Runtime.(error ~loc (InvalidAsEquality j_tv))
          end
      end

let as_prod_alpha (Jdg.Ty (_, (Tt.Ty {Tt.term=t';_}))) =
  match t' with
    | Tt.Prod (xts,t) -> Some (xts,t)
    | _ -> None

let as_prod (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Prod (xts,t) -> Monad.return (ctx, (xts,t))
    | _ ->
      Monad.lift (Predefined.operation_as_prod (Runtime.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Predefined.as_option ~loc v with
        | None -> Runtime.(error ~loc (ProductExpected jt))
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Runtime.as_term ~loc v in
          let j_tv = Jdg.mk_ty ctxv tv in
          begin
            match as_eq_alpha j_tv with
            | None -> Runtime.(error ~loc (InvalidAsProduct j_tv))
            | Some (tv,e1,e2) ->
               if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
               then
                 begin
                   match as_prod_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) with
                   | None -> Runtime.(error ~loc (InvalidAsProduct j_tv))
                   | Some (xts,t) ->
                      let ctx = Jdg.Ctx.join ~loc ctx ctxv in
                      let hyps = Tt.assumptions_term ev in
                      Monad.add_hyps hyps >>= fun () ->
                      Monad.return (ctx,(xts,t))
                 end
               else
                 Runtime.(error ~loc (InvalidAsProduct j_tv))
          end
      end
*)
end

(** Expose without the monad stuff *)

let equal ~loc j1 j2 = Opt.run (Internals.equal ~loc j1 j2)

let equal_ty ~loc j1 j2 = Opt.run (Internals.equal_ty ~loc j1 j2)

let reduction_step ~loc j = Opt.run (Internals.reduction_step ~loc j)

let congruence ~loc j1 j2 = Opt.run (Internals.congruence ~loc j1 j2)

let extensionality ~loc j1 j2 = Opt.run (Internals.extensionality ~loc j1 j2)

let as_eq ~loc j = Opt.run (Internals.as_eq ~loc j)

let as_prod ~loc j = Opt.run (Internals.as_prod ~loc j)

