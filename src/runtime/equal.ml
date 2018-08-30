(** Equality checking and coercions *)

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

  let run m =
    m.k (fun x -> Runtime.return (Some x)) (Runtime.return None)
end

(*
let (>>=) = Runtime.bind
*)

let (>?=) = Opt.(>?=)

let (>!=) m f = (Opt.lift m) >?= f

module Internals = struct

(** Compare two terms *)
let equal ~loc j1 j2 =
  match Jdg.mk_alpha_equal ~loc j1 j2 with
    | Some eq -> Opt.return eq
    | None ->
      Predefined.operation_equal_term ~loc j1 j2 >!=
        begin function
          | None -> Opt.fail
          | Some juser ->
             let (k1, k2, _) = Jdg.invert_eq_term juser in
             begin
               match Jdg.alpha_equal_is_term j1 k1 && Jdg.alpha_equal_is_term j2 k2 with
               | false -> Opt.lift (Runtime.(error ~loc (InvalidEqualTerm (j1, j2))))
               | true -> Opt.return juser
             end
        end

(** Compare two types *)
let equal_ty ~loc j1 j2 =
  match Jdg.mk_alpha_equal_ty ~loc j1 j2 with
    | Some eq -> Opt.return eq
    | None ->
      Predefined.operation_equal_type ~loc j1 j2 >!=
        begin function
          | None -> Opt.fail
          | Some juser ->
             let (k1, k2) = Jdg.invert_eq_type juser in
             begin
               match Jdg.alpha_equal_is_type j1 k1 && Jdg.alpha_equal_is_type j2 k2 with
               | false -> Opt.lift (Runtime.(error ~loc (InvalidEqualType (j1, j2))))
               | true -> Opt.return juser
             end
        end

let coerce ~loc je jt =
  let je_ty = Jdg.typeof je in
  match Jdg.alpha_equal_eq_type ~loc je_ty jt with

  | Some _ ->
     Opt.return je

  | None ->
     Predefined.operation_coerce ~loc je jt >!=
       begin function

       | Predefined.NotCoercible -> Opt.fail

       | Predefined.Convertible eq ->
          let eq_lhs = Jdg.eq_type_side Jdg.LEFT eq
          and eq_rhs = Jdg.eq_type_side Jdg.RIGHT eq in
          begin
            match Jdg.alpha_equal_eq_type ~loc je_ty eq_lhs,
                  Jdg.alpha_equal_eq_type ~loc jt eq_rhs
            with
            | Some _, Some _ ->
               Opt.return (Jdg.convert ~loc je eq)
            | (None, Some _ | Some _, None | None, None) ->
               Runtime.(error ~loc (InvalidConvertible (je_ty, jt, eq)))
          end

       | Predefined.Coercible je ->
          begin
            match Jdg.alpha_equal_eq_type ~loc (Jdg.typeof je) jt with
            | Some _ ->
               Opt.return je
            | None ->
               Runtime.(error ~loc (InvalidCoerce (jt, je)))
          end
       end
end

(** Expose without the monad stuff *)

let equal ~loc j1 j2 = Opt.run (Internals.equal ~loc j1 j2)

let equal_ty ~loc j1 j2 = Opt.run (Internals.equal_ty ~loc j1 j2)

let coerce ~loc je jt = Opt.run (Internals.coerce ~loc je jt)
