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
let equal ~loc sgn e1 e2 =
  match Jdg.mk_alpha_equal_term sgn e1 e2 with
    | Some eq -> Opt.return eq
    | None ->
      Predefined.operation_equal_term ~loc e1 e2 >!=
        begin function
          | None -> Opt.fail
          | Some eq ->
             let (Jdg.Stump_EqTerm (_asmp, e1', e2', _)) = Jdg.invert_eq_term eq in
             begin
               match Jdg.alpha_equal_term e1 e1' && Jdg.alpha_equal_term e2 e2' with
               | false -> Opt.lift (Runtime.(error ~loc (InvalidEqualTerm (e1, e2))))
               | true -> Opt.return eq
             end
        end

(* Compare two types *)
let equal_type ~loc t1 t2 =
  match Jdg.mk_alpha_equal_type t1 t2 with
    | Some eq -> Opt.return eq
    | None ->
      Predefined.operation_equal_type ~loc t1 t2 >!=
        begin function
          | None -> Opt.fail
          | Some eq ->
             let (Jdg.Stump_EqType (_asmp, t1', t2')) = Jdg.invert_eq_type eq in
             begin match Jdg.alpha_equal_type t1 t1' && Jdg.alpha_equal_type t2 t2' with
             | false -> Opt.lift (Runtime.(error ~loc (InvalidEqualType (t1, t2))))
             | true -> Opt.return eq
             end
        end

let coerce ~loc sgn e t =
  let t' = Jdg.type_of_term_abstraction sgn e in
  match Jdg.alpha_equal_abstraction Jdg.alpha_equal_type t' t with

  | true -> Opt.return e

  | false ->
     Predefined.operation_coerce ~loc e t >!=
       begin function

       | Predefined.NotCoercible -> Opt.fail

       | Predefined.Convertible eq ->
          (* Have:
             e  = {x:A₁} … {x:Aₙ} ⊢ s : A
             t' = {x:A₁} … {x:Aₙ} ⊢ A type
             t  = {x:B₁} … {x:Bₘ} ⊢ B type
             eq = {x:C₁} … {x:Cₘ} ⊢ C == D

             Plan:
             - Invert e to
                 [a₁, …, aₙ] ⊢ s : A
             - apply eq to [a₁, …, aₙ] forming
                 eq' := (⊢ C == D) [ a₁, …, aₙ / x₁, …, xₘ ]
               This might fail if `n =/= m` or if `∃ i, Aᵢ =/= Cᵢ`
               We could check for this first and raise a runtime error, or try
               and leave it to the nucleus to fail.
             - check that `D' =α= t` to make sure we actually convert to where
               we want
             - convert s along eq', which might again fail in the nucleus.
             - abstract [a₁, …, aₙ]
          *)
          let rec fully_apply_abstraction apply_abstr abstr = function
            | [] -> abstr
            | arg :: args ->
               let abstr = apply_abstr sgn abstr arg in
               fully_apply_abstraction apply_abstr abstr args
          in
          let fully_apply_eq_type_abstraction =
            fully_apply_abstraction Jdg.apply_eq_type_abstraction in
          let fully_apply_is_type_abstraction =
            fully_apply_abstraction Jdg.apply_is_type_abstraction in

          let rec convert_is_term_abstraction atoms abstr =
            match Jdg.invert_is_term_abstraction abstr with
            | Jdg.Stump_NotAbstract e ->
               let atoms = List.rev atoms in
               let atoms = List.map Jdg.form_is_term_atom atoms in
               let eq_app =
                 let eq_app = fully_apply_eq_type_abstraction eq atoms in
                 begin match Jdg.as_not_abstract eq_app with
                   | None -> Runtime.(error ~loc (InvalidConvertible (t', t, eq)))
                   | Some eq -> eq
                 end
               and t_app =
                 let t_app = fully_apply_is_type_abstraction t atoms in
                 begin match Jdg.as_not_abstract t_app with
                   | None -> Runtime.(error ~loc (InvalidConvertible (t', t, eq)))
                   | Some t_app -> t_app
                 end
               and t'_app = Jdg.type_of_term sgn e
               in
               let Jdg.Stump_EqType (_asmp, lhs, rhs) = Jdg.invert_eq_type eq_app in
               begin match Jdg.alpha_equal_type rhs t_app && Jdg.alpha_equal_type lhs t'_app with
               | true -> ()
               | false -> Runtime.(error ~loc (InvalidConvertible (t', t, eq)))
               end ;
               let e = Jdg.form_is_term_convert sgn e eq_app in
               Jdg.abstract_not_abstract e
            | Jdg.Stump_Abstract (a, abstr) ->
               let abstr = convert_is_term_abstraction (a::atoms) abstr in
               Jdg.abstract_is_term a abstr
          in
          Opt.return (convert_is_term_abstraction [] e)

       | Predefined.Coercible e' ->
          begin
            let u = Jdg.type_of_term_abstraction sgn e' in
            match Jdg.alpha_equal_abstraction Jdg.alpha_equal_type t u with
            | true -> Opt.return e'
            | false -> Runtime.(error ~loc (InvalidCoerce (t, e')))
          end
       end

end

(** Expose without the monad stuff *)

let equal ~loc sgn j1 j2 = Opt.run (Internals.equal ~loc sgn j1 j2)

let equal_type ~loc j1 j2 = Opt.run (Internals.equal_type ~loc j1 j2)

let coerce ~loc sgn je jt = Opt.run (Internals.coerce ~loc sgn je jt)
