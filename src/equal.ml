(** The whnf of a type [t] in context [ctx]. *)
let rec whnf_ty ctx (Value.Ty t) =
  Value.ty (whnf ctx t Value.typ)

(** The whnf of term [e] at type [t] in context [ctx]. *)
and whnf ctx ((e',loc) as e) t =
  match e' with

    | Value.Name _ -> e

    | Value.Bound _ -> Error.impossible ~loc "deBruijn encountered in whnf"

    | Value.Lambda _ -> e

    | Value.Spine _ -> Error.unimplemented ~loc "whnf for spines not implemented"

    | Value.Type -> e

    | Value.Prod _ -> e

    | Value.Eq _ -> e

    | Value.Refl _ -> e

let equal_ty ctx (Value.Ty t1) (Value.Ty t2) =
  Error.unimplemented "Type equivalence not implemented"

let as_prod ctx t =
  let (Value.Ty (t', loc)) = whnf_ty ctx t in
  match t' with
  | Value.Prod (xts, u) -> (xts, u)
  | _ -> Error.typing ~loc "Type %t cannot be decomposed into a product" (Print.ty ctx t)
