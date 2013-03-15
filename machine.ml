(** Abstract machine for evaluating computations. *)

open Context
open Syntax

let run ctx (c, loc) =
  match c with
    | Infer e ->
      let t = Typing.infer ctx e in
        Format.printf "%t@\n    : %t@." (Print.expr ctx.names e) (Print.expr ctx.names t)
    | Check (e1, e2) ->
      Typing.check ctx e1 e2 ;
      Format.printf "Brasil relata sucesso.@."
    | Equal (t, e1, e2) ->
      assert false
