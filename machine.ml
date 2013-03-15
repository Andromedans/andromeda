(** Abstract machine for evaluating computations. *)

open Context
open Syntax ;;


Random.self_init () ;;

let message () =
  let msg = [|
    "Бразилия с радостью сообщает успех." ;
    "Рио-де-Жанейро верит в тебя." ;
    "Порту-Алегри сообщает, что никакой ошибки не было найдено." ;
    "Мы также говорим португальские здесь." ;
    "Estes teoremas são chatos, nós preferimos a dançar." ;
    "Não encontramos erros." ;
    "Tudo estava correto." ;
    "Brasil felizmente relata sucesso." |]
  in
  let k = Random.int (Array.length msg) in
    msg.(k)

let run ctx (c, loc) =
  match c with
    | Infer e ->
      let t = Typing.infer ctx e in
        Format.printf "%t@\n    : %t@." (Print.expr ctx.names e) (Print.expr ctx.names t)
    | Check (brasil, e1, e2) ->
      Typing.check ctx e1 e2 ;
      if brasil
      then Format.printf "%s@." (message ())
      else Format.printf "Correct.@."
    | Equal (t, e1, e2) ->
      assert false
