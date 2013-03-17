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

let run_operation ctx (op, loc) =
  match op with
    | Inhabit t ->
      ignore (Typing.check_sort ctx t) ;
      Error.runtime ~loc "sorry, this has not been implemented yet" (Print.expr ctx.names t)
    | Infer e ->
      let t = Typing.infer ctx e in
        mk_tywtn e t, mk_tyjdg e t
    | HasType (e, t) ->
      Typing.check ctx e t ;
      mk_tywtn e t, mk_tyjdg e t
    | Equal (e1, e2, t) ->
      ignore (Typing.check_sort ctx t) ;
      if Typing.equal_at ctx e1 e2 t
      then mk_eqwtn e1 e2 t, mk_eqjdg e1 e2 t
      else Error.runtime ~loc "do not know how to derive %t" (Print.expr ctx.names (mk_eqjdg e1 e2 t))

let rec run ctx (c, loc) =
  match c with
    | Abstraction (x, t, c) ->
      ignore (Typing.check_sort ctx t) ;
      let e, t' = run (add_parameter x t ctx) c in
        mk_lambda x (Some t) e, mk_pi x t t'
    | Operation op ->
      run_operation ctx op
