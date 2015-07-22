open Parser
open Ulexbuf
open Lexer

let rec longest_prefix_up_to l1 l2 pos_lim =
  match l1, l2 with
  | h1::t1, h2::t2 ->
     if h1 = h2 &&
       let p_end = (fst (snd h1)) in
       pos_lim > p_end
     then
       h1 :: (longest_prefix_up_to t1 t2 pos_lim)
     else []
  | _::_, [] | [], _ -> []

let tokens_up_to_pos tokens lim =
  let rec fold acc tokens =
    match tokens with
    | [] -> List.rev acc
    | (((beg, _), _) as h) :: tokens ->
       if beg.Lexing.pos_cnum > lim.Lexing.pos_cnum
       then List.rev acc
       else fold (h::acc) tokens
  in fold [] tokens


let tokens_of_stream ?fn s =
  let lb = from_channel ?fn s in
  let rec fold tks errs =
    begin match token lb with
          | EOF as t ->
             let pos = lb.pos_start, lb.pos_end in
             List.rev ((pos, (t, "End_Of_File")) :: tks), List.rev errs
          | t ->
             let pos = lb.pos_start, lb.pos_end in
             let w = lexeme lb in
             fold ((pos, (t, w)) :: tks) errs
          | exception (Error.Error _ as e) ->
                      let pos = lb.pos_start, lb.pos_end in
                      fold tks ((pos, e) :: errs)
    end in
  let ts = fold [] [] in
  ts

let tokens_of_file fn =
  try
    let fs = open_in fn in
    let ts = tokens_of_stream ~fn fs in
    close_in fs;
    ts
  with
    Sys_error msg -> Error.fatal ~loc:Location.unknown "%s" msg
