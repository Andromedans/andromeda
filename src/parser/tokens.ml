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

(** [items] is an ordered list of tuples of two [Lexing.position]s and an item.
    Truncate the list before the first position greater than [lim] *)
let items_up_to_pos
      (items : ((Lexing.position * Lexing.position) * 'a) list)
      lim : ((Lexing.position * Lexing.position) * 'a) list =
  let rec fold acc tokens =
    match tokens with
    | [] -> List.rev acc
    | (((beg, _), _) as h) :: tokens ->
       if beg.Lexing.pos_cnum > lim.Lexing.pos_cnum
       then List.rev acc
       else fold (h::acc) tokens
  in fold [] items


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

(* take one toplevel command from a list of tokens, return the command and the remaining tokens *)
let parse_cmd (tokens : ((Lexing.position * Lexing.position) * (Parser.token * string)) list) :
      Input.toplevel * ((Lexing.position * Lexing.position) * (Parser.token * string)) list =
  let tks = ref tokens in
  let pop lb =
    match !tks with
    | [] ->
       (* under-ran tokens without producing a valid command *)
       Parser.EOF
       (* assert false *)
    | ((s, e), (t, w)) :: tks' ->
       tks := tks';
       lb.Lexing.lex_buffer <- w;
       lb.Lexing.lex_start_p <- s;
       lb.Lexing.lex_curr_p <- e;
       t
  in
  let lb = Lexing.from_string "" in
  try
    let res = Parser.command pop lb in
    res, !tks
  with
  | Parser.Error
  | Sedlexing.MalFormed
  | Sedlexing.InvalidCodepoint _ ->
     let w = lb.Lexing.lex_buffer in
     let p_s, p_e = lb.Lexing.lex_start_p, lb.Lexing.lex_curr_p in
     raise (Ulexbuf.Parse_Error (w, p_s, p_e))

(* convert a list of [tokens] to a list of toplevel commands *)
let cmds_of_tokens ?(limit : (Lexing.position * bool) option) tokens errs =

  let limit, tokens, errs =

    match limit with
    | None -> limit, tokens, errs
    | Some (lim, complete) as limit ->
       if not complete then
         let tokens = items_up_to_pos tokens lim
         and errs   = items_up_to_pos errs lim in
         None, tokens, errs
       else
         limit, tokens, errs
  in

  (* XXX Do something smart with the errors. Either we assume that the caller
     provided mode-dependent error-handlers or we extend the class of values
     with an Error case. *)
  List.iter (fun (_, e) -> raise e) errs;

  let rec fold cmds tokens =
    match tokens with
    | []
    | (_, (Parser.EOF, _)) :: _ -> List.rev cmds
    | ((beg, _), _) :: _ ->
       match limit with
       | Some (limit, _) ->
          if beg.Lexing.pos_cnum < limit.Lexing.pos_cnum then
            let cmd, tokens = parse_cmd tokens in
            fold (cmd :: cmds) tokens
          else List.rev cmds
       | None ->
          let cmd, tokens = parse_cmd tokens in
          fold (cmd :: cmds) tokens
  in fold [] tokens
