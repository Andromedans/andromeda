(** A toplevel computation carries around the current
    environment. *)
type state = {
  desugar : Desugar.Ctx.t ;
  typing : Mlty.Ctx.t ;
  runtime : Runtime.topenv
}

type error =
  | RuntimeError of Runtime.error * TT.print_env
  | JdgError of Jdg.error * TT.print_env
  | ParserError of Ulexbuf.error
  | DesugarError of Desugar.error

exception Error of error Location.located

let print_error err ppf =
  match err with
  | RuntimeError (err, penv) -> Runtime.print_error ~penv err ppf
  | JdgError (err, penv) -> Jdg.print_error ~penv err ppf
  | ParserError err -> Ulexbuf.print_error err ppf
  | DesugarError err -> Desugar.print_error err ppf

let print_located_error {Location.thing=err; loc} ppf =
  Format.fprintf ppf "%t:@ %t" (Location.print loc) (print_error err)

let wrap f state =
  try f state
  with
    | Runtime.Error {Location.thing=err; loc} ->
       let penv = Runtime.get_penv state.runtime in
       raise (Error (Location.locate (RuntimeError (err, penv)) loc))
    | Jdg.Error {Location.thing=err; loc} ->
       let penv = Runtime.get_penv state.runtime in
       raise (Error (Location.locate (JdgError (err, penv)) loc))
    | Ulexbuf.Error {Location.thing=err; loc} ->
      raise (Error (Location.locate (ParserError err) loc))
    | Desugar.Error {Location.thing=err; loc} ->
      raise (Error (Location.locate (DesugarError err) loc))

(** Evaluation of toplevel computations *)
let exec_cmd ~quiet c = wrap (fun {desugar;typing;runtime} ->
  let desugar, c = Desugar.toplevel  ~basedir:Filename.current_dir_name desugar c in
  let typing = Mlty.infer typing c in
  let comp = Eval.toplevel ~quiet c in
  let (), runtime = Runtime.exec comp runtime in
  {desugar;typing;runtime})

let exec_interactive = wrap (fun state ->
  let cmd = Lexer.read_toplevel Parser.commandline () in
  exec_cmd ~quiet:false cmd state)

let use_file ~fn ~quiet = wrap (fun {desugar;typing;runtime} ->
  let desugar, cmds = Desugar.file desugar fn in
  let typing = List.fold_left Mlty.infer typing cmds in
  let comp =
    List.fold_left
      (fun m cmd -> Runtime.top_bind m (fun () -> Eval.toplevel ~quiet cmd))
      (Runtime.top_return ()) cmds
  in
  let (), runtime = Runtime.exec comp runtime in
  {desugar;typing;runtime})

let initial =
  let cmds = Lexer.read_string Parser.file Predefined.definitions in
  let desugar, cmds = List.fold_left (fun (desugar, cmds) cmd ->
      let desugar, cmd = Desugar.toplevel ~basedir:Filename.current_dir_name desugar cmd in
      (desugar, cmd :: cmds))
    (Desugar.Ctx.empty, []) cmds
  in
  let cmds = List.rev cmds in
  let typing = List.fold_left Mlty.infer Mlty.Ctx.empty cmds in
  let comp = List.fold_left
    (fun m cmd -> Runtime.top_bind m (fun () -> Eval.toplevel ~quiet:true cmd))
    (Runtime.top_return ()) cmds
  in
  let (), runtime = Runtime.exec comp Runtime.empty in
  {desugar;typing;runtime}

