(** A toplevel computation carries around the current
    environment. *)
type state = {
  desugar : Desugar.Ctx.t ;
  typing : Tyenv.t ;
  runtime : Runtime.topenv
}

type error =
  | ParserError of Ulexbuf.error Location.located
  | DesugarError of Desugar.error Location.located
  | TypingError of Mlty.error Location.located
  | RuntimeError of Runtime.error Location.located
  | NucleusError of Nucleus.error

exception Error of error

let print_error state err ppf =
  match err with

  | ParserError {Location.thing=err; loc} ->
     Format.fprintf ppf "%t:@.@[<hov 2>Parsing error:@ %t@]" (Location.print loc) (Ulexbuf.print_error err)

  | DesugarError {Location.thing=err; loc} ->
     Format.fprintf ppf "%t:@.@[<hov 2>Type error:@ %t@]" (Location.print loc) (Desugar.print_error err)

  | TypingError {Location.thing=err; loc} ->
     Format.fprintf ppf "%t:@.@[<hov 2>Type error:@ %t@]" (Location.print loc) (Mlty.print_error err)

  | RuntimeError {Location.thing=err; loc} ->
     let names = Runtime.get_names state.runtime in
     Format.fprintf ppf "@[<hov 2>Runtime error:@ %t@]" (Runtime.print_error ~names err)

  | NucleusError err ->
     let names = Runtime.get_names state.runtime in
     Format.fprintf ppf "@[<hov 2>Nucleus error:@ %t@]" (Nucleus.print_error ~names err)

let wrap_error f state =
  try f state
  with
    | Ulexbuf.Error err -> raise (Error (ParserError err))
    | Desugar.Error err -> raise (Error (DesugarError err))
    | Mlty.Error err -> raise (Error (TypingError err))
    | Runtime.Error err -> raise (Error (RuntimeError err))
    | Nucleus.Error err -> raise (Error (NucleusError err))

(** Evaluation of toplevel computations *)
let print_annot () =
  let penv = Mlty.fresh_penv () in
  fun t ppf -> Mlty.print_ty_schema ~penv t ppf

let exec_cmd ~quiet c =
  wrap_error
    begin
      fun {desugar;typing;runtime} ->
      let desugar, c = Desugar.toplevel  ~basedir:Filename.current_dir_name desugar c in
      let typing, c = Typecheck.toplevel typing c in
      let comp = Eval.toplevel ~quiet ~print_annot c in
      let (), runtime = Runtime.exec comp runtime in
      {desugar;typing;runtime}
    end

let exec_interactive =
  wrap_error
    begin
      fun state ->
      let cmd = Lexer.read_toplevel Parser.commandline () in
      exec_cmd ~quiet:false cmd state
    end

let use_file ~fn ~quiet =
  wrap_error
    begin
      fun {desugar;typing;runtime} ->
      let desugar, cmds = Desugar.file desugar fn in
      let typing, cmds =
        List.fold_left
          (fun (typing, cmds) cmd ->
            let typing, cmd = Typecheck.toplevel typing cmd in
            (typing, cmd :: cmds))
          (typing, [])
          cmds
      in
      let cmds = List.rev cmds in
      let comp =
        List.fold_left
          (fun m cmd -> Runtime.top_bind m (fun () -> Eval.toplevel ~quiet ~print_annot cmd))
          (Runtime.top_return ())
          cmds
      in
      let (), runtime = Runtime.exec comp runtime in
      {desugar;typing;runtime}
    end

(** Set up the initial environment, with built-in definitions *)
let initial_environment =
  let comp =
    List.fold_left
      (fun m cmd -> Runtime.top_bind m (fun () -> Eval.toplevel ~quiet:true ~print_annot cmd))
      (Runtime.top_return ())
      Typecheck.initial_commands
  in
  let (), initial_runtime = Runtime.exec comp Runtime.empty in
  { desugar = Desugar.initial_context;
    typing = Typecheck.initial_context;
    runtime = initial_runtime }
