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
     let penv = Runtime.get_penv state.runtime in
     Format.fprintf ppf "%t:@.@[<hov 2>Runtime error:@ %t@]" (Location.print loc) (Runtime.print_error ~penv err)

  | NucleusError err ->
     let penv = Runtime.get_nucleus_penv state.runtime in
     Format.fprintf ppf "@[<hov 2>Nucleus error:@ %t@]" (Nucleus.print_error ~penv err)

let wrap_error f x =
  try f x
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

let exec_interactive =
  wrap_error
    begin
      fun {desugar;typing;runtime} ->
      let c = Lexer.read_toplevel Parser.commandline () in
      let desugar, cs = Desugar.toplevel  ~basedir:Filename.current_dir_name desugar c in
      let typing, cs = Typecheck.toplevels typing cs in
      let comp = Eval.toplevels ~quiet:false ~print_annot cs in
      let (), runtime = Runtime.exec comp runtime in
      { desugar; typing; runtime}
    end

let use_file ~quiet fn =
  wrap_error
    begin
      fun {desugar;typing;runtime} ->
      let desugar, cmds = Desugar.use_file desugar fn in
      let typing, cmds = Typecheck.toplevels typing cmds in
      let comp = Eval.toplevels ~quiet ~print_annot cmds in
      let (), runtime = Runtime.exec comp runtime in
      { desugar; typing; runtime }
    end

let load_ml_module ~fn ~quiet =
  wrap_error
    begin
      fun {desugar;typing;runtime} ->
      (* When desugar loads a file as a module, it returns a single
         toplevel cmd [module X = struct <content of file> end] *)
      let desugar, cmd = Desugar.load_ml_module desugar fn in
      let typing, cmd = Typecheck.toplevel typing cmd in
      let comp = Eval.toplevel ~quiet ~print_annot cmd in
      let (), runtime = Runtime.exec comp runtime in
      { desugar; typing; runtime }
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
