(** A toplevel computation carries around the current
    environment. *)
type state = {
  desugar : Desugar.Ctx.t ;
  typing : Mlty.Ctx.t ;
  runtime : Runtime.topenv
}

(** Evaluation of toplevel computations *)
let exec_cmd ~quiet c {desugar;typing;runtime} =
  let desugar, c = Desugar.toplevel desugar c in
  let typing = Mlty.infer typing c in
  let comp = Eval.toplevel ~quiet c in
  let (), runtime = Runtime.exec comp runtime in
  {desugar;typing;runtime}

let use_file ~fn ~quiet {desugar;typing;runtime} =
  let desugar, cmds = Desugar.file desugar fn in
  let typing = List.fold_left Mlty.infer typing cmds in
  let comp = List.fold_left
    (fun m cmd -> Runtime.top_bind m (fun () -> Eval.toplevel ~quiet cmd))
    (Runtime.top_return ()) cmds
  in
  let (), runtime = Runtime.exec comp runtime in
  {desugar;typing;runtime}

let initial =
  try
    let cmds = Desugar.parse Lexer.read_string Parser.file Predefined.definitions in
    let desugar, cmds = List.fold_left (fun (desugar, cmds) cmd ->
        let desugar, cmd = Desugar.toplevel desugar cmd in
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
  with
   | Error.Error err -> Print.error "Error while setting predefined constructs:\n%t" (Error.print err); exit 1

