(** Andromeda main program *)

(** The location of prelude file *)

type prelude =
  | PreludeNone
  | PreludeDefault
  | PreludeFile of string

let prelude_file = ref PreludeDefault

(** Should the interactive shell be run? *)
let interactive_shell = ref true

(** The command-line wrappers that we look for. *)
let wrapper = ref (Some ["rlwrap"; "ledit"])

(** The usage message. *)
let usage = "Usage: andromeda [option] ... [file] ..."

(** The help text printed when [#help] is used. *)
let help_text = "Toplevel directives:
#context .... print current context
#help ....... print this help
#quit ....... exit

Parameter <ident> ... <ident> : <sort>.  .... assume variable <ident> has sort <sort>
Definition <ident> := <expr>.            .... define <ident> to be <expr>
Definition <ident> : <type> := <expr>.   .... define <ident> to be <expr> of <type>
Equation e.                              .... install a global equation hint
Rewrite e.                               .... install a global rewrite hint

The syntax is vaugely Coq-like. The strict equalit is written with a double ==.
" ;;

(** A list of files to be loaded and run, together with information on whether they should
    be loaded in interactive mode. *)
let files = ref []

(** Add a file to the list of files to be loaded, and record whether it should
    be processed in interactive mode. *)
let add_file interactive filename = (files := (filename, interactive) :: !files)

(** A list of command-line wrappers to look for. *)
let wrapper = ref (Some ["rlwrap"; "ledit"])

(** Command-line options *)
let options = Arg.align [
  ("--annotate",
   Arg.Set Print.annotate,
   "print type annotations");
  ("--wrapper",
    Arg.String (fun str -> wrapper := Some [str]),
    "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)");
  ("--no-wrapper",
    Arg.Unit (fun () -> wrapper := None),
    " Do not use a command-line wrapper");
  ("--no-prelude",
    Arg.Unit (fun () -> prelude_file := PreludeNone),
    " Do not load the prelude.m31 file");
  ("--prelude",
    Arg.String (fun str -> prelude_file := PreludeFile str),
    "<file> Specify the prelude file to load initially");
  ("-v",
    Arg.Unit (fun () ->
      Format.printf "Andromeda %s (%s)@." Version.version Sys.os_type ;
      exit 0),
    " Print version information and exit");
  ("-V",
   Arg.Int (fun k -> Print.verbosity := k),
   "<int> Set verbosity level");
  ("-n",
    Arg.Clear interactive_shell,
    " Do not run the interactive toplevel");
  ("-l",
    Arg.String (fun str -> add_file false str),
    "<file> Load <file> into the initial environment");
]

(** Treat anonymous arguments as files to be run. *)
let anonymous str =
  add_file true str;
  interactive_shell := false

(** Parser wrapper that reads extra lines on demand. *)
let parse parse lex =
  try
    parse Lexer.token lex
  with
  | Parser.Error ->
      Error.syntax ~loc:(Position.of_lex lex) ""
  | Failure "lexing: empty token" ->
      Error.syntax ~loc:(Position.of_lex lex) "unrecognised symbol."

(** [exec_cmd ctx d] executes toplevel directive [d] in context [ctx]. It prints the
    result if in interactive mode, and returns the new context. *)
let rec exec_cmd interactive ctx (d, loc) =
  let names = Context.names ctx in
  match d with
    | Input.Assume (xs, t) ->
        let t = Debruijn.ty names t in
        let t = Typing.is_type ctx t  in
        let t = Syntax.simplify_ty t  in
          if interactive then
            begin
              List.iter (fun x -> Format.printf "%s is assumed.@\n" x) xs ;
              Format.printf "@."
            end ;
          fst (List.fold_left
                 (fun (ctx,t) x -> (Context.add_var x t ctx, Syntax.shift_ty 1 t))
                 (ctx, t)
                 xs)
    | Input.Define (x, e) ->
      let e = Debruijn.term names e in
      let e,t = Typing.syn_term ctx e in
      let e = Syntax.simplify e  in
      let t = Syntax.simplify_ty t  in
        if interactive then Format.printf "%s is defined.@\n@." x ;
        Context.add_def x t e ctx

    | Input.TopRewrite e ->
      let e = Debruijn.term names e in
      let e, t = Typing.syn_term ctx e in
      let h = Equal.as_hint ctx e t in
      let ctx = Context.add_rewrite h ctx in
        if interactive then Format.printf "Rewrite added.@\n@." ;
        ctx

    | Input.TopEquation e ->
      let e = Debruijn.term names e in
      let e, t = Typing.syn_term ctx e in
      let h = Equal.as_hint ctx e t in
      let ctx = Context.add_equation h ctx in
        if interactive then Format.printf "Equation added.@\n@." ;
        ctx

    | Input.Context ->
        Context.print ctx ; ctx

    | Input.Help ->
      Format.printf "%s" help_text ; ctx

    | Input.Verbose n ->
        Print.verbosity := n; ctx

    | Input.Quit ->
      exit 0

(** Load directives from the given file. *)
and use_file ctx (filename, interactive) =
  let cmds = Lexer.read_file (parse Parser.file) filename in
    List.fold_left (exec_cmd interactive) ctx cmds

(** Interactive toplevel *)
let toplevel ctx =
  Format.printf "Andromeda %s@\n[Type #help for help.]@." Version.version ;
  try
    let ctx = ref ctx in
    while true do
      try
        let cmd = Lexer.read_toplevel (parse Parser.commandline) () in
        ctx := exec_cmd true !ctx cmd
      with
        | Error.Error err -> Print.error err
        | Sys.Break -> Format.printf "Interrupted.@."
    done
  with End_of_file -> ()

(** Main program *)
let main =
  Sys.catch_break true;
  (* Parse the arguments. *)
  Arg.parse options anonymous usage;
  (* Attempt to wrap yourself with a line-editing wrapper. *)
  if !interactive_shell then
    begin match !wrapper with
      | None -> ()
      | Some lst ->
          let n = Array.length Sys.argv + 2 in
          let args = Array.make n "" in
            Array.blit Sys.argv 0 args 1 (n - 2);
            args.(n - 1) <- "--no-wrapper";
            List.iter
              (fun wrapper ->
                 try
                   args.(0) <- wrapper;
                   Unix.execvp wrapper args
                 with Unix.Unix_error _ -> ())
              lst
    end ;
  (* Files were listed in the wrong order, so we reverse them *)
  files := List.rev !files;
  (* Should we load the prelude file? *)
  begin
    match !prelude_file with
      | PreludeNone -> ()
      | PreludeFile f -> files := (f, false) :: !files
      | PreludeDefault ->
        (* look for prelude next to the executable, don't whine if it is not there *)
        let f = Filename.concat (Filename.dirname Sys.argv.(0)) "prelude.m31" in
          if Sys.file_exists f
          then files := (f, false) :: !files
  end ;

  (* Set the maximum depth of pretty-printing, after which it prints ellipsis. *)
  Format.set_max_boxes 42 ;
  Format.set_ellipsis_text "..." ;
  try
    (* Run and load all the specified files. *)
    let ctx = List.fold_left use_file Context.empty !files in
    if !interactive_shell then
      toplevel ctx
  with
    Error.Error err -> Print.error err ; exit 1

