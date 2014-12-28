(** Andromeda main program *)

(** Possible locations of prelude file *)
type prelude =
  | PreludeNone             (* do not use a prelude, turned on by the --no-prelude *)
  | PreludeDefault          (* look in the default location, which is next to executable *)
  | PreludeFile of string   (* look for prelude in a specific location *)

(** Location of the prelude file *)
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

Parameter <ident> ... <ident> : <sort> .     assume variable <ident> has sort <sort>
Let <ident> := <expr> .                      define <ident> to be <expr>

The syntax is vaguely Coq-like. The strict equalit is written with a double ==.
" ;;

(** A list of files to be loaded and run, together with information on whether they should
    be loaded in interactive mode. *)
let files = ref []

(** Add a file to the list of files to be loaded, and record whether it should
    be processed in interactive mode. *)
let add_file interactive filename = (files := (filename, interactive) :: !files)

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

  ("-n",
    Arg.Clear interactive_shell,
    " Do not run the interactive toplevel");

  ("-l",
    Arg.String (fun str -> add_file false str),
    "<file> Load <file> into the initial environment");
]

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
let rec exec_cmd interactive ctx d =
  let (d', loc) = Desugar.toplevel d in
    match d' with
    | Syntax.Parameter (xs,c) ->
      let t = Eval.ty ctx c in
      let ctx =
        List.fold_left
          (fun ctx x -> 
            let ctx = Context.add_free x t ctx in
              if interactive then Format.printf "%t is assumed.@\n" (Print.name x) ;
              ctx)
          ctx
          xs
      in
        Format.printf "@." ;
        ctx

    | Syntax.TopLet (x, c) ->
       begin
         match Eval.infer ctx c with
         | Value.Return v ->
            let ctx = Context.add_meta x v ctx in
              if interactive then Format.printf "%t is defined.@\n@." (Print.name x) ;
              ctx
       end

    | Syntax.TopCheck c ->
       begin
         match Eval.infer ctx c with
         | Value.Return v ->
            Format.printf "%t" (Print.value ctx v) ;
            ctx
       end

    | Syntax.Context ->
        Format.printf "%t" (Print.context ctx) ;
        ctx

    | Syntax.Help ->
      Format.printf "%s" help_text ; ctx

    | Syntax.Quit ->
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
  Sys.catch_break true ;
  (* Parse the arguments. *)
  Arg.parse
    options
    (fun str -> add_file true str ; interactive_shell := false)
    usage ;
  (* Attempt to wrap yourself with a line-editing wrapper. *)
  if !interactive_shell then
    begin match !wrapper with
      | None -> ()
      | Some lst ->
          let n = Array.length Sys.argv + 2 in
          let args = Array.make n "" in
            Array.blit Sys.argv 0 args 1 (n - 2) ;
            args.(n - 1) <- "--no-wrapper" ;
            List.iter
              (fun wrapper ->
                 try
                   args.(0) <- wrapper ;
                   Unix.execvp wrapper args
                 with Unix.Unix_error _ -> ())
              lst
    end ;
  (* Files were accumulated in the wrong order, so we reverse them *)
  files := List.rev !files ;
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

