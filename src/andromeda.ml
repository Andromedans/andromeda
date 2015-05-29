(** Andromeda main program *)

(** The usage message. *)
let usage = "Usage: andromeda [option] ... [file] ..."

(** The help text printed when [#help] is used. *)
let help_text = "Toplevel directives:
#context .... print current context
#help ....... print this help
#quit ....... exit

Parameter <ident> ... <ident> : <type> .     assume variable <ident> has type <type>
Let <ident> := <expr> .                      define <ident> to be <expr>
Check <expr> .                               check the type of <expr>

The syntax is vaguely Coq-like. The strict equality is written with a double ==.
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
     Arg.Set Config.annotate,
     " Print type annotations");

    ("--debruijn",
      Arg.Set Config.debruijn,
     " Print de Bruijn indices of bound variables");

    ("--wrapper",
     Arg.String (fun str -> Config.wrapper := Some [str]),
     "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)");

    ("--no-wrapper",
     Arg.Unit (fun () -> Config.wrapper := None),
     " Do not use a command-line wrapper");

    ("--no-prelude",
     Arg.Unit (fun () -> Config.prelude_file := Config.PreludeNone),
     " Do not load the prelude.m31 file");

    ("--prelude",
     Arg.String (fun str -> Config.prelude_file := Config.PreludeFile str),
     "<file> Specify the prelude file to load initially");

    ("-v",
     Arg.Unit (fun () ->
         Format.printf "Andromeda %s (%s)@." Version.version Sys.os_type ;
         exit 0),
     " Print version information and exit");

    ("-V",
     Arg.Set_int Config.verbosity,
     "<n> Set printing verbosity to <n>");

    ("-n",
     Arg.Clear Config.interactive_shell,
     " Do not run the interactive toplevel");

    ("-l",
     Arg.String (fun str -> add_file false str),
     "<file> Load <file> into the initial environment");
  ]

(** Parser wrapper that reads extra lines on demand. *)
let parse parse lexbuf =
  try
    parse Lexer.token lexbuf
  with
  | Parser.Error ->
    Error.syntax ~loc:(Location.of_lexeme lexbuf) ""
  | Failure "lexing: empty token" ->
    Error.syntax ~loc:(Location.of_lexeme lexbuf) "unrecognised symbol."

(** [exec_cmd ctx d] executes toplevel command [c] in context [ctx]. It prints the
    result if in interactive mode, and returns the new context. *)
let rec exec_cmd interactive ctx c =
  let (c', loc) = Desugar.toplevel (Context.bound_names ctx) c in
  match c' with
  | Syntax.Parameter (xs,c) ->
    let t = Eval.ty ctx c in
    let ctx =
      List.fold_left
        (fun ctx x ->
           let ctx = Context.add_free x t ctx in
           if interactive then Format.printf "%t is assumed.@\n" (Name.print x) ;
           ctx)
        ctx
        xs
    in
    Format.printf "@." ;
    ctx

  | Syntax.TopLet (x, c) ->
    begin
      match Eval.comp ctx c with
      | Value.Return v ->
        let ctx = Context.add_bound x v ctx in
        if interactive then Format.printf "%t is defined.@\n@." (Name.print x) ;
        ctx
    end

  | Syntax.TopCheck c ->
    begin
      match Eval.comp ctx c with
      | Value.Return (e,t) ->
        let e = Simplify.simplify ctx e
        and t = Simplify.simplify_ty ctx t in
        Format.printf "%t@." (Value.print (Context.used_names ctx) (e,t)) ;
        ctx
    end

  | Syntax.TopBeta c ->
    begin
      match Eval.comp ctx c with
        | Value.Return (_,t) ->
            let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
            let h = Pattern.make_beta_hint ~loc (xts, (t, e1, e2)) in
            let ctx = Context.add_beta h ctx in
            Format.printf "Beta hint installed.@." ;
            ctx
    end

  | Syntax.TopEta c ->
    begin
      match Eval.comp ctx c with
        | Value.Return (_,t) ->
            let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
            let h = Pattern.make_eta_hint ~loc (xts, (t, e1, e2)) in
            let ctx = Context.add_eta h ctx in
            Format.printf "Eta hint installed.@." ;
            ctx
    end

  | Syntax.TopInhabit c ->
    begin
      match Eval.comp ctx c with
        | Value.Return (_,t) ->
          let (xts, u) = Equal.as_universal_ty ctx t in
          let h = Pattern.make_inhabit ~loc (xts, u) in
          let ctx = Context.add_inhabit h ctx in
          Format.printf "Inhabit hint installed.@." ;
          ctx
    end

  | Syntax.TopHint c ->
    begin
      match Eval.comp ctx c with
        | Value.Return (_,t) ->
            let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
            let h = Pattern.make_hint ~loc (xts, (t, e1, e2)) in
            let ctx = Context.add_hint h ctx in
            Format.printf "Hint installed.@." ;
            ctx
    end

  | Syntax.Context ->
    Format.printf "%t@." (Context.print ctx) ;
    ctx

  | Syntax.Help ->
    Format.printf "%s@." help_text ; ctx

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
      | Error.Error err -> Error.print err Format.err_formatter
      | Sys.Break -> Format.eprintf "Interrupted.@."
    done
  with End_of_file -> ()

(** Main program *)
let main =
  Sys.catch_break true ;
  (* Parse the arguments. *)
  Arg.parse
    options
    (fun str -> add_file true str ; Config.interactive_shell := false)
    usage ;
  (* Attempt to wrap yourself with a line-editing wrapper. *)
  if !Config.interactive_shell then
    begin match !Config.wrapper with
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
    match !Config.prelude_file with
    | Config.PreludeNone -> ()
    | Config.PreludeFile f -> files := (f, false) :: !files
    | Config.PreludeDefault ->
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
    if !Config.interactive_shell then
      toplevel ctx
  with
    Error.Error err -> Error.print err Format.err_formatter; exit 1

