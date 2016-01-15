(** Andromeda main program *)

(** The usage message. *)
let usage = "Usage: andromeda [option] ... [file] ..."

(** The help text printed when [#help] is used. *)
let help_text = "Toplevel directives:
#environment. .... print current environment
#help. ........... print this help
#quit. ........... exit

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
let add_file ?lim ~once interactive filename = (files := (filename, lim, interactive, once) :: !files)

(** Command-line options *)
let options = Arg.align [

    ("--annotate",
     Arg.Set Config.annotate,
     " Print type annotations");

    ("--ascii",
      Arg.Set Config.ascii,
     " Print terms in ASCII format");

    ("--debruijn",
     Arg.Set Config.debruijn,
     " Print de Bruijn indices of bound variables");

    ("--dependencies",
     Arg.Set Config.print_dependencies,
     " Print depdenencies between assumptions");

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
         Format.printf "Andromeda %s (%s)@." Build.version Sys.os_type ;
         exit 0),
     " Print version information and exit");

    ("-V",
     Arg.Set_int Config.verbosity,
     "<n> Set printing verbosity to <n>");

    ("-n",
     Arg.Clear Config.interactive_shell,
     " Do not run the interactive toplevel");

    ("-l",
     Arg.String (fun str -> add_file ~once:false false str),
     "<file> Load <file> into the initial environment");

    ("--lim-file",
     Arg.Tuple
       (let lim = ref 0 in
        [Arg.Set_int lim;
         Arg.String
           (fun fn ->
            Config.interactive_shell := false ;
            add_file ~lim:!lim ~once:false true fn)]),
     "<lim> <file> Process <file> up to the end of the statement at character\
      <lim>, do not enter interactive mode");
  ]

(** Parser wrapper that reads extra lines on demand. *)
let parse lex parse resource =
  try
    lex parse resource
  with
  | Ulexbuf.Parse_Error (w, p_start, p_end) ->
     let loc = Location.make p_start p_end in
     Error.syntax ~loc "Unexpected: %s" w

let (>>=) = Value.top_bind
let (>>) m1 m2 = m1 >>= fun () -> m2
let return = Value.top_return

let rec fold f acc = function
  | [] -> return acc
  | x::rem -> f acc x >>= fun acc ->
    fold f acc rem

(** [exec_cmd d] executes toplevel command [c].
    It prints the result if in interactive mode.
    The environment is passed through a state monad. *)
let rec exec_cmd base_dir interactive c =
  Value.top_get_env >>= fun env ->
  Value.top_bound_names >>= fun xs ->
  let (c', loc) = Desugar.toplevel env xs c in
  match c' with

  | Syntax.Operation (x, k) ->
     Value.add_operation ~loc x k >>
     (if interactive then Format.printf "Operation %t is declared.@." (Name.print_ident x) ;
     return ())

  | Syntax.Data (x, k) ->
     Value.add_data ~loc x k >>
     (if interactive then Format.printf "Data constructor %t is declared.@." (Name.print_ident x) ;
     return ())

  | Syntax.Axiom (x, ryus, c) ->
     Eval.comp_constant ryus c >>= fun yrusv ->
     Value.add_constant ~loc x yrusv >>
     (if interactive then Format.printf "Constant %t is declared.@." (Name.print_ident x) ;
     return ())

  | Syntax.TopHandle lst ->
    fold (fun () (op, xc) ->
        Eval.comp_handle xc >>= fun f ->
        Value.add_handle op f) () lst

  | Syntax.TopLet (x, c) ->
     Eval.comp_value c >>= fun v ->
     Value.add_topbound ~loc x v >>
     (if interactive then Format.printf "%t is defined.@." (Name.print_ident x) ;
     return ())

  | Syntax.TopCheck c ->
     Eval.comp_value c >>= fun v ->
     let v = Simplify.value v in
     Value.top_print_value >>= fun print_value ->
     (if interactive then Format.printf "%t@." (print_value v) ;
     return ())

  | Syntax.Include (fs,once) ->
    fold (fun () f ->
         (* don't print deeper includes *)
         if interactive then Format.printf "#including %s@." f ;
           let f =
             if Filename.is_relative f
             then Filename.concat base_dir f
             else f
           in
           use_file (f, None, false, once) >>
           (if interactive then Format.printf "#processed %s@." f ;
           return ())) () fs

  | Syntax.Verbosity i -> Config.verbosity := i; return ()

  | Syntax.Environment ->
    Value.print_env >>= fun p ->
    Format.printf "%t@." p;
    return ()

  | Syntax.Help ->
    Format.printf "%s@." help_text ; return ()

  | Syntax.Quit ->
    exit 0


(** Load directives from the given file. *)
and use_file (filename, line_limit, interactive, once) =
  (if once then Value.included filename else return false) >>= fun skip ->
  if skip then return () else
    begin
      let cmds = parse (Lexer.read_file ?line_limit) Parser.file filename in
      let base_dir = Filename.dirname filename in
      Value.push_file filename >>
      fold (fun () c -> exec_cmd base_dir interactive c) () cmds
    end

(** Interactive toplevel *)
let toplevel cmp =
  Format.printf "Andromeda %s@\n[Type #help for help.]@." Build.version ;
  try
    let pc = ref (Value.initial cmp) in
    while true do
      try
        let cmd = parse Lexer.read_toplevel Parser.commandline () in
        pc := Value.progress !pc (fun () -> exec_cmd Filename.current_dir_name true cmd)
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
    (fun str -> add_file ~once:false true str ; Config.interactive_shell := false)
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
    | Config.PreludeFile f -> add_file ~once:false false f
    | Config.PreludeDefault ->
      (* look for prelude next to the executable and in the , don't whine if it is not there *)
      try
        let d = Build.lib_dir in
        let d' = Filename.dirname Sys.argv.(0) in
        let l = List.map (fun d -> Filename.concat d "prelude.m31") [d; d'] in
        let f = List.find (fun f ->  Sys.file_exists f) l in
        add_file ~once:false false f
      with Not_found -> ()
  end ;

  (* Set the maximum depth of pretty-printing, after which it prints ellipsis. *)
  Format.set_max_boxes 42 ;
  Format.set_ellipsis_text "..." ;
  try
    (* Run and load all the specified files. *)
    let comp = fold (fun () f -> use_file f) () !files in
    if !Config.interactive_shell
      then toplevel comp
      else Value.run comp
  with
    Error.Error err -> Error.print err Format.err_formatter; exit 1

