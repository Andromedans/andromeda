(** Andromeda main program *)

(** The usage message. *)
let usage = "Usage: andromeda [option] ... [file] ..."

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
     " Print dependencies between free variables and inside terms");

    ("--no-subscripts",
     Arg.Set Config.print_dependencies,
     " Do not print the freshness-index subscripts of atoms");

    ("--max-boxes",
     Arg.Set_int Config.max_boxes,
     " Set the maximum depth of pretty printing");

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

(** Interactive toplevel *)
let toplevel cmp =
  Format.printf "Andromeda %s@\n[Type #help for help.]@." Build.version ;
  let rec fold state =
    let state =
      try
        let cmd = Eval.parse Lexer.read_toplevel Parser.commandline () in
        Value.progress state (fun () -> Eval.exec_cmd Filename.current_dir_name true cmd)
      with
      | Error.Error err -> Print.error "%t" (Error.print err); state
      | Sys.Break -> Format.eprintf "Interrupted.@."; state
    in fold state
  in
  fold (Value.initial cmp)

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
  Format.set_max_boxes !Config.max_boxes ;
  Format.set_ellipsis_text "..." ;
  try
    (* Run and load all the specified files. *)
    let comp = Value.top_fold (fun () f -> Eval.use_file f) () !files in
    if !Config.interactive_shell
      then toplevel comp
      else Value.run comp
  with
    | Error.Error err -> Print.error "%t" (Error.print err); exit 1
    | End_of_file -> ()

