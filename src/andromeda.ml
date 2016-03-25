(** Andromeda main program *)

(** The usage message. *)
let usage = "Usage: andromeda [option] ... [file] ..."

(** A list of files to be loaded and run, together with information on whether they should
    be loaded in interactive mode. *)
let files = ref []

(** Add a file to the list of files to be loaded, and record whether it should
    be processed in interactive mode. *)
let add_file quiet filename = (files := (filename, quiet) :: !files)

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

    ("--global-atom-printer",
     Arg.Set Config.global_atom_printer,
     " Do print the freshness-index subscripts of atoms on a global basis");

    ("--max-boxes",
     Arg.Set_int Config.max_boxes,
     " Set the maximum depth of pretty printing");

    ("--columns",
     Arg.Set_int Config.columns,
     " Set the maximum number of columns of pretty printing");

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
     Arg.String (fun str -> add_file true str),
     "<file> Load <file> into the initial environment");
  ]

(** Interactive toplevel *)
let interactive_shell state =
  Format.printf "Andromeda %s@ [https://andromedans.github.io/andromeda/]@." Build.version ;
  let rec loop state =
    let state =
      try
        Toplevel.exec_interactive state
      with
      | Toplevel.Error err ->
         Format.eprintf "%t@." (Toplevel.print_located_error err) ; state
      | Sys.Break -> Format.eprintf "Interrupted.@."; state
    in loop state
  in
  loop state

(** Main program *)
let main =
  Sys.catch_break true ;
  (* Parse the arguments. *)
  Arg.parse
    options
    (fun str -> add_file false str ; Config.interactive_shell := false)
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
    | Config.PreludeFile f -> add_file true f
    | Config.PreludeDefault ->
      (* look for prelude next to the executable and in the , don't whine if it is not there *)
      try
        let d = Build.lib_dir in
        let d' = Filename.dirname Sys.argv.(0) in
        let l = List.map (fun d -> Filename.concat d "prelude.m31") [d; d'] in
        let f = List.find (fun f ->  Sys.file_exists f) l in
        add_file true f
      with Not_found -> ()
  end ;

  (* Set the maximum depth of pretty-printing, after which it prints ellipsis. *)
  Format.set_max_boxes !Config.max_boxes ;
  Format.set_margin !Config.columns ;
  Format.set_ellipsis_text "..." ;
  try

    (* Run and load all the specified files. *)
    let topstate =
      List.fold_left
        (fun topstate (fn, quiet) -> Toplevel.use_file ~fn ~quiet topstate)
        Toplevel.initial !files in

    if !Config.interactive_shell
      then interactive_shell topstate
      else ()

  with
    | Toplevel.Error err ->
       Format.eprintf "%t@." (Toplevel.print_located_error err) ; exit 1
    | End_of_file -> ()

