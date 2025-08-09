(** Andromeda main program *)

(** The usage message. *)
let usage = "Usage: andromeda [option] ... [file] ..."

(** A list of files to be loaded and run, together with information on whether they should
    be loaded in interactive mode. *)
let files = ref []

(** Add a file to the list of files to be loaded, and record whether it should
    be processed in interactive mode. *)
let add_file quiet filename = (files := (filename, quiet) :: !files)

(** Set the version via build info *)
let version = match Build_info.V1.version () with
| None -> "n/a"
| Some v -> Build_info.V1.Version.to_string v

(** Command-line options *)
let options = Arg.align [
    ("-I",
     Arg.String (fun dir -> Config.require_dirs := !Config.require_dirs @ [dir]),
     " Look for required files in the given directory");

    ("--ascii",
      Arg.Set Config.ascii,
     " Print terms in ASCII format");

    ("--max-boxes",
     Arg.Set_int Config.max_boxes,
     " Set the maximum depth of pretty printing");

    ("--columns",
     Arg.Set_int Config.columns,
     " Set the maximum number of columns of pretty printing");

    ("--no-prelude",
     Arg.Unit (fun () -> Config.prelude_file := None),
     " Do not load the prelude.m31 file");

    ("--prelude",
     Arg.String (fun str -> Config.prelude_file := Some str),
     "<file> Specify the prelude file to load initially");

    ("--no-stdlib",
     Arg.Unit (fun () -> Config.stdlib_directory := None),
     " Do not add the standard library directory the load path");

    ("--stdlib",
     Arg.String (fun str -> Config.stdlib_directory := Some str),
     "<directory> Specify the standard library directory to initially add to \
the load path");

    ("--json-location",
     Arg.Set Config.json_location,
     " Print locations in JSON output");

    ("-v",
     Arg.Unit (fun () ->
         Format.printf "Andromeda %s (%s)@." version Sys.os_type ;
         exit 0),
     " Print version information and exit");

    ("-V",
     Arg.Set_int Config.verbosity,
     "<n> Set printing verbosity to <n>");

    ("-n",
     Arg.Clear Config.interactive_shell,
     " Do not run the interactive toplevel");
  ]

(** Interactive toplevel *)
let interactive_shell state =
  Format.printf "Andromeda %s@ [https://www.andromeda-prover.org/]@." version ;
  let rec loop state =
    let state =
      try
        Toplevel.exec_interactive state
      with
      | Toplevel.Error err ->
         Format.eprintf "@[<hov 2>%t@]@." (Toplevel.print_error state err) ; state
      | Sys.Break -> Format.eprintf "Interrupted.@."; state
      | End_of_file -> exit 0
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
  (* Files were accumulated in the wrong order, so we reverse them *)
  files := List.rev !files ;
  (* Should we load the prelude file? *)
  begin
    match !Config.prelude_file with
    | None -> ()
    | Some f -> add_file true f
  end ;

  begin
    match !Config.stdlib_directory with
    | None -> ()
    | Some d -> Config.(require_dirs := d :: !require_dirs)
  end ;

  (* Set the maximum depth of pretty-printing, after which it prints ellipsis. *)
  Format.set_max_boxes !Config.max_boxes ;
  Format.set_margin !Config.columns ;
  Format.set_ellipsis_text "..." ;

  (* Run and load all the specified files. *)
  let rec process_files state  = function
    | [] -> state
    | (fn, quiet) :: files ->
       begin
         try
           let state = Toplevel.use_file ~quiet fn state in
           process_files state files
         with
         | Toplevel.Error err ->
            Format.eprintf "@[<hov 2>%t@]@." (Toplevel.print_error state err) ;
            exit 1
       end
  in
  let state = process_files Toplevel.initial_environment !files in
  if !Config.interactive_shell
  then interactive_shell state
  else ()
