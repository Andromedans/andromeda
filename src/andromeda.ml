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

    ("--json-location",
     Arg.Set Config.json_location,
     " Print locations in JSON output");

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
  ]

(** Interactive toplevel *)
let interactive_shell state =
  Format.printf "Andromeda %s@ [https://www.andromeda-prover.org/]@." Build.version ;
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
      (* look for prelude next to the executable and in the library directory,
         warn if it is not found. *)
       let d = Build.lib_dir in
       let d' = Filename.dirname Sys.argv.(0) in
       let l = List.map (fun d -> Filename.concat d "prelude.m31") [d'; d] in
       try
         let f = List.find (fun f -> Sys.file_exists f) l in
         add_file true f
       with Not_found ->
         Print.warning
           "%s:@\n@[<hv>%t@]"
           "Andromeda prelude module could not be found, looked in"
           (Print.sequence (fun fn ppf -> Format.fprintf ppf "%s" fn) "," l)
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
