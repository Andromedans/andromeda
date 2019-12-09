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

    ("--no-stdlib",
     Arg.Unit (fun () -> Config.stdlib_directory := Config.StdlibNone),
     " Do not add the standard library directory the load path");

    ("--stdlib",
     Arg.String (fun str -> Config.stdlib_directory := Config.StdlibDirectory str),
     "<directory> Specify the standard library directory to initially add to \
the load path");

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
    | Config.PreludeDefault prelude ->
      (* look for prelude next to the executable and in the library directory,
         warn if it is not found. *)
       let executable_dir = Filename.dirname Sys.argv.(0) in
       let candidates = List.map (fun d -> Filename.concat d prelude)
           [executable_dir; Build.lib_dir] in
       try
         let f = List.find (fun f -> Sys.file_exists f) candidates in
         add_file true f
       with Not_found ->
         Print.warning
           "%s:@\n@[<hv>%t@]"
           "Andromeda prelude module could not be found, looked in"
           (Print.sequence (fun fn ppf -> Format.fprintf ppf "%s" fn) "," candidates)
  end ;

  begin
    let cons_to_require d = Config.(require_dirs := d :: !require_dirs) in
    match !Config.stdlib_directory with
    | Config.StdlibNone -> ()
    | Config.StdlibDirectory d -> cons_to_require d
    | Config.StdlibDefault stdlib ->
      (* look for stdlib next to the executable and in the library directory,
         warn if it is not found. *)
       let executable_dir = Filename.dirname Sys.argv.(0) in
       let dirs =
         List.map (fun d -> Filename.concat d "stdlib")
           [executable_dir ; Build.lib_dir] in
       try
         let d = List.find (fun d -> Sys.(file_exists d && is_directory d)) dirs in
         cons_to_require d
       with Not_found ->
         Print.warning
           "%s:@\n@[<hv>%t@]"
           "Andromeda stdlib directory could not be found, looked in"
           (Print.sequence (fun fn ppf -> Format.fprintf ppf "%s" fn) "," dirs)
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

(* XXX un ugly hack to force the compiler to compile the equality checker.
   If you see this and you are not Andrej Bauer, you may safely delete it. *)
;;
Eqchk_equalizer.empty_checker
