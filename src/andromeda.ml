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
let add_file ?lim interactive filename = (files := (filename, lim, interactive) :: !files)

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

    ("--ignore-hints",
     Arg.Set Config.ignore_hints,
     " Ignore all installed hints");

    ("-n",
     Arg.Clear Config.interactive_shell,
     " Do not run the interactive toplevel");

    ("-l",
     Arg.String (fun str -> add_file false str),
     "<file> Load <file> into the initial environment");

    ("--lim-file",
     Arg.Tuple
       (let lim = ref 0 in
        [Arg.Set_int lim;
         Arg.String
           (fun fn ->
            Config.interactive_shell := false ;
            add_file ~lim:!lim true fn)]),
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

(** [exec_cmd env d] executes toplevel command [c] in environment [env]. It prints the
    result if in interactive mode, and returns the new environment. *)
let rec exec_cmd base_dir interactive env c =
  let (c', loc) = Desugar.toplevel env (Value.Env.bound_names env) c in
  match c' with

  | Syntax.Operation (x, k) ->
     let env = Value.Env.add_operation ~loc x k env in
     if interactive then Format.printf "Operation %t is declared.@." (Name.print_ident x) ;
     env

  | Syntax.Data (x, k) ->
     let env = Value.Env.add_data ~loc x k env in
     if interactive then Format.printf "Data constructor %t is declared.@." (Name.print_ident x) ;
     env

  | Syntax.Axiom (x, ryus, c) ->
     (* XXX this is seriously messed up with respect to contexts. *)
     let rec fold env ctx zs yrws = function
       | [] ->
          let (ctxt, t') = Eval.comp_ty env c in
          let t' = Tt.abstract_ty zs t' in
          let ctx = Context.join ~loc ctxt ctx in
          let yrws = List.rev yrws in
          (ctx, (yrws, t'))
       | (r, (y, c)) :: ryus ->
          let ((ctxu, u) as ju) = Eval.comp_ty env c in
          let _, z, env = Value.Env.add_abstracting ~loc:Location.unknown env y ju in
          let w = Tt.abstract_ty zs u in
          let ctx = Context.join ~loc ctx ctxu in
          fold env ctx (z :: zs) ((y, (r, w)) :: yrws) ryus in
     let ctx, yrusv = fold env Context.empty [] [] ryus in
     (* XXX do sth with ctx *)
     let env = Value.Env.add_constant ~loc x yrusv env in
     if interactive then Format.printf "Constant %t is declared.@." (Name.print_ident x) ;
     env

  | Syntax.TopHandle lst ->
     List.fold_left (fun env (op, xc) ->
        let f = Eval.comp_handle env xc in
        Value.Env.add_handle op f env)
      env lst

  | Syntax.TopLet (x, c) ->
     let v = Eval.comp_value env c in
     let env = Value.Env.add_bound x v env in
     if interactive then Format.printf "%t is defined.@." (Name.print_ident x) ;
     env

  | Syntax.TopCheck c ->
     let v =
       begin match Eval.comp_value env c with
             | Value.Ty (ctx, t) ->
                let ctx = Simplify.context ctx in
                let t = Simplify.ty t in
                let j = Judgement.mk_ty ctx t in
                Value.Ty j
             | Value.Term (ctx, e, t) ->
                let ctx = Simplify.context ctx in
                let e = Simplify.term e
                and t = Simplify.ty t in
                let j = Judgement.mk_term ctx e t in
                  Value.Term j
             | v -> v
       end
     in
       if interactive then Format.printf "%t@." (Value.print_value (Value.Env.used_names env) v) ;
       env

  | Syntax.Include fs ->
    (* relative file names get interpreted relative to the file we're
       currently loading *)
    List.fold_left
      (fun env f ->
         (* don't print deeper includes *)
         begin if interactive then Format.printf "#including %s@." f ;
           let env =
             let f =
               if Filename.is_relative f then
                 Filename.concat base_dir f
               else f in
             use_file env (f, None, false) in
           if interactive then Format.printf "#processed %s@." f ;
           env
         end)
      env fs

  | Syntax.Verbosity i -> Config.verbosity := i; env

  | Syntax.Environment ->
    Format.printf "%t@." (Value.Env.print env) ;
    env

  | Syntax.Help ->
    Format.printf "%s@." help_text ; env

  | Syntax.Quit ->
    exit 0


(** Load directives from the given file. *)
and use_file env (filename, line_limit, interactive) =
  if Value.Env.included filename env then env else
    begin
      let cmds = parse (Lexer.read_file ?line_limit) Parser.file filename in
      let base_dir = Filename.dirname filename in
      let env = Value.Env.add_file filename env in
      List.fold_left (exec_cmd base_dir interactive) env cmds
    end

(** Interactive toplevel *)
let toplevel env =
  Format.printf "Andromeda %s@\n[Type #help for help.]@." Build.version ;
  try
    let env = ref env in
    while true do
      try
        let cmd = parse Lexer.read_toplevel Parser.commandline () in
        env := exec_cmd Filename.current_dir_name true !env cmd
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
    | Config.PreludeFile f -> files := (f, None, false) :: !files
    | Config.PreludeDefault ->
      (* look for prelude next to the executable and in the , don't whine if it is not there *)
      try
        let d = Build.lib_dir in
        let d' = Filename.dirname Sys.argv.(0) in
        let l = List.map (fun d -> Filename.concat d "prelude.m31") [d; d'] in
        let f = List.find (fun f ->  Sys.file_exists f) l in
        files := (f, None, false) :: !files
      with Not_found -> ()
  end ;

  (* Set the maximum depth of pretty-printing, after which it prints ellipsis. *)
  Format.set_max_boxes 42 ;
  Format.set_ellipsis_text "..." ;
  try
    let env = Value.Env.empty in
    (* Declare predefined data constructors *)
    let env = List.fold_left
                (fun env (x, k) -> Value.Env.add_data ~loc:Location.unknown x k env)
                env
                Value.predefined_tags
    in
    (* Declare predefined operations *)
    let env = List.fold_left
                (fun env (x, k) -> Value.Env.add_operation ~loc:Location.unknown x k env)
                env
                Value.predefined_ops
    in    
    (* Run and load all the specified files. *)
    let env = List.fold_left use_file env !files in
    if !Config.interactive_shell then
      toplevel env
  with
    Error.Error err -> Error.print err Format.err_formatter; exit 1

