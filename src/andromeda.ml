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

    ("--ascii",
      Arg.Set Config.ascii,
     " Print terms in ASCII format");

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
         Format.printf "Andromeda %s (%s)@." Build.version Sys.os_type ;
         exit 0),
     " Print version information and exit");

    ("-V",
     Arg.Set_int Config.verbosity,
     "<n> Set printing verbosity to <n>");

    ("--ignore-hints",
     Arg.Set Config.ignore_hints,
     " Ignore all installed rewrite hints");

    ("-n",
     Arg.Clear Config.interactive_shell,
     " Do not run the interactive toplevel");

    ("-l",
     Arg.String (fun str -> add_file false str),
     "<file> Load <file> into the initial environment");
  ]

(** Parser wrapper that reads extra lines on demand. *)
let parse lex parse resource =
  try
    lex parse resource
  with
  | Ulexbuf.Parse_Error (w, p_start, p_end) ->
     let loc = Location.make p_start p_end in
     Error.syntax ~loc "Unexpected: %s" w

(** [exec_cmd ctx d] executes toplevel command [c] in context [ctx]. It prints the
    result if in interactive mode, and returns the new context. *)
let rec exec_cmd base_dir interactive ctx c =
  let (c', loc) = Desugar.toplevel (Context.primitives ctx) (Context.bound_names ctx) c in
  match c' with

  | Syntax.Primitive (xs, yts, u) ->
    let rec fold ctx zs yts' = function
      | [] ->
        let u = Eval.ty ctx u in
        let u = Tt.abstract_ty zs 0 u in
        let yts' = List.rev yts' in
        (yts', u)
      | (y, reducing, t)::yts ->
        let t = Eval.ty ctx t in
        let z, v = Value.fresh ~loc y t in
        let ctx = Context.add_bound y v ctx in
        let t = Tt.abstract_ty zs 0 t in
        fold ctx (z::zs) ((y, (reducing, t)) :: yts') yts
    in
    let ytsu = fold ctx [] [] yts in
    let ctx =
      List.fold_left (fun ctx x -> Context.add_primitive x ytsu ctx) ctx xs in
    if interactive then
      List.iter (fun x -> Format.printf "%t is assumed.@." (Name.print x)) xs ;
    ctx

  | Syntax.TopLet (x, c) ->
     let v = Eval.comp_value ctx c in
     let ctx = Context.add_bound x v ctx in
     if interactive then Format.printf "%t is defined.@." (Name.print x) ;
     ctx

  | Syntax.TopCheck c ->
     let v = 
       begin match Eval.comp_value ctx c with
             | Value.Judge (e, t) ->
                let e = Simplify.simplify ctx e
                and t = Simplify.simplify_ty ctx t in
                  Value.Judge (e, t)
             | v -> v
       end
     in
       if interactive then Format.printf "%t@." (Value.print (Context.used_names ctx) v) ;
       ctx

  | Syntax.TopBeta xscs ->
    let rec fold xshs = function
      | [] ->
        let xshs = List.rev xshs in
        let ctx = Context.add_betas xshs ctx in
        Print.debug "Installed beta hints@ %t"
          (Print.sequence (fun (tags, (_, h)) ppf ->
               Print.print ppf "@[tags: %s ;@ hint: %t@]"
                 (String.concat " " tags)
                 (Pattern.print_beta_hint [] h)) "," xshs);
        ctx
      | (xs,c) :: xscs ->
         let (_,t) = Value.as_judge ~loc (Eval.comp_value ctx c) in
         let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
         let h = Hint.mk_beta ~loc ctx (xts, (t, e1, e2)) in
         fold ((xs,h) :: xshs) xscs
    in fold [] xscs

  | Syntax.TopEta xscs ->
    let rec fold xshs = function
      | [] ->
        let xshs = List.rev xshs in
        let ctx = Context.add_etas xshs ctx in
        Print.debug "Installed eta hints@ %t"
          (Print.sequence (fun (tags, (_, h)) ppf ->
               Print.print ppf "@[tags: %s ;@ hint: %t@]"
                 (String.concat " " tags)
                 (Pattern.print_eta_hint [] h)) "," xshs);
        ctx
      | (xs,c) :: xscs ->
         let (_,t) = Value.as_judge ~loc (Eval.comp_value ctx c) in
         let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
         let h = Hint.mk_eta ~loc ctx (xts, (t, e1, e2)) in
         fold ((xs,h) :: xshs) xscs
    in fold [] xscs

  | Syntax.TopHint xscs ->
    let rec fold xshs = function
      | [] ->
        let xshs = List.rev xshs in
        let ctx = Context.add_generals xshs ctx in
        Print.debug "Installed general hints@ %t"
          (Print.sequence (fun (tags, (_, h)) ppf ->
               Print.print ppf "@[tags: %s ;@ hint: %t@]"
                 (String.concat " " tags)
                 (Pattern.print_hint [] h)) "," xshs);
        ctx
      | (xs,c) :: xscs ->
         let (_,t) = Value.as_judge ~loc (Eval.comp_value ctx c) in
         let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
         let h = Hint.mk_general ~loc ctx (xts, (t, e1, e2)) in
         fold ((xs,h) :: xshs) xscs
    in fold [] xscs

  | Syntax.TopInhabit xscs ->
    let rec fold xshs = function
      | [] ->
        let xshs = List.rev xshs in
        let ctx = Context.add_inhabits xshs ctx in
        Print.debug "Installed inhabit hints@ %t"
          (Print.sequence (fun (tags, (_, h)) ppf ->
               Print.print ppf "@[tags: %s ;@ hint: %t@]"
                 (String.concat " " tags)
                 (Pattern.print_inhabit_hint [] h)) "," xshs);
        ctx
      | (xs,c) :: xscs ->
         let (_,t) = Value.as_judge ~loc (Eval.comp_value ctx c) in
         let (xts, u) = Equal.as_universal_bracket ctx t in
         let h = Hint.mk_inhabit ~loc ctx (xts, u) in
         fold ((xs,h) :: xshs) xscs
    in fold [] xscs

  | Syntax.TopUnhint xs -> Context.unhint xs ctx

  | Syntax.Include fs ->
    (* relative file names get interpreted relative to the file we're
       currently loading *)
    List.fold_left
      (fun ctx f ->
         (* don't print deeper includes *)
         begin if interactive then Format.printf "#including %s@." f ;
           let ctx =
             let f =
               if Filename.is_relative f then
                 Filename.concat base_dir f
               else f in
             use_file ctx (f, false) in
           if interactive then Format.printf "#processed %s@." f ;
           ctx
         end)
      ctx fs

  | Syntax.Verbosity i -> Config.verbosity := i; ctx

  | Syntax.Context ->
    Format.printf "%t@." (Context.print ctx) ;
    ctx

  | Syntax.Help ->
    Format.printf "%s@." help_text ; ctx

  | Syntax.Quit ->
    exit 0


(** Load directives from the given file. *)
and use_file ctx (filename, interactive) =
  let filename, limit =
    if Str.string_match (Str.regexp "\\(.*\\)#line_limit:\\([0-9]+\\)") filename 0
    then let fn, lim = Str.matched_group 1 filename,
                      (int_of_string (Str.matched_group 2 filename)) in
         let limit = { Lexing.dummy_pos with Lexing.pos_cnum = lim } in
      fn, Some (limit, true)
    else filename, None in

  if Context.included filename ctx then ctx else
    begin
      let tokens, errs = Tokens.tokens_of_file filename in

      let cmds = parse (Tokens.cmds_of_tokens ?limit) tokens errs in

      let base_dir = Filename.dirname filename in
      let ctx = Context.add_file filename ctx in
      List.fold_left (exec_cmd base_dir interactive) ctx cmds
    end

(** Interactive toplevel *)
let toplevel ctx =
  Format.printf "Andromeda %s@\n[Type #help for help.]@." Build.version ;
  try
    let ctx = ref ctx in
    while true do
      try
        let cmd = parse Lexer.read_toplevel Parser.commandline () in
        ctx := exec_cmd Filename.current_dir_name true !ctx cmd
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
      (* look for prelude next to the executable and in the , don't whine if it is not there *)
      try
        let d = Build.lib_dir in
        let d' = Filename.dirname Sys.argv.(0) in
        let l = List.map (fun d -> Filename.concat d "prelude.m31") [d; d'] in
        let f = List.find (fun f ->  Sys.file_exists f) l in
        files := (f, false) :: !files
      with Not_found -> ()
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

