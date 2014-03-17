(** Toplevel. *)

module Ctx = BrazilContext.Ctx

(** Should the interactive shell be run? *)
let interactive_shell = ref true

(** The command-line wrappers that we look for. *)
let wrapper = ref (Some ["rlwrap"; "ledit"])

(** The usage message. *)
let usage = "Usage: tt [option] ... [file] ..."

(** The help text printed when [#help] is used. *)
let help_text = "Toplevel directives:
#eval <expr> ;;                evaluate <expr>
#context ;;                    print current contex
#help ;;                       print this help
#quit ;;                       exit

assume <ident> : <sort> ;;     assume variable <ident> has sort <sort>
define <ident> := <expr> ;;    define <ident> to be <expr>
let <indent> := <comp> ;;      define <ident> to be the result of computation <comp>
[ <expr> :: <sort> ] ;;        check that <expr> has sort <sort>
[ <expr> :: ? ] ;;             infer the sort of expression <expr>
[ ? :: <sort> ] ;;             inhabit sort <sort>

Syntax:
Type                           the sort of types
<expr> :: <sort>               the sort of typing judgments
<expr> == <expr> @ <sort>      the sort of equality judgments
fun x : e1 => e2               function abstraction
forall x : e1, e2              dependent product
e1 e2                          application
" ;;

(** A list of files to be loaded and run. *)
let files = ref []

(** Add a file to the list of files to be loaded, and record whether it should
    be processed in interactive mode. *)
let add_file interactive filename = (files := (filename, interactive) :: !files)

(** A list of command-line wrappers to look for. *)
let wrapper = ref (Some ["rlwrap"; "ledit"])

(** Command-line options *)
let options = Arg.align [
  ("--wrapper",
    Arg.String (fun str -> wrapper := Some [str]),
    "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)");
  ("--no-wrapper",
    Arg.Unit (fun () -> wrapper := None),
    " Do not use a command-line wrapper");
  ("-v",
    Arg.Unit (fun () ->
      print_endline ("tt " ^ Version.version ^ "(" ^ Sys.os_type ^ ")");
      exit 0),
    " Print version information and exit");
  ("-V",
   Arg.Int (fun k -> BrazilPrint.verbosity := k),
   "<int> Set verbosity level");
  ("-n",
    Arg.Clear interactive_shell,
    " Do not run the interactive toplevel");
  ("-l",
    Arg.String (fun str -> add_file false str),
    "<file> Load <file> into the initial environment");
]

(** Treat anonymous arguments as files to be run. *)
let anonymous str =
  add_file true str;
  interactive_shell := false

(** Parser wrapper that reads extra lines on demand. *)
let parse parser lex =
  try
    parser Lexer.token lex
  with
  | Parser.Error ->
      Error.syntax ~loc:(Lexer.position_of_lex lex) ""
  | Failure "lexing: empty token" ->
      Error.syntax ~loc:(Lexer.position_of_lex lex) "unrecognised symbol."

(** [exec_cmd env d] executes toplevel directive [d] in context [env]. It prints the
    result if in interactive mode, and returns the new context. *)
let rec exec_cmd interactive env (d, loc) =
  let ctx = Typing.Infer.get_ctx env  in
  let ctx_names = ctx.Ctx.names in
  match d with
    | Input.Context ->
        let _ = Ctx.print ctx  in
        env
    | Input.TopParam (xs, t) ->
        let t    = Input.desugar ctx_names t in
        let env' = Typing.Infer.inferParam ~verbose:interactive env xs t  in
        env'
    | Input.TopDef (x, topt, e) ->
        let e    = Input.desugar ctx_names e in
        let topt = Input.desugar_opt ctx_names topt in
        let env' = Typing.Infer.inferDefinition ~verbose:interactive env x topt e  in
        env'
    | Input.TopHandler hs ->
        let hs   = Input.desugar_handler ctx_names hs   in
        let env' = Typing.Infer.addHandlers env loc hs in
        env'
    | Input.Help ->
      print_endline help_text ; env
    | Input.Quit -> exit 0

(** Load directives from the given file. *)
and use_file env (filename, interactive) =
  let cmds = Lexer.read_file (parse Parser.file) filename in
    List.fold_left (exec_cmd interactive) env cmds

(** Interactive toplevel *)
let toplevel env =
  let eof = match Sys.os_type with
    | "Unix" | "Cygwin" -> "Ctrl-D"
    | "Win32" -> "Ctrl-Z"
    | _ -> "EOF"
  in
  print_endline ("tt " ^ Version.version);
  print_endline ("[Type " ^ eof ^ " to exit or \"#help;;\" for help.]");
  try
    let env = ref env in
    while true do
      try
        let cmd = Lexer.read_toplevel (parse Parser.commandline) () in
        env := exec_cmd true !env cmd
      with
        | Error.Error err -> BrazilPrint.error err
        | Sys.Break -> prerr_endline "Interrupted."
    done
  with End_of_file -> ()

(** Main program *)
let main =
  Sys.catch_break true;
  (* Parse the arguments. *)
  Arg.parse options anonymous usage;
  (* Attempt to wrap yourself with a line-editing wrapper. *)
  if !interactive_shell then
    begin match !wrapper with
      | None -> ()
      | Some lst ->
          let n = Array.length Sys.argv + 2 in
          let args = Array.make n "" in
            Array.blit Sys.argv 0 args 1 (n - 2);
            args.(n - 1) <- "--no-wrapper";
            List.iter
              (fun wrapper ->
                 try
                   args.(0) <- wrapper;
                   Unix.execvp wrapper args
                 with Unix.Unix_error _ -> ())
              lst
    end;
  (* Files were listed in the wrong order, so we reverse them *)
  files := List.rev !files;
  (* Set the maximum depth of pretty-printing, after which it prints ellipsis. *)
  Format.set_max_boxes 42 ;
  Format.set_ellipsis_text "..." ;
  try
    (* Run and load all the specified files. *)
    let env = List.fold_left use_file Typing.Infer.empty_env !files in
    if !interactive_shell then
      toplevel env
    else
      print_endline "Verifying";
      let ctx = Typing.Infer.get_ctx env   in
      Brazil.Verify.verifyContext ctx
  with
    Error.Error err -> BrazilPrint.error err; exit 1
