(** Toplevel. *)

module Ctx = BrazilContext.Ctx
module BI = BrazilInput
module BT = BrazilTyping
module BP = BrazilPrint

(** Should the interactive shell be run? *)
let interactive_shell = ref true

(** The command-line wrappers that we look for. *)
let wrapper = ref (Some ["rlwrap"; "ledit"])

(** The usage message. *)
let usage = "Usage: tt [option] ... [file] ..."

(** The help text printed when [#help] is used. *)
let help_text = "Toplevel directives:
#context ;;                    print current contex
#help ;;                       print this help
#quit ;;                       exit

assume <ident> : <sort> ;;     assume variable <ident> has sort <sort>
define <ident> := <expr> ;;    define <ident> to be <expr>

Syntax:
...";;
(*
"Type                           the sort of types
<expr> :: <sort>               the sort of typing judgments
<expr> == <expr> @ <sort>      the sort of equality judgments
fun x : e1 => e2               function abstraction
forall x : e1, e2              dependent product
e1 e2                          application
" ;;
*)

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
   Arg.Int (fun k -> BP.verbosity := k),
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
    parser BrazilLexer.token lex
  with
  | BrazilParser.Error ->
      Error.syntax ~loc:(BrazilLexer.position_of_lex lex) ""
  | Failure "lexing: empty token" ->
      Error.syntax ~loc:(BrazilLexer.position_of_lex lex) "unrecognised symbol."

(** [exec_cmd env d] executes toplevel directive [d] in context [env]. It prints the
    result if in interactive mode, and returns the new context. *)
let rec exec_cmd interactive env (d, loc) =
  match d with
    | BI.Context ->
        let _ = Ctx.print env.BT.ctx  in
        env
    | BI.TopParam (xs, t) ->
        let t = BI.desugar env.BT.ctx.Ctx.names t in
        let env' = BT.inferParam ~verbose:interactive env xs t  in
        env'
    | BI.TopDef (x, e) ->
        let e = BI.desugar env.BT.ctx.Ctx.names e in
        let env' = BT.inferDefinition ~verbose:interactive env x e  in
        env'
    | BI.TopHandler hs ->
        let hs = List.map (BI.desugar env.BT.ctx.Ctx.names) hs   in
        let env' = BT.addHandlers env hs in
        env'
    | BI.Help ->
      print_endline help_text ; env
    | BI.Quit -> exit 0

(** Load directives from the given file. *)
and use_file env (filename, interactive) =
  let cmds = BrazilLexer.read_file (parse BrazilParser.file) filename in
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
        let cmd = BrazilLexer.read_toplevel (parse BrazilParser.commandline) () in
        env := exec_cmd true !env cmd
      with
        | Error.Error err -> BP.error err
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
    let env = List.fold_left use_file BT.empty_env !files in
    if !interactive_shell then toplevel env
  with
    Error.Error err -> BP.error err; exit 1
