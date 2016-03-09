(** A toplevel computation carries around the current
    environment. *)
type topenv = {
  runtime : Runtime.env ;
  typing : Mlty.Ctx.t
}

type 'a toplevel = topenv -> 'a * topenv

let comp_value c =
  let r = Eval.infer c in
  Runtime.top_handle ~loc:c.Syntax.loc r

let comp_handle (xs,y,c) =
  Runtime.top_return_closure (fun (vs,checking) ->
      let rec fold2 xs vs = match xs,vs with
        | [], [] ->
           begin match y with
           | Some y ->
              let checking = match checking with
                | Some jt -> Some (Runtime.mk_term (Jdg.term_of_ty jt))
                | None -> None
              in
              let vy = Predefined.from_option checking in
              Runtime.add_bound y vy (Eval.infer c)
           | None -> Eval.infer c
           end
        | x::xs, v::vs -> Runtime.add_bound x v (fold2 xs vs)
        | [],_::_ | _::_,[] -> Error.impossible ~loc:(c.Syntax.loc) "bad top handler case"
      in
      fold2 xs vs)

let comp_signature ~loc lxcs =
  let (>>=) = Runtime.bind in
  let rec fold ys yts lxts = function
    | [] ->
       let lxts = List.rev lxts in
       Runtime.return lxts

    | (l,x,c) :: lxcs ->
       Eval.check_ty c >>= fun (Jdg.Ty (ctxt,t)) ->
       if not (Context.is_subset ctxt yts)
       then Error.runtime ~loc "signature field %t has unresolved assumptions"
           (Name.print_ident l)
       else begin
         let jt = Jdg.mk_ty ctxt t
         and tabs = Tt.abstract_ty ys t in
         Runtime.add_abstracting ~loc x jt (fun _ y ->
             fold (y::ys) ((y,t)::yts) ((l,x,tabs) :: lxts) lxcs)
       end
  in
  Runtime.top_handle ~loc (fold [] [] [] lxcs)


(** Evaluation of toplevel computations *)

let parse lex parse resource =
  try
    lex parse resource
  with
  | Ulexbuf.Parse_Error (w, p_start, p_end) ->
     let loc = Location.make p_start p_end in
     Error.syntax ~loc "Unexpected: %s" w


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


let (>>=) = Runtime.top_bind
let return = Runtime.top_return

let rec mfold f acc = function
  | [] -> return acc
  | x::rem -> f acc x >>= fun acc ->
     mfold f acc rem

let add_predefined_runtime =
  (* Declare predefined data constructors *)
  mfold
    (fun () (x, _) -> Runtime.add_data ~loc:Location.unknown x)
    ()
    Predefined.predefined_tags
  >>= fun () ->
  (* Declare predefined operations *)
  mfold
    (fun () (x, _) -> Runtime.add_operation ~loc:Location.unknown x)
    ()
    Predefined.predefined_ops

let initial = ()

let toplet_bind ~loc interactive xcs =
  let rec fold xvs = function
    | [] ->
       (* parallel let: only bind at the end *)
       List.fold_left
         (fun cmd (x,v) ->
            Runtime.add_topbound ~loc x v >>= fun () ->
            if interactive && not (Name.is_anonymous x)
            then Format.printf "%t is defined.@." (Name.print_ident x) ;
            cmd)
         (return ())
         xvs
    | (x, c) :: xcs ->
       comp_value c >>= fun v ->
       fold ((x, v) :: xvs) xcs
  in
  fold [] xcs

let topletrec_bind ~loc interactive fxcs =
  let gs =
    List.map
      (fun (f, x, c) -> (f, (fun v -> Runtime.add_bound x v (Eval.infer c))))
      fxcs
  in
  Runtime.add_topbound_rec ~loc gs >>= fun () ->
  if interactive then
    List.iter (fun (f, _, _) ->
        if not (Name.is_anonymous f) then
          Format.printf "%t is defined.@." (Name.print_ident f)) fxcs ;
  return ()

let rec exec_cmd base_dir interactive c {runtime; typing} =
  let (c, loc) = Desugar.toplevel typing c in
  let typing = Mlty.infer (c, loc) typing in
  match c with

  | Syntax.DeclOperation (x, k) ->
     Runtime.add_operation ~loc x k >>= fun () ->
     if interactive then Format.printf "Operation %t is declared.@." (Name.print_ident x) ;
     return ()

  | Syntax.DeclData (x, k) ->
     Runtime.add_data ~loc x k >>= fun () ->
     if interactive then Format.printf "Data constructor %t is declared.@." (Name.print_ident x) ;
     return ()

  | Syntax.DeclConstants (xs, c) ->
     Runtime.top_handle ~loc:(c.Syntax.loc) (Eval.check_ty c) >>= fun (Jdg.Ty (ctxt, t)) ->
     if Context.is_empty ctxt
     then
       let rec fold = function
         | [] -> return ()
         | x :: xs ->
            Runtime.add_constant ~loc x t >>= fun () ->
            (if interactive then Format.printf "Constant %t is declared.@." (Name.print_ident x) ;
             fold xs)
       in
       fold xs
     else
       Error.typing "Constants may not depend on free variables" ~loc:(c.Syntax.loc)

  | Syntax.DeclSignature (s, lxcs) ->
     comp_signature ~loc lxcs >>= fun lxts ->
     Runtime.add_signature ~loc s lxts  >>= fun () ->
     (if interactive then Format.printf "Signature %t is declared.@." (Name.print_ident s) ;
      return ())

  | Syntax.TopHandle lst ->
     mfold (fun () (op, xc) ->
         comp_handle xc >>= fun f ->
         Runtime.add_handle op f) () lst

  | Syntax.TopLet xcs ->
     toplet_bind ~loc interactive xcs

  | Syntax.TopLetRec fxcs ->
     topletrec_bind ~loc interactive fxcs

  | Syntax.TopDynamic (x,c) ->
     comp_value c >>= fun v ->
     Runtime.add_dynamic ~loc x v

  | Syntax.TopNow (x,c) ->
     comp_value c >>= fun v ->
     Runtime.top_now ~loc x v

  | Syntax.TopDo c ->
     comp_value c >>= fun v ->
     Runtime.top_print_value >>= fun print_value ->
     (if interactive then Format.printf "%t@." (print_value v) ;
      return ())

  | Syntax.TopFail c ->
     Runtime.catch (fun () -> comp_value (Lazy.force c)) >>= begin function
     | Error.Err err ->
        (if interactive then Format.printf "The command failed with error:\n%t@." (Error.print err));
        return ()
     | Error.OK v ->
        Runtime.top_print_value >>= fun pval ->
        Error.runtime ~loc "The command has not failed: got %t." (pval v)
     end

  | Syntax.Include (fs,once) ->
     mfold (fun () f ->
         (* don't print deeper includes *)
         if interactive then Format.printf "#including %s@." f ;
         let f =
           if Filename.is_relative f
           then Filename.concat base_dir f
           else f
         in
         use_file (f, None, false, once) >>= fun () ->
         (if interactive then Format.printf "#processed %s@." f ;
          return ())) () fs

  | Syntax.Verbosity i -> Config.verbosity := i; return ()

  | Syntax.Environment ->
     Runtime.print_env >>= fun p ->
     Format.printf "%t@." p;
     return ()

  | Syntax.Help ->
     Format.printf "%s@." help_text ; return ()

  | Syntax.Quit ->
     exit 0

and use_file ~fn ~limit ~interactive ~state =
  if Runtime.included fn then return () else
    begin
      let cmds = parse (Lexer.read_file ?line_limit) Parser.file fn in
      let base_dir = Filename.dirname fn in
      let typing, cmds = typecheck cmds typing in
      Runtime.push_file fn >>= fun () ->
      mfold (fun () c -> chain_cmd base_dir interactive c) () cmds
    end
