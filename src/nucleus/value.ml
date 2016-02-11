(** Runtime values and results *)

(* Information about a toplevel declaration *)
type decl =
  | DeclConstant of Tt.ty
  | DeclData of int
  | DeclOperation of int
  | DeclSignature of Tt.sig_def

type dynamic = {
  decls : (Name.ident * decl) list ;
  (* Toplevel declaration *)

  abstracting : Jdg.term list;
  (* The list of judgments about atoms which are going to be abstracted. We
     should avoid creating atoms which depends on these, as this will prevent
     abstraction from working. The list is in the reverse order from
     abstraction, i.e., the inner-most abstracted variable appears first in the
     list. *)
}

type lexical = {
  bound : (Name.ident * value) list;
  continuation : (value,value) closure option;
  handle : (Name.ident * (value list * Jdg.ty option,value) closure) list;
  files : string list;
}

and state = value Store.t

and value =
  | Term of Jdg.term
  | Closure of (value, value) closure
  | Handler of handler
  | Tag of Name.ident * value list
  | List of value list
  | Tuple of value list
  | Ref of Store.key
  | String of string
  | Ident of Name.ident

(* It's important not to confuse the closure and the underlying ocaml function *)
and ('a, 'b) closure = Clos of ('a -> 'b result)

and 'a raw_result =
  | Return of 'a
  | Operation of Name.ident * value list * Jdg.ty option * dynamic * (value,'a) closure

and 'a result = env -> 'a raw_result * state

and operation_args = { args : value list; checking : Jdg.ty option; cont : (value,value) closure }

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (operation_args, value) closure Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

(** Run-time environment. *)
and env = {
  dynamic : dynamic;
  lexical : lexical;
  state   : state  ;
}

(** A toplevel computation carries around the current
    environment. *)
type 'a toplevel = env -> 'a * env

(** Predeclared *)
let name_some = Name.make "Some"
let name_none = Name.make "None"
let name_unit = Name.make "tt"
let name_inl  = Name.make "Inl"
let name_inr  = Name.make "Inr"

let predefined_tags = [
  (name_some, 1);
  (name_none, 0);
  (name_unit, 0);
  (name_inl,  1);
  (name_inr,  1)
]

let name_equal        = Name.make "equal"
let name_as_prod      = Name.make "as_prod"
let name_as_eq        = Name.make "as_eq"
let name_as_signature = Name.make "as_signature"

let predefined_ops = [
  (name_equal       , 2) ;
  (name_as_prod     , 1) ;
  (name_as_eq       , 1) ;
  (name_as_signature, 1) ;
]

(** Make values *)
let mk_term j =
  let j = Jdg.strengthen j in
  Term j

let mk_handler h = Handler h
let mk_tag t lst = Tag (t, lst)
let mk_tuple lst = Tuple lst
let mk_string s = String s
let mk_ident x = Ident x

let mk_closure0 (f : 'a -> 'b result) {lexical;_} = Clos (fun v env -> f v {env with lexical})

let apply_closure (Clos f) v env = f v env

(** References *)
let mk_ref v env =
  let x,state = Store.fresh v env.state in
  Return (Ref x),state

let lookup_ref x env =
  let v = Store.lookup x env.state in
  Return v, env.state

let update_ref x v env =
  let state = Store.update x v env.state in
  Return (), state

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind (r:'a result) (f:'a -> 'b result) : 'b result = fun env ->
  match r env with
  | Return v, state -> f v {env with state}
  | Operation (op, vs, jt, d, k), state ->
     let env = {env with state} in
     let k = mk_closure0 (fun x -> bind (apply_closure k x) f) env in
     Operation (op, vs, jt, d, k), env.state

let (>>=) = bind

let top_bind m f env =
  let x, env = m env in
  f x env

let catch m env =
  try
    let x, env = m () env in
    Error.OK x, env
  with
    | Error.Error err ->
      Error.Err err, env

(** Returns *)
let top_return x env = x, env

let top_mk_closure f env = Closure (mk_closure0 f env), env
let top_return_closure f env = mk_closure0 f env, env

let return x env = Return x, env.state

let return_term e = return (mk_term e)

let return_closure f env = Return (Closure (mk_closure0 f env)), env.state

let return_handler handler_val handler_ops handler_finally env =
  let option_map g = function None -> None | Some x -> Some (g x) in
  let h = {
    handler_val = option_map (fun v -> mk_closure0 v env) handler_val ;
    handler_ops = Name.IdentMap.map (fun f -> mk_closure0 f env) handler_ops ;
    handler_finally = option_map (fun v -> mk_closure0 v env) handler_finally ;
  } in
  Return (Handler h), env.state

let rec top_fold f acc = function
  | [] -> top_return acc
  | x::rem -> top_bind (f acc x) (fun acc ->
    top_fold f acc rem)

let name_of v =
  match v with
    | Term _ -> "a term"
    | Closure _ -> "a function"
    | Handler _ -> "a handler"
    | Tag _ -> "a data tag"
    | List _ -> "a list"
    | Tuple _ -> "a tuple"
    | Ref _ -> "a reference"
    | String _ -> "a string"
    | Ident _ -> "an identifier"

(** Coerce values *)
let as_term ~loc = function
  | Term e -> e
  | (Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected a term but got %s" (name_of v)

let as_closure ~loc = function
  | Closure f -> f
  | (Term _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected a closure but got %s" (name_of v)

let as_handler ~loc = function
  | Handler h -> h
  | (Term _ | Closure _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected a handler but got %s" (name_of v)

let as_ref ~loc = function
  | Ref v -> v
  | (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected a ref but got %s" (name_of v)

let as_string ~loc = function
  | String v -> v
  | (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | Ident _) as v ->
    Error.runtime ~loc "expected a string but got %s" (name_of v)

let as_ident ~loc = function
  | Ident v -> v
  | (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _) as v ->
    Error.runtime ~loc "expected an identifier but got %s" (name_of v)

let as_option ~loc = function
  | Tag (t,[]) when (Name.eq_ident t name_none)  -> None
  | Tag (t,[x]) when (Name.eq_ident t name_some) -> Some x
  | (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected an option but got %s" (name_of v)

let as_sum ~loc = function
  | Tag (t,[x]) when (Name.eq_ident t name_inl) -> Tt.Inl x
  | Tag (t,[x]) when (Name.eq_ident t name_inr) -> Tt.Inr x
  | (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected a sum but got %s" (name_of v)

(** Wrappers for making tags *)
let as_list ~loc = function
  | List lst -> lst
  | (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected a list but got %s" (name_of v)

let from_option = function
  | None -> Tag (name_none, [])
  | Some v -> Tag (name_some, [v])

let from_list lst = List lst

let from_sum = function
  | Tt.Inl x -> Tag (name_inl, [x])
  | Tt.Inr x -> Tag (name_inr, [x])

let list_nil = List []

let list_cons v lst = List (v :: lst)

let return_unit = return (Tag (name_unit, []))

(** Operations *)

let operation op ?checking vs env =
  Operation (op, vs, checking, env.dynamic, mk_closure0 return env), env.state

let operation_equal v1 v2 =
  operation name_equal [v1;v2]

let operation_as_prod v =
  operation name_as_prod [v]

let operation_as_eq v =
  operation name_as_eq [v]

let operation_as_signature v =
  operation name_as_signature [v]


(** Interact with the environment *)

let top_bound_names env = List.map fst env.lexical.bound, env

let top_get_env env = env, env

let get_env env = Return env, env.state

let get_decl x env =
  let rec get = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq_ident x y then Some v else get lst
  in
  get env.dynamic.decls

let get_operation x env =
  match get_decl x env with
  | None -> None
  | Some (DeclOperation k) -> Some k
  | Some (DeclData _ | DeclConstant _ | DeclSignature _) -> None

let get_data x env =
  match get_decl x env with
  | None -> None
  | Some (DeclData k) -> Some k
  | Some (DeclOperation _ | DeclConstant _ | DeclSignature _) -> None

let get_constant x env =
  match get_decl x env with
  | None -> None
  | Some (DeclConstant c) -> Some c
  | Some (DeclData _ | DeclOperation _ | DeclSignature _) -> None

let get_signature x env =
  match get_decl x env with
  | None -> None
  | Some (DeclSignature s) -> Some s
  | Some (DeclData _ | DeclOperation _ | DeclConstant _) -> None

let lookup_constant ~loc x env =
  match get_constant x env with
    | Some t -> Return t, env.state
    | None -> Error.impossible ~loc "Unknown constant %t" (Name.print_ident x)

let lookup_signature ~loc x env =
  match get_signature x env with
   | Some def -> Return def, env.state
   | None -> Error.impossible ~loc "Unknown signature %t" (Name.print_ident x)

let find_signature ~loc ls env =
  let rec fold = function
    | [] -> Error.runtime ~loc "No signature has these exact fields."
    | (s, DeclSignature s_def) :: lst ->
       let rec cmp lst1 lst2 =
         match lst1, lst2 with
         | [], [] -> true
         | l1::lst1, (l2,_,_)::lst2 -> Name.eq_ident l1 l2 && cmp lst1 lst2
         | [],_::_ | _::_,[] -> false
       in
       if cmp ls s_def then s, s_def else fold lst
    | (_, (DeclConstant _ | DeclData _ | DeclOperation _)) :: lst -> fold lst
  in
  Return (fold env.dynamic.decls), env.state

let lookup_abstracting env = Return env.dynamic.abstracting, env.state

let get_bound ~loc k env =
  try
    snd (List.nth env.lexical.bound k)
  with
  | Failure _ -> Error.impossible ~loc "invalid de Bruijn index %d" k

let lookup_bound ~loc k env =
  Return (get_bound ~loc k env), env.state

let add_bound0 x v env = {env with lexical = { env.lexical with bound = (x,v)::env.lexical.bound } }

(** generate a fresh atom of type [t] and bind it to [x]
    NB: This is an effectful computation, as it increases a global counter. *)
let add_free ~loc x (Jdg.Ty (ctx, t)) m env =
  let y, ctx = Context.add_fresh ctx x t in
  let yt = mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc y) t) in
  let env = add_bound0 x yt env in
  m ctx y env

(** generate a fresh atom of type [t] and bind it to [x],
    and record that the atom will be abstracted.
    NB: This is an effectful computation, as it increases a global counter. *)
let add_abstracting ~loc ?(bind=true) x (Jdg.Ty (ctx, t)) m env =
  let y, ctx = Context.add_fresh ctx x t in
  let env =
    if not bind
    then
      env
    else
      let ya = Tt.mk_atom ~loc y in
      let jyt = Jdg.mk_term ctx ya t in
      let env = add_bound0 x (mk_term jyt) env in
      { env with
                dynamic = { env.dynamic with
                            abstracting = jyt :: env.dynamic.abstracting } }
  in
  m ctx y env

let is_known x env =
  if Name.eq_ident Name.anonymous x then false
  else
    let rec is_bound = function
      | [] -> false
      | (y,_) :: lst -> Name.eq_ident x y || is_bound lst
    in
    is_bound env.lexical.bound ||
    (match get_decl x env with
     | None -> false
     | Some _ -> true)

let add_operation0 ~loc x k env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else { env with dynamic = {env.dynamic with decls = (x, DeclOperation k) :: env.dynamic.decls }} 

let add_operation ~loc x k env = (),add_operation0 ~loc x k env

let add_data0 ~loc x k env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else { env with dynamic = {env.dynamic with decls = (x, DeclData k) :: env.dynamic.decls }}

let add_data ~loc x k env = (), add_data0 ~loc x k env

let add_constant ~loc x ytsu env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else (),{ env with dynamic = {env.dynamic with decls = (x, DeclConstant ytsu) :: env.dynamic.decls }}

let add_signature ~loc s s_def env =
  if is_known s env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident s)
  else (), {env with dynamic = {env.dynamic with decls = (s, DeclSignature s_def) :: env.dynamic.decls}}

let add_bound x v m env =
  let env = add_bound0 x v env in
  m env

let push_bound = add_bound0

let add_topbound ~loc x v env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else
    let env = add_bound0 x v env in
    (), env

let add_topbounds ~loc xvs env =
  let rec fold env = function
    | [] -> (), env
    | (x,v) :: xvs ->
       if is_known x env
       then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
       else
         let env = add_bound0 x v env in
         fold env xvs
  in
  fold env xvs

let add_handle op xsc env =
  (),{ env with lexical = { env.lexical with handle = (op, xsc) :: env.lexical.handle } }

(* This function for internal use *)
let lookup_handle op {lexical={handle=lst;_};_} =
  try
    Some (List.assoc op lst)
  with Not_found -> None

let set_continuation c m env =
  m { env with lexical = { env.lexical with continuation = Some c } }

let lookup_continuation ~loc ({lexical={continuation;_};_} as env) =
  match continuation with
    | Some cont -> Return cont, env.state
    | None -> Error.impossible ~loc "No continuation"

let push_file f env =
  (),{ env with lexical = { env.lexical with files = (Filename.basename f) :: env.lexical.files } }

let included f env =
  List.mem (Filename.basename f) env.lexical.files, env

(** Printers *)

(** Generate a printing environment from runtime environment *)
let get_penv env =
  { Tt.forbidden = List.map fst env.lexical.bound @ List.map fst env.dynamic.decls ;
    Tt.sigs = (fun s ->
               match get_signature s env with
                 | None -> Error.impossible ~loc:Location.unknown "get_penv: unknown signature %t" (Name.print_ident s)
                 | Some s_def -> List.map (fun (l,_,_) -> l) s_def)
  }

let lookup_penv env =
  Return (get_penv env), env.state

let rec print_value' ?max_level ~penv refs v ppf =
  match v with

  | Term e -> Jdg.print_term ~penv ?max_level e ppf

  | Closure f -> Format.fprintf ppf "<function>"

  | Handler h -> Format.fprintf ppf "<handler>"

  | Tag (t, lst) ->
     begin
       match lst with
       | [] -> Name.print_ident t ppf
       | (_::_) -> Print.print ?max_level ~at_level:1 ppf "%t@ %t"
                               (Name.print_ident t)
                               (Print.sequence (print_value' ~max_level:0 ~penv refs) "" lst)
     end

  | List lst -> Format.fprintf ppf "[%t]"
                  (Print.sequence (print_value' ~max_level:2 ~penv refs) "," lst)

  | Tuple lst -> Format.fprintf ppf "(%t)"
                  (Print.sequence (print_value' ~max_level:2 ~penv refs) "," lst)

  | Ref v -> Print.print ?max_level ~at_level:1 ppf "ref@ %t := %t"
                  (Store.print_key v)
                  (print_value' ~penv ~max_level:0 refs (Store.lookup v refs))

  | String s -> Format.fprintf ppf "\"%s\"" (String.escaped s)

  | Ident x -> Name.print_ident x ppf

let print_value'' env ?max_level v ppf =
  let penv = get_penv env in
  let refs = env.state in
  Format.fprintf ppf "@[<hov>%t@]"
                 (print_value' ?max_level ~penv refs v)

let top_print_value env = (print_value'' env), env

let print_value env =
  Return (print_value'' env), env.state

let print_term env =
  Return (fun ?max_level -> Tt.print_term ~penv:(get_penv env) ?max_level), env.state

let print_ty env =
  Return (fun ?max_level -> Tt.print_ty ~penv:(get_penv env) ?max_level), env.state

let print_env env =
  let print env ppf =
    let penv = get_penv env in
    List.iter
      (function
        | (x, DeclConstant t) ->
           Format.fprintf ppf "@[<hov 4>constant %t@;<1 -2>%t@]@\n"
                          (Name.print_ident x)
                          (Tt.print_ty ~penv t)
        | (x, DeclData k) ->
           Format.fprintf ppf "@[<hov 4>data %t %d@]@\n"
                          (Name.print_ident x)
                          k
        | (x, DeclOperation k) ->
           Format.fprintf ppf "@[<hov 4>operation %t %d@]@\n"
                          (Name.print_ident x)
                          k
        | (x, DeclSignature s) ->
           Format.fprintf ppf "@[<hov 4>signature %t %t@]@\n"
                       (Name.print_ident x)
                       (Tt.print_sig_def ~penv s)
      )
      (List.rev env.dynamic.decls) ;
  in
  print env, env

(* The empty environment *)
let empty = {
  lexical = {
    bound = [] ;
    handle = [] ;
    continuation = None ;
    files = [] ;
  } ;
  dynamic = {
    decls = [] ;
    abstracting = [] ;
  } ;
  state = Store.empty;
}

let initialised =
  let env = empty in
  (* Declare predefined data constructors *)
  let env = List.fold_left
              (fun env (x, k) -> add_data0 ~loc:Location.unknown x k env)
              env
              predefined_tags
  in
  (* Declare predefined operations *)
  let env = List.fold_left
              (fun env (x, k) -> add_operation0 ~loc:Location.unknown x k env)
              env
              predefined_ops
  in
  env

let run m = fst (m initialised)

type 'a progress = 'a * env

let initial m = m initialised
let progress (x, env) f = f x env
let finish (x,_) = x

(** Handling *)
let rec handle_result {handler_val; handler_ops; handler_finally} (r : value result) : value result =
  begin fun env -> match r env with
  | Return v , state ->
     let env = {env with state} in
     begin match handler_val with
     | Some f -> apply_closure f v env
     | None -> Return v, env.state
     end
  | Operation (op, vs, jt, dynamic, cont), state ->
     let env = {env with dynamic; state} in
     let h = {handler_val; handler_ops; handler_finally=None} in
     let cont = mk_closure0 (fun v env -> handle_result h (apply_closure cont v) env) env in
     begin
       try
         let f = Name.IdentMap.find op handler_ops in
         apply_closure f {args=vs;checking=jt; cont} env
       with
         Not_found ->
           Operation (op, vs, jt, dynamic, cont), env.state
     end
  end >>= fun v ->
  match handler_finally with
    | Some f -> apply_closure f v
    | None -> return v

let top_handle ~loc r env0 =
  let rec handle r env =
    match r with
    | Return v, state -> v, state
    | Operation (op, vs, checking, dynamic, k), state ->
       let env = {env with dynamic;state} in
       begin match lookup_handle op env with
        | None -> Error.runtime ~loc "unhandled operation %t" (Name.print_op op)
        | Some f ->
          let r = apply_closure f (vs,checking) >>=
            apply_closure k
          in
          handle (r env) env
       end
  in
  let v, state = handle (r env0) env0 in
  v, {env0 with state}

(** Equality *)
let rec equal_value v1 v2 =
  match v1, v2 with
    | Term (Jdg.Term (_,te1,_)), Term (Jdg.Term (_,te2,_)) ->
      Tt.alpha_equal te1 te2

    | Tag (t1,vs1), Tag (t2,vs2) ->
      Name.eq_ident t1 t2 &&
      let rec fold vs1 vs2 =
        match vs1, vs2 with
          | [], [] -> true
          | v1::vs1, v2::vs2 ->
            equal_value v1 v2 &&
            fold vs1 vs2
          | _::_, [] | [], _::_ -> false
        in
      fold vs1 vs2

    | List lst1, List lst2 ->
       let rec fold = function
         | [], [] -> true
         | v1 :: lst1, v2 :: lst2 -> equal_value v1 v2 && fold (lst1, lst2)
         | [], _::_ | _::_, [] -> false
       in
       fold (lst1, lst2)

    | Tuple lst1, Tuple lst2 ->
       let rec fold = function
         | [], [] -> true
         | v1 :: lst1, v2 :: lst2 -> equal_value v1 v2 && fold (lst1, lst2)
         | [], _::_ | _::_, [] -> false
       in
       fold (lst1, lst2)

    | Ref v1, Ref v2 ->
       (* XXX should we compare references by value instead? *)
       Store.key_eq v1 v2

    | String s1, String s2 ->
      s1 = s2

    | Ident x1, Ident x2 ->
      Name.eq_ident x1 x2

    | Closure _, Closure _
    | Handler _, Handler _ ->
       (* XXX should we use physical comparison == instead? *)
       false

    (* At some level the following is a bit ridiculous *)
    | Term _, (Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _)
    | Closure _, (Term _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _)
    | Handler _, (Term _ | Closure _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _)
    | Tag _, (Term _ | Closure _ | Handler _ | List _ | Tuple _ | Ref _ | String _ | Ident _)
    | List _, (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | String _ | Ident _)
    | Tuple _, (Term _ | Closure _ | Handler _ | Tag _ | List _ | Ref _ | String _ | Ident _)
    | String _, (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | Ident _)
    | Ident _, (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _)
    | Ref _, (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | String _ | Ident _) ->
      false

