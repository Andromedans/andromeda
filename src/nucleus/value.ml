(** Runtime values and computations *)

type ref = Store.key

type dyn = Store.key

type bound_info =
  | BoundVal
  | BoundConst of Name.constant
  | BoundData of Name.data * int
  | BoundOp of Name.operation * int
  | BoundSig of Name.signature
  | BoundDyn of dyn

(** This module defines 2 monads:
    - the computation monad [comp], providing operations and an environment of which part is dynamically scoped.
      Primitives are like [add_bound].
    - the toplevel monad [toplevel], a standard state monad with restricted accessors.
      Primitives are like [top_add_bound].
      Some modifications of the environment may only be done at the top level, for instance declaring constants.
    For internal use, functions which work on the environment may be defined, eg [add_bound0].

    Finally in a small number of restricted circumstances the environment is accessed outside the monads.
*)

(** Run-time environment. *)
type env = {
  dynamic : dynamic;
  lexical : lexical;
  state   : state  ;
}

and dynamic = {
  (* Toplevel declarations *)
  constants : (Name.constant * Tt.ty) list;
  datas : (Name.data * int) list;
  operations : (Name.operation * int) list;
  signatures : (Name.signature * Tt.sig_def) list;

  (* The list of judgments about atoms which are going to be abstracted. We
     should avoid creating atoms which depends on these, as this will prevent
     abstraction from working. The list is in the reverse order from
     abstraction, i.e., the inner-most abstracted variable appears first in the
     list. *)
  abstracting : value list;

  (* Current values of dynamic variables *)
  vars : value Store.t
}

and lexical = {
  context : (Name.ident * bound_info) list;
  bound : value list;

  continuation : (value,value) closure option;

  (* The following are only modified at the top level *)
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
  | Ref of ref
  | String of string
  | Ident of Name.ident

(* It's important not to confuse the closure and the underlying ocaml function *)
and ('a, 'b) closure = Clos of ('a -> 'b comp)

and 'a result =
  | Return of 'a
  | Operation of Name.ident * value list * Jdg.ty option * dynamic * (value,'a) closure

and 'a comp = env -> 'a result * state

and operation_args = { args : value list; checking : Jdg.ty option; cont : (value,value) closure }

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (operation_args, value) closure Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

(** A toplevel computation carries around the current
    environment. *)
type 'a toplevel = env -> 'a * env

(** Predeclared *)
let name_some          = Name.make "Some"
let name_none          = Name.make "None"
let name_unconstrained = Name.make "Unconstrained"
let name_constrained   = Name.make "Constrained"

let predefined_tags = [
  (name_some,          1);
  (name_none,          0);
  (name_unconstrained, 1);
  (name_constrained,   1);
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

let mk_list lst = List lst
let list_nil = List []
let list_cons v lst = List (v :: lst)

let mk_closure0 f {lexical;_} = Clos (fun v env -> f v {env with lexical})
let mk_closure_ref g r = Clos (fun v env -> g v {env with lexical = (!r).lexical})

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
let rec bind (r:'a comp) (f:'a -> 'b comp) : 'b comp = fun env ->
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

let return_unit = return (Tuple [])

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

let as_list ~loc = function
  | List lst -> lst
  | (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected a list but got %s" (name_of v)

(** Wrappers for making tags *)
let from_option = function
  | None -> Tag (name_none, [])
  | Some v -> Tag (name_some, [v])

let as_option ~loc = function
  | Tag (t,[]) when (Name.eq_ident t name_none)  -> None
  | Tag (t,[x]) when (Name.eq_ident t name_some) -> Some x
  | (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected an option but got %s" (name_of v)

let from_constrain = function
  | Tt.Unconstrained x -> Tag (name_unconstrained, [x])
  | Tt.Constrained x -> Tag (name_constrained, [x])

let as_constrain ~loc = function
  | Tag (t,[x]) when (Name.eq_ident t name_unconstrained) -> Tt.Unconstrained x
  | Tag (t,[x]) when (Name.eq_ident t name_constrained) -> Tt.Constrained x
  | (Term _ | Closure _ | Handler _ | Tag _ | List _ | Tuple _ | Ref _ | String _ | Ident _) as v ->
    Error.runtime ~loc "expected a constrain but got %s" (name_of v)

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

let top_bound_info env = env.lexical.context, env

let get_env env = Return env, env.state

let get_constant x env =
  Name.assoc_ident x env.dynamic.constants

let get_signature x env =
  Name.assoc_ident x env.dynamic.signatures

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
    | (s, s_def) :: lst ->
       let rec cmp lst1 lst2 =
         match lst1, lst2 with
         | [], [] -> true
         | l1::lst1, (l2,_,_)::lst2 -> Name.eq_ident l1 l2 && cmp lst1 lst2
         | [],_::_ | _::_,[] -> false
       in
       if cmp ls s_def then s, s_def else fold lst
  in
  Return (fold env.dynamic.signatures), env.state

let lookup_abstracting env = Return env.dynamic.abstracting, env.state

let get_bound ~loc k env =
  try
    List.nth env.lexical.bound k
  with
  (* TODO is there a point in having this? *)
  | Failure _ -> Error.impossible ~loc "invalid de Bruijn index %d" k

let get_dynamic_value x env = Store.lookup x env.dynamic.vars

let lookup_bound ~loc k env =
  Return (get_bound ~loc k env), env.state

let lookup_dynamic_value x env =
  Return (get_dynamic_value x env), env.state

let add_bound0 x v env = {env with lexical = { env.lexical with
                                               context = (x, BoundVal) :: env.lexical.context;
                                               bound = v :: env.lexical.bound } }

let add_free ~loc x (Jdg.Ty (ctx, t)) m env =
  let y, ctx = Context.add_fresh ctx x t in
  let yt = mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc y) t) in
  let env = add_bound0 x yt env in
  m ctx y env

let add_abstracting ~loc ?(bind=true) x (Jdg.Ty (ctx, t)) m env =
  let y, ctx = Context.add_fresh ctx x t in
  let env =
    if not bind
    then
      env
    else
      let yt = mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc y) t) in
      let env = add_bound0 x yt env in
      { env with
                dynamic = { env.dynamic with
                            abstracting = yt :: env.dynamic.abstracting } }
  in
  m ctx y env

let is_known x env =
  if Name.eq_ident Name.anonymous x then false
  else
    match Name.assoc_ident x env.lexical.context with
      | Some _ -> true
      | None -> false

let add_operation0 ~loc x k env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else
  { env with dynamic = {env.dynamic with operations = (x, k) :: env.dynamic.operations };
             lexical = {env.lexical with context = (x, BoundOp (x, k)) :: env.lexical.context } }

let add_operation ~loc x k env = (),add_operation0 ~loc x k env

let add_data0 ~loc x k env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else
  { env with dynamic = {env.dynamic with datas = (x, k) :: env.dynamic.datas };
             lexical = {env.lexical with context = (x, BoundData (x, k)) :: env.lexical.context } }

let add_data ~loc x k env = (), add_data0 ~loc x k env

let add_constant0 ~loc x t env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else
  { env with dynamic = {env.dynamic with constants = (x, t) :: env.dynamic.constants };
             lexical = {env.lexical with context = (x, BoundConst x) :: env.lexical.context } }

let add_constant ~loc x t env = (), add_constant0 ~loc x t env

let add_signature0 ~loc s s_def env =
  if is_known s env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident s)
  else
  { env with dynamic = {env.dynamic with signatures = (s, s_def) :: env.dynamic.signatures };
             lexical = {env.lexical with context = (s, BoundSig s) :: env.lexical.context } }

let add_signature ~loc s s_def env = (), add_signature0 ~loc s s_def env

let add_bound x v m env =
  let env = add_bound0 x v env in
  m env

let add_bound_rec0 lst env =
  let r = ref env in
  let env =
    List.fold_left
      (fun env (f, g) ->
        let v = Closure (mk_closure_ref g r) in
        add_bound0 f v env)
      env lst
  in
  r := env ;
  env

let add_bound_rec lst m env =
  let env = add_bound_rec0 lst env in
  m env

let push_bound = add_bound0

let add_topbound ~loc x v env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else
    let env = add_bound0 x v env in
    (), env

let now0 x v env =
  {env with dynamic = {env.dynamic with vars = Store.update x v env.dynamic.vars }}

let now x v m env =
  let env = now0 x v env in
  m env

let top_now x v env =
  let env = now0 x v env in
  (), env

let add_dynamic0 ~loc x v env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else
    let y,vars = Store.fresh v env.dynamic.vars in
    { env with dynamic = {env.dynamic with vars };
               lexical = {env.lexical with context = (x, BoundDyn y) :: env.lexical.context } }

let add_dynamic ~loc x v env = (), add_dynamic0 ~loc x v env

let add_handle0 op xsc env =
  { env with lexical = { env.lexical with handle = (op, xsc) :: env.lexical.handle } }

let add_handle op xsc env = (), add_handle0 op xsc env


let add_topbound_rec ~loc lst env =
  let rec find_known = function
    | (f,_)::_ when (is_known f env) -> Some f
    | _::rem -> find_known rem
    | [] -> None
  in
  match find_known lst with
    | Some f -> Error.runtime ~loc "%t is already declared" (Name.print_ident f)
    | None ->
      let env = add_bound_rec0 lst env in
      (), env

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
  { Tt.forbidden = List.map fst env.lexical.context ;
    Tt.sigs = (fun s ->
               match get_signature s env with
                 | None -> Error.impossible ~loc:Location.unknown "get_penv: unknown signature %t" (Name.print_ident s)
                 | Some s_def -> List.map (fun (l,_,_) -> l) s_def)
  }

let lookup_penv env =
  Return (get_penv env), env.state

let rec print_value_aux ?max_level ~penv refs v ppf =
  match v with

  | Term e -> Jdg.print_term ~penv ?max_level e ppf

  | Closure f -> Format.fprintf ppf "<function>"

  | Handler h -> Format.fprintf ppf "<handler>"

  | Tag (t, lst) ->
     print_tag ?max_level ~penv refs t lst ppf

  | List lst -> Format.fprintf ppf "[%t]"
                  (Print.sequence (print_value_aux ~penv refs) "," lst)

  | Tuple lst -> Format.fprintf ppf "(%t)"
                  (Print.sequence (print_value_aux ~penv refs) "," lst)

  | Ref v -> Print.print ?max_level ~at_level:Level.highest ppf "ref@ %t := %t"
                  (Store.print_key v)
                  (print_value_aux ~penv ~max_level:Level.no_parens refs (Store.lookup v refs))

  | String s -> Format.fprintf ppf "\"%s\"" (String.escaped s)

  | Ident x -> Name.print_ident x ppf

and print_tag ?max_level ~penv refs t lst ppf =
  match t, lst with

  | Name.Ident (_, Name.Prefix), [v] ->
     (* prefix tag applied to one argument *)
     Print.print ppf ?max_level ~at_level:Level.prefix "%t@ %t"
                 (Name.print_ident ~parentheses:false t)
                 (print_value_aux ~max_level:Level.prefix_arg ~penv refs v)

  | Name.Ident (_, Name.Infix fixity), [v1; v2] ->
     (* infix tag applied to two arguments *)
     let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
     Print.print ppf ?max_level ~at_level:lvl_op "%t@ %t@ %t"
                 (print_value_aux ~max_level:lvl_left ~penv refs v1)
                 (Name.print_ident ~parentheses:false t)
                 (print_value_aux ~max_level:lvl_right ~penv refs v2)

  | _ ->
     (* print as application *)
     begin
       match lst with
       | [] -> Name.print_ident t ppf
       | (_::_) -> Print.print ?max_level ~at_level:Level.app ppf "%t@ %t"
                               (Name.print_ident t)
                               (Print.sequence (print_value_aux ~max_level:Level.app_right ~penv refs) "" lst)
     end

let print_value0 env ?max_level v ppf =
  let penv = get_penv env in
  let refs = env.state in
  Format.fprintf ppf "@[<hov>%t@]"
                 (print_value_aux ?max_level ~penv refs v)

let top_print_value env = (print_value0 env), env

and print_operation env op vs ppf =
  let penv = get_penv env
  and refs = env.state in
  match op, vs with

  | Name.Ident (_, Name.Prefix), [v] ->
     (* prefix op applied to one argument *)
     Print.print ppf ~at_level:Level.prefix "%t@ %t"
                 (Name.print_ident ~parentheses:false op)
                 (print_value_aux ~max_level:Level.prefix_arg ~penv refs v)

  | Name.Ident (_, Name.Infix fixity), [v1; v2] ->
     (* infix op applied to two arguments *)
     let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
     Print.print ppf ~at_level:lvl_op "%t@ %t@ %t"
                 (print_value_aux ~max_level:lvl_left ~penv refs v1)
                 (Name.print_ident ~parentheses:false op)
                 (print_value_aux ~max_level:lvl_right ~penv refs v2)

  | _ ->
     (* print as application *)
     begin
       match vs with
       | [] -> Name.print_ident op ppf
       | (_::_) -> Print.print ~at_level:Level.app ppf "%t@ %t"
                               (Name.print_ident op)
                               (Print.sequence (print_value_aux ~max_level:Level.app_right ~penv refs) "" vs)
     end

let print_value env =
  Return (print_value0 env), env.state

let print_term env =
  Return (fun ?max_level -> Tt.print_term ~penv:(get_penv env) ?max_level), env.state

let print_ty env =
  Return (fun ?max_level -> Tt.print_ty ~penv:(get_penv env) ?max_level), env.state

let print_env env =
  let print env ppf =
    let penv = get_penv env in
    List.iter (fun (x,t) ->
           Format.fprintf ppf "@[<hov 4>constant %t@;<1 -2>%t@]@\n"
                          (Name.print_ident x)
                          (Tt.print_ty ~penv t))
      env.dynamic.constants ;
    List.iter (fun (x,k) ->
           Format.fprintf ppf "@[<hov 4>data %t %d@]@\n"
                          (Name.print_ident x)
                          k)
      env.dynamic.datas ;
    List.iter (fun (x,k) ->
           Format.fprintf ppf "@[<hov 4>operation %t %d@]@\n"
                          (Name.print_ident x)
                          k)
      env.dynamic.operations ;
    List.iter (fun (x,s) ->
           Format.fprintf ppf "@[<hov 4>signature %t %t@]@\n"
                       (Name.print_ident x)
                       (Tt.print_sig_def ~penv s))
      env.dynamic.signatures ;
  in
  print env, env

(* The empty environment *)
let empty = {
  lexical = {
    context = [] ;
    bound = [] ;
    handle = [] ;
    continuation = None ;
    files = [] ;
  } ;
  dynamic = {
    constants = [] ;
    datas = [] ;
    operations = [] ;
    signatures = [] ;
    abstracting = [] ;
    vars = Store.empty ;
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
let rec handle_comp {handler_val; handler_ops; handler_finally} (r : value comp) : value comp =
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
     let cont = mk_closure0 (fun v env -> handle_comp h (apply_closure cont v) env) env in
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
        | None -> Error.runtime ~loc "unhandled operation %t" (print_operation env op vs)
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

