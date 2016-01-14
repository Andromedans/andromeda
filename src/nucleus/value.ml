(** Runtime values and results *)

(* Information about a toplevel declaration *)
type decl =
  | Constant of Tt.constsig
  | Data of int
  | Operation of int

type dynamic = {
  decls : (Name.ident * decl) list ;
  (* Toplevel declaration *)

  abstracting : Judgement.term list;
  (* The list of judgments about atoms which are going to be abstracted. We
     should avoid creating atoms which depends on these, as this will prevent
     abstraction from working. The list is in the reverse order from
     abstraction, i.e., the inner-most abstracted variable appears first in the
     list. *)
}

(* for now the state is unit *)
type state = unit

type lexical = {
  bound : (Name.ident * value) list;
  continuation : (value,value) closure option;
  handle : (Name.ident * (value list,value) closure) list;
  files : string list;
}

and value =
  | Term of Judgement.term
  | Ty of Judgement.ty
  | Closure of (value,value) closure
  | Handler of handler
  | Tag of Name.ident * value list
  | List of value list
  | Ref of value ref

(* It's important not to confuse the closure and the underlying ocaml function *)
and ('a,'b) closure = Clos of ('a -> 'b result)

and 'a performance =
  | Return of 'a
  | Perform of Name.ident * value list * dynamic * (value,'a) closure

and 'a result = env -> 'a performance * state

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (value list * (value,value) closure, value) closure Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

(** Run-time environment. *)
and env = {
  dynamic : dynamic;
  lexical : lexical;
  state   : state  ;
}

type 'a toplevel = env -> 'a*env

(** Predeclared *)
let name_some = Name.make "Some"
let name_none = Name.make "None"
let name_pair = Name.make "pair"
let name_unit = Name.make "tt"

let predefined_tags = [
  (name_some, 1);
  (name_none, 0);
  (name_pair, 2);
  (name_unit, 0);
]

let name_equal        = Name.make "equal"
let name_abstract     = Name.make "abstract"
let name_as_prod      = Name.make "as_prod"
let name_as_eq        = Name.make "as_eq"
let name_as_signature = Name.make "as_signature"

let predefined_ops = [
  (name_equal       , 2) ;
  (name_abstract    , 2) ;
  (name_as_prod     , 1) ;
  (name_as_eq       , 1) ;
  (name_as_signature, 1) ;
]

(** Make values *)
let mk_term j = Term j
let mk_ty j = Ty j
let mk_handler h = Handler h
let mk_tag t lst = Tag (t, lst)
let mk_ref v = Ref (ref v)

let mk_closure0 (f : 'a -> 'b result) {lexical;_} = Clos (fun v env -> f v {env with lexical})
let mk_closure' f env = mk_closure0 f env, env

let apply_closure (Clos f) v env = f v env

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind (r:'a result) (f:'a -> 'b result) : 'b result = fun env ->
  match r env with
  | Return v, state -> f v {env with state}
  | Perform (op, vs, d, k), state -> 
     let env = {env with state} in
     let k = mk_closure0 (fun x -> bind (apply_closure k x) f) env in
     Perform (op, vs, d, k), env.state

let (>>=) = bind

let top_bind m f env =
  let x,env = m env in
  f x env

(** Returns *)
let top_return x env = x,env

let return x env = Return x, env.state

let return_term e = return (Term e)

let return_ty t = return (Ty t)

let return_closure f env = Return (Closure (mk_closure0 f env)), env.state

let return_handler handler_val handler_ops handler_finally env =
  let option_map g = function None -> None | Some x -> Some (g x) in
  let h = {
    handler_val = option_map (fun v -> mk_closure0 v env) handler_val ;
    handler_ops = Name.IdentMap.map (fun f -> mk_closure0 f env) handler_ops ;
    handler_finally = option_map (fun v -> mk_closure0 v env) handler_finally ;
  } in
  Return (Handler h), env.state

(** Printers *)
let print_closure xs _ ppf =
  Print.print ~at_level:0 ppf "<function>"

let print_handler xs h ppf =
  Print.print ~at_level:0 ppf "<handler>" (* XXX improve in your spare time *)

let rec print_tag ?max_level xs t lst ppf =
  match lst with
  | [] -> Print.print ?max_level ~at_level:0 ppf "%t" (Name.print_ident t)
  | (_::_) -> Print.print ?max_level ~at_level:1 ppf "%t %t"
                          (Name.print_ident t)
                          (Print.sequence (print_value ~max_level:0 xs) "" lst)

and print_value ?max_level xs v ppf =
  match v with
  | Term e -> Judgement.print_term ?max_level xs e ppf
  | Ty t -> Judgement.print_ty ?max_level xs t ppf
  | Closure f -> print_closure xs f ppf
  | Handler h -> print_handler xs h ppf
  | Tag (t, lst) -> print_tag ?max_level xs t lst ppf
  | List lst -> Print.print ~at_level:0 ppf "[%t]"
                            (Print.sequence (print_value ~max_level:2 xs) "," lst)
  | Ref v -> Print.print ?max_level ~at_level:1 ppf "ref@ %t" (print_value ~max_level:0 xs (!v))

let name_of v =
  match v with
    | Term _ -> "a term"
    | Ty _ -> "a type"
    | Closure _ -> "a function"
    | Handler _ -> "a handler"
    | Tag _ -> "a data tag"
    | List _ -> "a list"
    | Ref _ -> "a reference"

(** Prefill the [xs] argument of print_* *)
let used_names env =
  List.map fst env.lexical.bound @ List.map fst env.dynamic.decls

let top_print_value env =
  (fun ?max_level -> print_value ?max_level (used_names env)),env

let print_value env =
  Return (fun ?max_level -> print_value ?max_level (used_names env)), env.state

let print_term env =
  Return (fun ?max_level -> Tt.print_term ?max_level (used_names env)), env.state

let print_ty env =
  Return (fun ?max_level -> Tt.print_ty ?max_level (used_names env)), env.state

(** Coerce values *)
let as_term ~loc = function
  | Term e -> e
  | (Ty _ | Closure _ | Handler _ | Tag _ | List _ | Ref _) as v ->
    Error.runtime ~loc "expected a term but got %s" (name_of v)

let as_ty ~loc = function
  | Ty t -> t
  | (Term _ | Closure _ | Handler _ | Tag _ | List _ | Ref _) as v ->
    Error.runtime ~loc "expected a term but got %s" (name_of v)

let as_closure ~loc = function
  | Closure f -> f
  | (Ty _ | Term _ | Handler _ | Tag _ | List _ | Ref _) as v ->
    Error.runtime ~loc "expected a term but got %s" (name_of v)

let as_handler ~loc = function
  | Handler h -> h
  | (Ty _ | Term _ | Closure _ | Tag _ | List _ | Ref _) as v ->
    Error.runtime ~loc "expected a term but got %s" (name_of v)

let as_ref ~loc = function
  | Ref v -> v
  | (Ty _ | Term _ | Closure _ | Handler _ | Tag _ | List _) as v ->
    Error.runtime ~loc "expected a term but got %s" (name_of v)

let as_option ~loc = function
  | Tag (t,[]) when (Name.eq_ident t name_none)  -> None
  | Tag (t,[x]) when (Name.eq_ident t name_some) -> Some x
  | (Ty _ | Term _ | Closure _ | Handler _ | Tag _ | List _ | Ref _) as v ->
    Error.runtime ~loc "expected a term but got %s" (name_of v)

(** Wrappers for making tags *)
let as_list ~loc = function
  | List lst -> lst
  | (Ty _ | Term _ | Closure _ | Handler _ | Tag _ | Ref _) as v ->
    Error.runtime ~loc "expected a list but got %s" (name_of v)

let from_option = function
  | None -> Tag (name_none, [])
  | Some v -> Tag (name_some, [v])

let from_pair (v1, v2) = Tag (name_pair, [v1; v2])

let from_list lst = List lst

let list_nil = List []

let list_cons v lst = List (v :: lst)

let return_unit = return (Tag (name_unit, []))

(** Operations *)
let perform op vs env =
  Perform (op, vs, env.dynamic, mk_closure0 return env), env.state

let perform_equal v1 v2 =
  perform name_equal [v1;v2]

let perform_abstract v1 v2 =
  perform name_abstract [v1;v2]

let perform_as_prod v =
  perform name_as_prod [v]

let perform_as_eq v =
  perform name_as_eq [v]

let perform_as_signature v =
  perform name_as_signature [v]


(** Interact with the environment *)

let top_bound_names env = List.map fst env.lexical.bound, env

let top_get_env env = env,env

let get_env env = Return env, env.state

let lookup_decl x env =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq_ident x y then Some v else lookup lst
  in
  lookup env.dynamic.decls

let lookup_operation x env =
  match lookup_decl x env with
  | None -> None
  | Some (Operation k) -> Some k
  | Some (Data _ | Constant _) -> None

let lookup_data x env =
  match lookup_decl x env with
  | None -> None
  | Some (Data k) -> Some k
  | Some (Operation _ | Constant _) -> None

let get_constant x env =
  match lookup_decl x env with
  | None -> None
  | Some (Constant c) -> Some c
  | Some (Data _ | Operation _) -> None

let lookup_constant x env = Return (get_constant x env), env.state

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
    NB: This is an effectful computation. TODO what? *)
let add_free ~loc x (ctx, t) m env =
  let y, ctx = Context.add_fresh ctx x t in
  let yt = Term (ctx, Tt.mk_atom ~loc y, t) in
  let env = add_bound0 x yt env in
  m ctx y env

(** generate a fresh atom of type [t] and bind it to [x],
    and record that the atom will be abstracted.
    NB: This is an effectful computation. *)
let add_abstracting ~loc x (ctx, t) m env =
  let y, ctx = Context.add_fresh ctx x t in
  let ya = Tt.mk_atom ~loc y in
  let jyt = Judgement.mk_term ctx ya t in
  let env = add_bound0 x (Term jyt) env in
  let env = { env with
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
    (match lookup_decl x env with
     | None -> false
     | Some _ -> true)

let add_operation0 ~loc x k env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else { env with dynamic = {env.dynamic with decls = (x, Operation k) :: env.dynamic.decls }} 

let add_operation ~loc x k env = (),add_operation0 ~loc x k env

let add_data0 ~loc x k env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else { env with dynamic = {env.dynamic with decls = (x, Data k) :: env.dynamic.decls }}

let add_data ~loc x k env = (), add_data0 ~loc x k env

let add_constant ~loc x ytsu env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else (),{ env with dynamic = {env.dynamic with decls = (x, Constant ytsu) :: env.dynamic.decls }}

let add_bound x v m env =
  let env = add_bound0 x v env in
  m env

let push_bound = add_bound0

let add_topbound ~loc x v env =
  if is_known x env
  then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
  else
    let env = add_bound0 x v env in
    (),env


let add_handle op xsc env =
  (),{ env with lexical = { env.lexical with handle = (op, xsc) :: env.lexical.handle } }

(* This function for internal use *)
let lookup_handle op {lexical={handle=lst;_};_} =
  try
    Some (List.assoc op lst)
  with Not_found -> None

let set_continuation c m env =
  m { env with lexical = { env.lexical with continuation = Some c } }

let lookup_continuation ({lexical={continuation;_};_} as env) =
  Return continuation, env.state

let push_file f env =
  (),{ env with lexical = { env.lexical with files = (Filename.basename f) :: env.lexical.files } }

let included f env =
  List.mem (Filename.basename f) env.lexical.files, env

let print env ppf =
  let forbidden_names = used_names env in
  Print.print ppf "---ENVIRONMENT---@." ;
  List.iter
    (function
      | (x, Constant t) ->
         Print.print ppf "@[<hov 4>constant %t@;<1 -2>%t@]@\n" (Name.print_ident x)
                     (Tt.print_constsig forbidden_names t)
      | (x, Data k) ->
         Print.print ppf "@[<hov 4>data %t %d@]@\n" (Name.print_ident x) k
      | (x, Operation k) ->
         Print.print ppf "@[<hov 4>operation %t %d@]@\n" (Name.print_ident x) k
    )
    (List.rev env.dynamic.decls) ;
  Print.print ppf "-----END-----@."

let print_env env = print env,env

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
  state = ();
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
let progress (x,env) f = f x env
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
  | Perform (op, vs, dynamic, cont), state ->
     let env = {env with dynamic; state} in
     let h = {handler_val; handler_ops; handler_finally=None} in
     let cont = mk_closure0 (fun v env -> handle_result h (apply_closure cont v) env) env in
     begin
       try
         let f = Name.IdentMap.find op handler_ops in
         apply_closure f (vs, cont) env
       with
         Not_found ->
           Perform (op, vs, dynamic, cont), env.state
     end
  end >>= fun v ->
  match handler_finally with
    | Some f -> apply_closure f v
    | None -> return v

let rec top_handle ~loc r env =
  match r env with
    | Return v, state -> v,{env with state}
    | Perform (op, vs, dynamic, k), state ->
       let env = {env with dynamic;state} in
       begin match lookup_handle op env with
        | None -> Error.runtime ~loc "unhandled operation %t" (Name.print_op op)
        | Some f ->
          let r = apply_closure f vs >>=
            apply_closure k
          in
          top_handle ~loc r env
       end

(** Equality *)
let rec equal_value v1 v2 =
  match v1, v2 with
    | Term (_,te1,_), Term (_,te2,_) ->
      Tt.alpha_equal te1 te2

    | Ty (_,t1), Ty (_,t2) ->
      Tt.alpha_equal_ty t1 t2

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

    | Ref v1, Ref v2 ->
       (* XXX should we compare references by value instead? *)
       v1 == v2

    | Closure _, Closure _
    | Handler _, Handler _ ->
       (* XXX should we use physical comparison == instead? *)
       false

    | Term _, (Ty _ | Closure _ | Handler _ | Tag _ | List _ | Ref _)
    | Ty _, (Term _ | Closure _ | Handler _ | Tag _ | List _ | Ref _)
    | Closure _, (Term _ | Ty _ | Handler _ | Tag _ | List _ | Ref _)
    | Handler _, (Term _ | Ty _ | Closure _ | Tag _ | List _ | Ref _)
    | Tag _, (Term _ | Ty _ | Closure _ | Handler _ | List _ | Ref _)
    | List _, (Term _ | Ty _ | Closure _ | Handler _ | Tag _ | Ref _)
    | Ref _, (Term _ | Ty _ | Closure _ | Handler _ | Tag _ | List _) ->
      false

