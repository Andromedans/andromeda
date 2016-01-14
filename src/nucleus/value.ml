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

type value =
  | Term of Judgement.term
  | Ty of Judgement.ty
  | Closure of (value,value) closure
  | Handler of handler
  | Tag of Name.ident * value list

and ('a,'b) closure = dynamic -> 'a -> 'b result

and 'a performance =
  | Return of 'a
  | Perform of Name.ident * value list * dynamic * (value,'a) closure

and 'a result = env -> 'a performance

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (value list * (value,value) closure, value) closure Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

(** Run-time environment. *)
and env = {
  bound : (Name.ident * value) list;
  continuation : (value,value) closure option;
  handle : (Name.ident * (value list,value) closure) list;
  files : string list;
  dynamic : dynamic;
}

type 'a toplevel = env -> 'a*env

(** Predeclared *)
let name_some = Name.make "Some"
let name_none = Name.make "None"
let name_pair = Name.make "pair"
let name_cons = Name.make "cons"
let name_nil = Name.make "nil"
let name_unit = Name.make "tt"

let predefined_tags = [
  (name_some, 1);
  (name_none, 0);
  (name_pair, 2);
  (name_cons, 2);
  (name_nil, 0);
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

let mk_closure0 f env = (fun dynamic v env -> f v {env with dynamic})
let mk_closure' f env = mk_closure0 f env, env

let apply_closure f v env = f env.dynamic v env

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind r f env =
  match r env with
  | Return v -> f v env
  | Perform (op, vs, d, k) -> 
     let k d x = bind (k d x) f in
     Perform (op, vs, d, k)

let (>>=) = bind

let top_bind m f env =
  let x,env = m env in
  f x env

(** Returns *)
let top_return x env = x,env

let return x _ = Return x

let return_term e = return (Term e)

let return_ty t = return (Ty t)

let return_closure f env = Return (Closure (mk_closure0 f env))

let return_handler handler_val handler_ops handler_finally env =
  let option_map g = function None -> None | Some x -> Some (g x) in
  let h = {
    handler_val = option_map (fun v -> mk_closure0 v env) handler_val ;
    handler_ops = Name.IdentMap.map (fun f -> mk_closure0 f env) handler_ops ;
    handler_finally = option_map (fun v -> mk_closure0 v env) handler_finally ;
  } in
  Return (Handler h)

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

let print_value_key v ppf =
  match v with
    | Term _ -> Print.print ~at_level:0 ppf "<term>"
    | Ty _ -> Print.print ~at_level:0 ppf "<type>"
    | Closure _ -> Print.print ~at_level:0 ppf "<function>"
    | Handler _ -> Print.print ~at_level:0 ppf "<handler>"
    | Tag _ -> Print.print ~at_level:0 ppf "<tag>"

(** Prefill the [xs] argument of print_* *)
let used_names env =
  List.map fst env.bound @ List.map fst env.dynamic.decls

let top_print_value env =
  (fun ?max_level -> print_value ?max_level (used_names env)),env

let print_value env =
  Return (fun ?max_level -> print_value ?max_level (used_names env))

let print_term env =
  Return (fun ?max_level -> Tt.print_term ?max_level (used_names env))

let print_ty env =
  Return (fun ?max_level -> Tt.print_ty ?max_level (used_names env))

(** Coerce values *)
let as_term ~loc = function
  | Term e -> e
  | Ty _ -> Error.runtime ~loc "expected a term but got a type"
  | Closure _ -> Error.runtime ~loc "expected a term but got a function"
  | Handler _ -> Error.runtime ~loc "expected a term but got a handler"
  | Tag _  -> Error.runtime ~loc "expected a term but got a tag"

let as_ty ~loc = function
  | Term _ -> Error.runtime ~loc "expected a type but got a term"
  | Ty t -> t
  | Closure _ -> Error.runtime ~loc "expected a type but got a function"
  | Handler _ -> Error.runtime ~loc "expected a type but got a handler"
  | Tag _  -> Error.runtime ~loc "expected a type but got a tag"

let as_closure ~loc = function
  | Term _ -> Error.runtime ~loc "expected a function but got a term"
  | Ty _ -> Error.runtime ~loc "expected a function but got a type"
  | Closure f -> f
  | Handler _ -> Error.runtime ~loc "expected a function but got a handler"
  | Tag _  -> Error.runtime ~loc "expected a function but got a tag"

let as_handler ~loc = function
  | Term _ -> Error.runtime ~loc "expected a handler but got a term"
  | Ty _ -> Error.runtime ~loc "expected a handler but got a type"
  | Closure _ -> Error.runtime ~loc "expected a handler but got a function"
  | Handler h -> h
  | Tag _  -> Error.runtime ~loc "expected a handler but got a tag"

let as_option ~loc = function
  | Term _ -> Error.runtime ~loc "expected an option but got a term"
  | Ty _ -> Error.runtime ~loc "expected an option but got a type"
  | Closure _ -> Error.runtime ~loc "expected an option but got a function"
  | Handler h -> Error.runtime ~loc "expected an option but got a handler"
  | Tag (t,[]) when (Name.eq_ident t name_none)  -> None
  | Tag (t,[x]) when (Name.eq_ident t name_some) -> Some x
  | Tag _ -> Error.runtime ~loc "expected an option but got a tag"

(** Wrappers for making tags *)
let from_option = function
  | None -> Tag (name_none, [])
  | Some v -> Tag (name_some, [v])

let from_pair (v1, v2) = Tag (name_pair, [v1; v2])

let from_unit () = Tag (name_unit, [])

let rec from_list = function
  | [] -> Tag (name_nil, [])
  | v :: vs -> Tag (name_cons, [v; from_list vs])

(** Operations *)
let perform op vs env =
  let k _ = return in
  Perform (op, vs, env.dynamic, k)

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

let top_bound_names env = List.map fst env.bound, env

let top_get_env env = env,env

let get_env env = Return env

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

let lookup_constant x env = Return (get_constant x env)

let lookup_abstracting env = Return env.dynamic.abstracting

let get_bound ~loc k env =
  try
    snd (List.nth env.bound k)
  with
  | Failure _ -> Error.impossible ~loc "invalid de Bruijn index %d" k

let lookup_bound ~loc k env =
  Return (get_bound ~loc k env)

let add_bound0 x v env = {env with bound = (x,v)::env.bound }

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
  let rec is_bound = function
    | [] -> false
    | (y,_) :: lst -> Name.eq_ident x y || is_bound lst
  in
  is_bound env.bound ||
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
  (),{ env with handle = (op, xsc) :: env.handle }

(* This function for internal use *)
let lookup_handle op {handle=lst;_} =
  try
    Some (List.assoc op lst)
  with Not_found -> None

let set_continuation c m env =
  m { env with continuation = Some c }

let lookup_continuation {continuation;_} =
  Return continuation

let push_file f env =
  (),{ env with files = (Filename.basename f) :: env.files }

let included f env =
  List.mem (Filename.basename f) env.files, env

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
  bound = [] ;
  handle = [] ;
  continuation = None ;
  files = [] ;
  dynamic = {
    decls = [] ;
    abstracting = [] ;
  }
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
  | Return v as r ->
     begin match handler_val with
     | Some f -> apply_closure f v env
     | None -> r
     end
  | Perform (op, vs, dynamic, cont) ->
     let env = {env with dynamic} in
     let h = {handler_val; handler_ops; handler_finally=None} in
     let cont = mk_closure0 (fun v env -> handle_result h (apply_closure cont v) env) env in
     begin
       try
         let f = Name.IdentMap.find op handler_ops in
         f dynamic (vs, cont) env
       with
         Not_found ->
           Perform (op, vs, dynamic, cont)
     end
  end >>=
  (fun v env ->
     match handler_finally with
     | Some f -> apply_closure f v env
     | None -> Return v)

let rec top_handle ~loc r env =
  match r env with
    | Return v -> v,env
    | Perform (op, vs, dynamic, k) ->
       let env = {env with dynamic} in
       begin match lookup_handle op env with
        | None -> Error.runtime ~loc "unhandled operation %t" (Name.print_op op)
        | Some f ->
          let r = apply_closure f vs >>=
            apply_closure k
          in
          top_handle ~loc r env
       end

(*********)
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

    | Term _, (Ty _ | Closure _ | Handler _ | Tag _)
    | Ty _, (Term _ | Closure _ | Handler _ | Tag _)
    | Closure _, (Term _ | Ty _ | Handler _ | Tag _)
    | Handler _, (Term _ | Ty _ | Closure _ | Tag _)
    | Tag _, (Term _ | Ty _ | Closure _ | Handler _) ->
      false

    | Closure _, Closure _
    | Handler _, Handler _ ->
      false

