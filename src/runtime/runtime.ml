(** Runtime values and computations *)

type ref = Store.Ref.key
type dyn = Store.Dyn.key

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
  (* Toplevel constant declarations *)
  signature : Jdg.Signature.t;

  (* Current values of dynamic variables *)
  vars : value Store.Dyn.t
}

and lexical = {
  (* for printing only *)
  forbidden : Name.ident list;

  bound : value list;
  (* current continuation if we're handling an operation *)
  continuation : value continuation option;

  (* toplevel handlers *)
  handle : (Name.ident * (value list * Jdg.ty option,value) closure) list;
}

and state = value Store.Ref.t

and value =
  | Term of Jdg.term
  | Closure of (value, value) closure
  | Handler of handler
  | Tag of Name.ident * value list
  | Tuple of value list
  | Ref of ref
  | Dyn of dyn
  | String of string

(* It's important not to confuse the closure and the underlying ocaml function *)
and ('a, 'b) closure = Clos of ('a -> 'b comp)

and 'a result =
  | Return of 'a
  | Operation of Name.ident * value list * Jdg.ty option * dynamic * 'a continuation

and 'a comp = env -> 'a result * state

and operation_args = { args : value list; checking : Jdg.ty option }

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (value continuation -> (operation_args, value) closure) Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

and 'a continuation = Continuation of (value -> state -> 'a result * state)

type 'a toplevel = env -> 'a * env

(** Error reporting *)
type error =
  | ExpectedAtom of Jdg.term
  | UnknownExternal of string
  | UnknownConfig of string
  | Inapplicable of value
  | AnnotationMismatch of Jdg.ty * Jdg.ty
  | TypeMismatchCheckingMode of Jdg.term * Jdg.ty
  | EqualityFail of Jdg.term * Jdg.term
  | UnannotatedLambda of Name.ident
  | MatchFail of value
  | FailureFail of value
  | InvalidEqual of Jdg.ty
  | EqualityTypeExpected of Jdg.ty
  | InvalidAsEquality of Jdg.ty
  | ProductExpected of Jdg.ty
  | InvalidAsProduct of Jdg.ty
  | ListExpected of value
  | OptionExpected of value
  | TermExpected of value
  | ClosureExpected of value
  | HandlerExpected of value
  | FunctionExpected of Jdg.term
  | RefExpected of value
  | DynExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | InvalidConvertible of Jdg.ty * Jdg.ty * Jdg.eq_ty
  | InvalidCoerce of Jdg.ty * Jdg.term
  | InvalidFunConvertible of Jdg.ty * Jdg.eq_ty
  | InvalidFunCoerce of Jdg.term
  | UnhandledOperation of Name.operation * value list

exception Error of error Location.located

let error ~loc err = raise (Error (Location.locate err loc))


(** Make values *)
let mk_term j =
  Term j

let mk_handler h = Handler h
let mk_tag t lst = Tag (t, lst)
let mk_tuple lst = Tuple lst
let mk_string s = String s

let mk_closure0 f {lexical;_} = Clos (fun v env -> f v {env with lexical})
let mk_closure_ref g r = Clos (fun v env -> g v {env with lexical = (!r).lexical})

let mk_closure f = Closure (Clos f)

let apply_closure (Clos f) v env = f v env

let mk_cont f env = Continuation (fun v state -> f v {env with state})
let apply_cont (Continuation f) v {state;_} = f v state

(** References *)
let mk_ref v env =
  let x,state = Store.Ref.fresh v env.state in
  Return (Ref x),state

let lookup_ref x env =
  let v = Store.Ref.lookup x env.state in
  Return v, env.state

let update_ref x v env =
  let state = Store.Ref.update x v env.state in
  Return (), state

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind (r:'a comp) (f:'a -> 'b comp) : 'b comp = fun env ->
  match r env with
  | Return v, state -> f v {env with state}
  | Operation (op, vs, jt, d, k), state ->
     let env = {env with state} in
     let k = mk_cont (fun x -> bind (apply_cont k x) f) env in
     Operation (op, vs, jt, d, k), env.state

let (>>=) = bind

let top_bind m f env =
  let x, env = m env in
  f x env

type 'a caught =
  | CaughtJdg of Jdg.error Location.located
  | CaughtRuntime of error Location.located
  | Value of 'a

let catch m env =
  try
    let x, env = Lazy.force m env in
    Value x, env
  with
    | Jdg.Error err -> CaughtJdg err, env
    | Error err -> CaughtRuntime err, env

(** Returns *)
let top_return x env = x, env

let top_return_closure f env = mk_closure0 f env, env

let return x env = Return x, env.state

let return_term e = return (mk_term e)

let return_closure f env = Return (Closure (mk_closure0 f env)), env.state

let return_handler handler_val handler_ops handler_finally env =
  let option_map g = function None -> None | Some x -> Some (g x) in
  let h = {
    handler_val = option_map (fun v -> mk_closure0 v env) handler_val ;
    handler_ops = Name.IdentMap.map (fun f ->
      fun k -> mk_closure0 f {env with lexical = {env.lexical with continuation = Some k}}) handler_ops ;
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
    | Tuple _ -> "a tuple"
    | Ref _ -> "a reference"
    | Dyn _ -> "a dynamic variable"
    | String _ -> "a string"

(** Coerce values *)
let as_term ~loc = function
  | Term e -> e
  | (Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (TermExpected v)

let as_closure ~loc = function
  | Closure f -> f
  | (Term _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (ClosureExpected v)

let as_handler ~loc = function
  | Handler h -> h
  | (Term _ | Closure _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (HandlerExpected v)

let as_ref ~loc = function
  | Ref v -> v
  | (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | Dyn _ | String _) as v ->
    error ~loc (RefExpected v)

let as_dyn ~loc = function
  | Dyn v -> v
  | (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~loc (DynExpected v)

let as_string ~loc = function
  | String v -> v
  | (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | Dyn _ | Ref _) as v ->
    error ~loc (StringExpected v)

(** Operations *)

let operation op ?checking vs env =
  Operation (op, vs, checking, env.dynamic, mk_cont return env), env.state

(** Interact with the environment *)

let get_env env = Return env, env.state

let get_typing_signature env = env.dynamic.signature

let lookup_typing_signature env =
  Return (get_typing_signature env), env.state

let index_of_level k env =
  let n = List.length env.lexical.bound - k - 1 in
  Return n, env.state

let get_bound ~loc k env = List.nth env.lexical.bound k

let lookup_bound ~loc k env =
  Return (get_bound ~loc k env), env.state

let get_dyn dyn env = Store.Dyn.lookup dyn env.dynamic.vars

let lookup_dyn dyn env =
  Return (get_dyn dyn env), env.state

let add_bound0 v env = {env with lexical = { env.lexical with
                                             bound = v :: env.lexical.bound } }

let add_free ~loc x jt m env =
  let jy = Jdg.Ctx.add_fresh jt x in
  let y_val = mk_term (Jdg.atom_term ~loc jy) in
  let env = add_bound0 y_val env in
  m jy env

let add_constant0 ~loc x t env =
  { env with dynamic = {env.dynamic with signature =
                           Jdg.Signature.add_constant x t env.dynamic.signature };
             lexical = {env.lexical with forbidden = x :: env.lexical.forbidden } }

let add_constant ~loc x t env = (), add_constant0 ~loc x t env

(* XXX rename to bind_value *)
let add_bound v m env =
  let env = add_bound0 v env in
  m env

let add_bound_rec0 lst env =
  let r = ref env in
  let env =
    List.fold_left
      (fun env g ->
        let v = Closure (mk_closure_ref g r) in
        add_bound0 v env)
      env lst
  in
  r := env ;
  env

let add_bound_rec lst m env =
  let env = add_bound_rec0 lst env in
  m env

let push_bound = add_bound0

let add_topbound v env =
  (), add_bound0 v env

let now0 x v env =
  { env with dynamic = {env.dynamic with vars = Store.Dyn.update x v env.dynamic.vars } }

let now x v m env =
  let env = now0 x v env in
  m env

let top_now x v env =
  let env = now0 x v env in
  (), env

let add_dynamic0 ~loc x v env =
  let y,vars = Store.Dyn.fresh v env.dynamic.vars in
  { env with dynamic = {env.dynamic with vars };
             lexical = {env.lexical with
                        bound = Dyn y :: env.lexical.bound } }

let add_dynamic ~loc x v env = (), add_dynamic0 ~loc x v env

let add_handle0 op xsc env =
  { env with lexical =
               { env.lexical with
                 handle = (op, xsc) :: env.lexical.handle } }

let add_handle op xsc env = (), add_handle0 op xsc env

let add_topbound_rec lst env =
  let env = add_bound_rec0 lst env in
  (), env

(* This function for internal use *)
let lookup_handle op {lexical={handle=lst;_};_} =
  try
    Some (List.assoc op lst)
  with Not_found -> None

let continue ~loc v ({lexical={continuation;_};_} as env) =
  match continuation with
    | Some cont -> apply_cont cont v env
    | None -> assert false

(** Printers *)

(** Generate a printing environment from runtime environment *)
let get_penv env =
  { TT.forbidden = env.lexical.forbidden ;
    TT.atoms = Name.atom_printer () }

let lookup_penv env =
  Return (get_penv env), env.state

let top_lookup_penv env =
  get_penv env, env


let rec as_list_opt = function
  | Tag (t, []) when Name.eq_ident t Name.Predefined.nil -> Some []
  | Tag (t, [x;xs]) when Name.eq_ident t Name.Predefined.cons ->
     begin
       match as_list_opt xs with
       | None -> None
       | Some xs -> Some (x :: xs)
     end
  | (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) ->
     None

let rec print_value ?max_level ~penv v ppf =
  match v with

  | Term e -> Jdg.print_term ~penv:penv ?max_level e ppf

  | Closure f -> Format.fprintf ppf "<function>"

  | Handler h -> Format.fprintf ppf "<handler>"

  | Tag (t, lst) as v ->
     begin
       match as_list_opt v with
       | Some lst -> Format.fprintf ppf "@[<hov>[%t]@]"
                                    (Print.sequence (print_value ~max_level:Level.highest ~penv) "," lst)
       | None ->  print_tag ?max_level ~penv t lst ppf
     end

  | Tuple lst -> Format.fprintf ppf "(%t)"
                  (Print.sequence (print_value ~max_level:Level.highest ~penv) "," lst)

  | Ref v -> Print.print ?max_level ~at_level:Level.highest ppf "ref<%t>"
                  (Store.Ref.print_key v)

  | Dyn v -> Print.print ?max_level ~at_level:Level.highest ppf "dyn<%t>"
                  (Store.Dyn.print_key v)

  | String s -> Format.fprintf ppf "\"%s\"" s

and print_tag ?max_level ~penv t lst ppf =
  match t, lst with

  | Name.Ident (_, Name.Prefix), [v] ->
     (* prefix tag applied to one argument *)
     (* Although it is reasonable to parse prefix operators as
        binding very tightly, it can be confusing to see
            f !! x instead of f (!! x).
        So we print out unary tags, at least, with the
        same parenthesization as application, i.e.,
        Level.app and Level.app_right instead of
        Level.prefix and Level.prefix_arg *)
     Print.print ppf ?max_level ~at_level:Level.app "%t@ %t"
                 (Name.print_ident ~parentheses:false t)
                 (print_value ~max_level:Level.app_right ~penv v)

  | Name.Ident (_, Name.Infix fixity), [v1; v2] ->
     (* infix tag applied to two arguments *)
     let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
     Print.print ppf ?max_level ~at_level:lvl_op "%t@ %t@ %t"
                 (print_value ~max_level:lvl_left ~penv v1)
                 (Name.print_ident ~parentheses:false t)
                 (print_value ~max_level:lvl_right ~penv v2)

  | _ ->
     (* print as application *)
     begin
       match lst with
       | [] -> Name.print_ident t ppf
       | (_::_) -> Print.print ?max_level ~at_level:Level.app ppf "%t@ %t"
                               (Name.print_ident t)
                               (Print.sequence (print_value ~max_level:Level.app_right ~penv) "" lst)
     end

let print_operation ~penv op vs ppf =
  match op, vs with

  | Name.Ident (_, Name.Prefix), [v] ->
     (* prefix op applied to one argument *)
     Print.print ppf ~at_level:Level.prefix "%t@ %t"
                 (Name.print_ident ~parentheses:false op)
                 (print_value ~max_level:Level.prefix_arg ~penv v)

  | Name.Ident (_, Name.Infix fixity), [v1; v2] ->
     (* infix op applied to two arguments *)
     let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
     Print.print ppf ~at_level:lvl_op "%t@ %t@ %t"
                 (print_value ~max_level:lvl_left ~penv v1)
                 (Name.print_ident ~parentheses:false op)
                 (print_value ~max_level:lvl_right ~penv v2)

  | _ ->
     (* print as application *)
     begin
       match vs with
       | [] -> Name.print_ident op ppf
       | (_::_) -> Print.print ~at_level:Level.app ppf "%t@ %t"
                               (Name.print_ident op)
                               (Print.sequence (print_value ~max_level:Level.app_right ~penv) "" vs)
     end

let print_error ~penv err ppf =
  match err with

  | ExpectedAtom j ->
     Format.fprintf ppf "expected an atom but got %t"
                    (Jdg.print_term ~penv:penv j)

  | UnknownExternal s ->
     Format.fprintf ppf "unknown external %s" s

  | UnknownConfig s ->
    Format.fprintf ppf "unknown config %s" s

  | Inapplicable v ->
     Format.fprintf ppf "cannot apply %s" (name_of v)

  | AnnotationMismatch (t1, t2) ->
      Format.fprintf ppf
      "@[<v>The type annotation is@,   @[<hov>%t@]@ but the surroundings imply it should be@,   @[<hov>%t@].@]"
                    (Jdg.print_ty ~penv:penv t1)
                    (Jdg.print_ty ~penv:penv t2)

  | TypeMismatchCheckingMode (v, t) ->
      Format.fprintf ppf "The term@,   @[<hov>%t@]@ is expected by its surroundings to have type@,   @[<hov>%t@]"
                    (Jdg.print_term ~penv:penv v)
                    (Jdg.print_ty ~penv:penv t)

  | EqualityFail (e1, e2) ->
     Format.fprintf ppf "failed to check that@ %t@ and@ %t@ are equal"
                    (Jdg.print_term ~penv:penv e1)
                    (Jdg.print_term ~penv:penv e2)

  | UnannotatedLambda x ->
     Format.fprintf ppf "cannot infer the type of@ %t" (Name.print_ident x)

  | MatchFail v ->
     Format.fprintf ppf "@[<v>No matching pattern found for value@,   @[<hov>%t@]@]@."
                    (print_value ~penv v)

  | FailureFail v ->
     Format.fprintf ppf "expected to fail but computed@ %t"
                    (print_value ~penv v)

  | InvalidEqual j ->
     Format.fprintf ppf "this should be a witness of %t"
                    (Jdg.print_ty ~penv:penv j)

  | EqualityTypeExpected j ->
     Format.fprintf ppf "expected an equality type but got@ %t"
                    (Jdg.print_ty ~penv:penv j)

  | InvalidAsEquality j ->
     Format.fprintf ppf "this should be an equality between %t and an equality"
                    (Jdg.print_ty ~penv:penv j)

  | ProductExpected j ->
     Format.fprintf ppf "expected a product but got@ %t"
                    (Jdg.print_ty ~penv:penv j)

  | InvalidAsProduct j ->
     Format.fprintf ppf "this should be an equality between %t and a product"
                    (Jdg.print_ty ~penv:penv j)

  | FunctionExpected t ->
     Format.fprintf ppf "@[<v>Application of the non-function:@    @[<hov>%t@]@]@."
                    (Jdg.print_term ~penv:penv t)

  | ListExpected v ->
     Format.fprintf ppf "expected a list but got %s" (name_of v)

  | OptionExpected v ->
     Format.fprintf ppf "expected an option but got %s" (name_of v)

  | TermExpected v ->
     Format.fprintf ppf "expected a term but got %s" (name_of v)

  | ClosureExpected v ->
     Format.fprintf ppf "expected a function but got %s" (name_of v)

  | HandlerExpected v ->
     Format.fprintf ppf "expected a handler but got %s" (name_of v)

  | RefExpected v ->
     Format.fprintf ppf "expected a reference but got %s" (name_of v)

  | DynExpected v ->
     Format.fprintf ppf "expected a dynamic variable but got %s" (name_of v)

  | StringExpected v ->
     Format.fprintf ppf "expected a string but got %s" (name_of v)

  | CoercibleExpected v ->
    Format.fprintf ppf "expected a coercible but got %s" (name_of v)

  | InvalidConvertible (t1, t2, eq) ->
     Format.fprintf ppf "expected a witness of equality between %t and %t but got %t"
                    (Jdg.print_ty ~penv t1)
                    (Jdg.print_ty ~penv t2)
                    (Jdg.print_eq_ty ~penv eq)

  | InvalidCoerce (t, e) ->
     Format.fprintf ppf "expected a term of type %t but got %t"
                    (Jdg.print_ty ~penv t)
                    (Jdg.print_term ~penv e)

  | InvalidFunConvertible (t, eq) ->
     Format.fprintf ppf "expected a witness of equality between %t and a product but got %t"
                    (Jdg.print_ty ~penv t)
                    (Jdg.print_eq_ty ~penv eq)

  | InvalidFunCoerce e ->
     Format.fprintf ppf "expected a term of a product type got %t"
                    (Jdg.print_term ~penv e)

  | UnhandledOperation (op, vs) ->
     Format.fprintf ppf "@[<v>Unhandled operation:@.   @[<hov>%t@]@]@."
                    (print_operation ~penv op vs)



let empty = {
  lexical = {
    forbidden = [] ;
    bound = [] ;
    handle = [] ;
    continuation = None ;
  } ;
  dynamic = {
    signature = Jdg.Signature.empty ;
    vars = Store.Dyn.empty ;
  } ;
  state = Store.Ref.empty;
}

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
     let cont = mk_cont (fun v env -> handle_comp h (apply_cont cont v) env) env in
     begin
       try
         let f = (Name.IdentMap.find op handler_ops) cont in
         (apply_closure f {args=vs;checking=jt}) env
       with
         Not_found ->
           Operation (op, vs, jt, dynamic, cont), env.state
     end
  end >>= fun v ->
  match handler_finally with
    | Some f -> apply_closure f v
    | None -> return v

let top_handle ~loc r env =
  let rec handle r env =
    match r with
    | Return v, state -> v, state
    | Operation (op, vs, checking, dynamic, k), state ->
       let env = {env with dynamic;state} in
       begin match lookup_handle op env with
        | None -> error ~loc (UnhandledOperation (op, vs))
        | Some f ->
          let r = apply_closure f (vs,checking) >>=
            apply_cont k
          in
          handle (r env) env
       end
  in
  let v, state = handle (r env) env in
  v, { env with state }

(** Equality *)
let rec equal_value v1 v2 =
  match v1, v2 with
    | Term j1, Term j2 ->
      Jdg.alpha_equal j1 j2

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

    | Tuple lst1, Tuple lst2 ->
       let rec fold = function
         | [], [] -> true
         | v1 :: lst1, v2 :: lst2 -> equal_value v1 v2 && fold (lst1, lst2)
         | [], _::_ | _::_, [] -> false
       in
       fold (lst1, lst2)

    | Ref v1, Ref v2 ->
       (* XXX should we compare references by value instead? *)
       Store.Ref.key_eq v1 v2

    | Dyn v1, Dyn v2 ->
       (* XXX should we compare dynamics by value instead? *)
       Store.Dyn.key_eq v1 v2

    | String s1, String s2 ->
      s1 = s2

    | Closure _, Closure _
    | Handler _, Handler _ ->
       (* XXX should we use physical comparison == instead? *)
       false

    (* At some level the following is a bit ridiculous *)
    | Term _, (Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Closure _, (Term _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Handler _, (Term _ | Closure _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Tag _, (Term _ | Closure _ | Handler _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Tuple _, (Term _ | Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | String _)
    | String _, (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _)
    | Ref _, (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | String _ | Dyn _)
    | Dyn _, (Term _ | Closure _ | Handler _ | Tag _ | Tuple _ | String _ | Ref _) ->
       false


type topenv = env

let exec m = m

module Json =
struct

  let rec value v =
    match v with

    | Term e -> Json.tag "Term" [Jdg.Json.term e]

    | Closure _ -> Json.tag "<fun>" []

    | Handler _ -> Json.tag "<handler>" []

    | Tag (c, lst) -> Json.tag "Tag" [Name.Json.ident c; Json.List (List.map value lst)]

    | Tuple lst -> Json.tag "Tuple" [Json.List (List.map value lst)]

    | Ref r -> Json.tag "<ref>" []

    | Dyn r -> Json.tag "<dyn>" []

    | String s -> Json.tag "String" [Json.String s]

end
