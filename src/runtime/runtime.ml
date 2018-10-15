(** Runtime values and computations *)

type ref = Store.Ref.key (* TODO rename to aml_ref, or just get rid of this *)
type dyn = Store.Dyn.key (* TODO rename to aml_dyn, or just get rid of this *)

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
  handle : (Name.ident * (value list * is_type_abstraction option,value) closure) list;
}

and state = value Store.Ref.t

and is_term_abstraction = Jdg.is_term Jdg.abstraction
and is_type_abstraction = Jdg.is_type Jdg.abstraction
and eq_term_abstraction = Jdg.eq_term Jdg.abstraction
and eq_type_abstraction = Jdg.eq_type Jdg.abstraction

and value =
  | IsTerm of is_term_abstraction
  | IsType of is_type_abstraction
  | EqTerm of eq_term_abstraction
  | EqType of eq_type_abstraction
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
  | Operation of Name.ident * value list * is_type_abstraction option * dynamic * 'a continuation

and 'a comp = env -> 'a result * state

and operation_args = { args : value list; checking : is_type_abstraction option }

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (value continuation -> (operation_args, value) closure) Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

and 'a continuation = Continuation of (value -> state -> 'a result * state)

type 'a toplevel = env -> 'a * env

(** Error reporting *)
type error =
  | ExpectedAtom of Jdg.is_term
  | UnknownExternal of string
  | UnknownConfig of string
  | Inapplicable of value
  | AnnotationMismatch of Jdg.is_type * Jdg.is_type
  | TypeMismatchCheckingMode of is_term_abstraction * is_type_abstraction
  | EqualityFail of Jdg.is_term * Jdg.is_term
  | UnannotatedAbstract of Name.ident
  | MatchFail of value
  | FailureFail of value
  | InvalidEqualTerm of Jdg.is_term * Jdg.is_term
  | InvalidEqualType of Jdg.is_type * Jdg.is_type
  | ListExpected of value
  | OptionExpected of value
  | IsTypeExpected of value
  | IsTermExpected of value
  | EqTypeExpected of value
  | EqTermExpected of value
  | JudgementExpected of value
  | ClosureExpected of value
  | HandlerExpected of value
  | RefExpected of value
  | DynExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | InvalidConvertible of Jdg.is_type * Jdg.is_type * Jdg.eq_type
  | InvalidCoerce of Jdg.is_type * Jdg.is_term
  | UnhandledOperation of Name.operation * value list

exception Error of error Location.located

let error ~loc err = raise (Error (Location.locate err loc))


(** Make values *)

let mk_is_term t = IsTerm t
let mk_is_type t = IsType t
let mk_eq_term eq = EqTerm eq
let mk_eq_type eq = EqType eq

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
  | Result of 'a

let catch ~loc m env =
  try
    let x, env = Lazy.force m env in
    Result x, env
  with
    | Jdg.Error err -> CaughtJdg (Location.locate err loc), env
    | Error err -> CaughtRuntime err, env

(** Returns *)
let top_return x env = x, env

let top_return_closure f env = mk_closure0 f env, env

let return x env = Return x, env.state

let return_is_term e = return (mk_is_term e)
let return_is_type e = return (mk_is_type e)
let return_eq_term e = return (mk_eq_term e)
let return_eq_type e = return (mk_eq_type e)

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
    | IsTerm _ -> "a term"
    | IsType _ -> "a type"
    | EqTerm _ -> "a term equality"
    | EqType _ -> "a type equality"
    | Closure _ -> "a function"
    | Handler _ -> "a handler"
    | Tag _ -> "a data tag"
    | Tuple _ -> "a tuple"
    | Ref _ -> "a reference"
    | Dyn _ -> "a dynamic variable"
    | String _ -> "a string"

(** Coerce values *)
let as_is_term ~loc = function
  | IsTerm e as v ->
     begin match Jdg.invert_is_term_abstraction e with
     | Jdg.NotAbstract e -> e
     | Jdg.Abstract _ -> error ~loc (IsTermExpected v)
     end
  | (IsType _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (IsTermExpected v)

let as_is_type ~loc = function
  | IsType t as v ->
     begin match Jdg.invert_is_type_abstraction t with
     | Jdg.NotAbstract t -> t
     | Jdg.Abstract _ -> error ~loc (IsTermExpected v)
     end
  | (IsTerm _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (IsTypeExpected v)

let as_eq_type ~loc = function
  | EqType eq as v ->
     begin match Jdg.invert_eq_type_abstraction eq with
     | Jdg.NotAbstract eq -> eq
     | Jdg.Abstract _ -> error ~loc (EqTypeExpected v)
     end
  | (IsType _ | IsTerm _ | EqTerm _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTypeExpected v)

let as_eq_term ~loc = function
  | EqTerm eq as v ->
     begin match Jdg.invert_eq_term_abstraction eq with
     | Jdg.NotAbstract eq -> eq
     | Jdg.Abstract _ -> error ~loc (EqTermExpected v)
     end
  | (IsType _ | IsTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTermExpected v)

let as_closure ~loc = function
  | Closure f -> f
  | (IsTerm _ | IsType _ | EqTerm _ | EqType _ |
     Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (ClosureExpected v)

let as_handler ~loc = function
  | Handler h -> h
  | (IsTerm _ | IsType _ | EqTerm _ | EqType _ |
     Closure _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (HandlerExpected v)

let as_ref ~loc = function
  | Ref v -> v
  | (IsTerm _ | IsType _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Dyn _ | String _) as v ->
    error ~loc (RefExpected v)

let as_dyn ~loc = function
  | Dyn v -> v
  | (IsTerm _ | IsType _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~loc (DynExpected v)

let as_string ~loc = function
  | String v -> v
  | (IsTerm _ | IsType _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Dyn _ | Ref _) as v ->
    error ~loc (StringExpected v)

(** Operations *)

let operation op ?checking vs env =
  Operation (op, vs, checking, env.dynamic, mk_cont return env), env.state

(** Interact with the environment *)

let get_env env = Return env, env.state

let top_get_env env = env, env

let get_signature env = env.dynamic.signature

let lookup_signature env =
  Return env.dynamic.signature, env.state

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

let add_free x jt m env =
  let jy = Jdg.fresh_atom x jt in
  let y_val = mk_is_term (Jdg.form_not_abstract (Jdg.form_is_term_atom jy)) in
  let env = add_bound0 y_val env in
  m jy env

(* XXX This will get fancier once we have rules and we want to add them to the signature
let add_constant0 ~loc x t env =
  { env with dynamic = {env.dynamic with signature =
                           Jdg.Signature.add_constant x t env.dynamic.signature };
             lexical = {env.lexical with forbidden = x :: env.lexical.forbidden } }

let add_constant ~loc x t env = (), add_constant0 ~loc x t env
*)


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
  | (IsTerm _ | IsType _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) ->
     None

let rec print_value ?max_level ~penv v ppf =
  match v with

  | IsTerm e -> Jdg.print_is_term_abstraction ~penv:penv ?max_level e ppf

  | IsType t -> Jdg.print_is_type_abstraction ~penv:penv ?max_level t ppf

  | EqTerm eq -> Jdg.print_eq_term_abstraction ~penv:penv ?max_level eq ppf

  | EqType eq -> Jdg.print_eq_type_abstraction ~penv:penv ?max_level eq ppf

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
                    (Jdg.print_is_term ~penv:penv j)

  | UnknownExternal s ->
     Format.fprintf ppf "unknown external %s" s

  | UnknownConfig s ->
    Format.fprintf ppf "unknown config %s" s

  | Inapplicable v ->
     Format.fprintf ppf "cannot apply %s" (name_of v)

  | AnnotationMismatch (t1, t2) ->
      Format.fprintf ppf
      "@[<v>The type annotation is@,   @[<hov>%t@]@ but the surroundings imply it should be@,   @[<hov>%t@].@]"
                    (Jdg.print_is_type ~penv:penv t1)
                    (Jdg.print_is_type ~penv:penv t2)

  | TypeMismatchCheckingMode (v, t) ->
      Format.fprintf ppf "The term@,   @[<hov>%t@]@ is expected by its surroundings to have type@,   @[<hov>%t@]"
                    (Jdg.print_is_term_abstraction ~penv:penv v)
                    (Jdg.print_is_type_abstraction ~penv:penv t)

  | EqualityFail (e1, e2) ->
     Format.fprintf ppf "failed to check that@ %t@ and@ %t@ are equal"
                    (Jdg.print_is_term ~penv:penv e1)
                    (Jdg.print_is_term ~penv:penv e2)

  | UnannotatedAbstract x ->
     Format.fprintf ppf "cannot infer the type of@ %t" (Name.print_ident x)

  | MatchFail v ->
     Format.fprintf ppf "@[<v>No matching pattern found for value@,   @[<hov>%t@]@]@."
                    (print_value ~penv v)

  | FailureFail v ->
     Format.fprintf ppf "expected to fail but computed@ %t"
                    (print_value ~penv v)

  | InvalidEqualTerm (e1, e2) ->
     Format.fprintf ppf "this should be equality of terms %t@ and@ %t"
                    (Jdg.print_is_term ~penv:penv e1)
                    (Jdg.print_is_term ~penv:penv e2)

  | InvalidEqualType (t1, t2) ->
     Format.fprintf ppf "this should be equality of types %t@ and@ %t"
                    (Jdg.print_is_type ~penv:penv t1)
                    (Jdg.print_is_type ~penv:penv t2)

  | ListExpected v ->
     Format.fprintf ppf "expected a list but got %s" (name_of v)

  | OptionExpected v ->
     Format.fprintf ppf "expected an option but got %s" (name_of v)

  | IsTypeExpected v ->
     Format.fprintf ppf "expected a type but got %s" (name_of v)

  | IsTermExpected v ->
     Format.fprintf ppf "expected a term but got %s" (name_of v)

  | EqTypeExpected v ->
     Format.fprintf ppf "expected a type equality but got %s" (name_of v)

  | EqTermExpected v ->
     Format.fprintf ppf "expected a term equality but got %s" (name_of v)

  | JudgementExpected v ->
     Format.fprintf ppf "expected a judgement but got %s" (name_of v)

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
                    (Jdg.print_is_type ~penv t1)
                    (Jdg.print_is_type ~penv t2)
                    (Jdg.print_eq_type ~penv eq)

  | InvalidCoerce (t, e) ->
     Format.fprintf ppf "expected a term of type %t but got %t"
                    (Jdg.print_is_type ~penv t)
                    (Jdg.print_is_term ~penv e)

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
    | IsTerm e1, IsTerm e2 ->
      Jdg.alpha_equal_abstraction Jdg.alpha_equal_term e1 e2

    | IsType t1, IsType t2 ->
      Jdg.alpha_equal_abstraction Jdg.alpha_equal_type t1 t2

    | EqTerm eq1, EqTerm eq2 ->
       (* XXX: should we even compare equality judgements for equality? That will lead to comparison of contexts. *)
       eq1 == eq2

    | EqType eq1, EqType eq2 ->
       (* XXX: should we even compare equality judgements for equality? That will lead to comparison of contexts. *)
       eq1 == eq2

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
    | IsTerm _, (IsType _ | EqTerm _ | EqType _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | IsType _, (IsTerm _ | EqTerm _ | EqType _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | EqTerm _, (IsTerm _ | IsType _ | EqType _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | EqType _, (IsTerm _ | IsType _ | EqTerm _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Closure _, (IsTerm _ | IsType _ | EqTerm _ | EqType _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Handler _, (IsTerm _ | IsType _ | EqTerm _ | EqType _ | Closure _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Tag _, (IsTerm _ | IsType _ | EqTerm _ | EqType _ | Closure _ | Handler _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Tuple _, (IsTerm _ | IsType _ | EqTerm _ | EqType _ | Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | String _)
    | String _, (IsTerm _ | IsType _ | EqTerm _ | EqType _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _)
    | Ref _, (IsTerm _ | IsType _ | EqTerm _ | EqType _ | Closure _ | Handler _ | Tag _ | Tuple _ | String _ | Dyn _)
    | Dyn _, (IsTerm _ | IsType _ | EqTerm _ | EqType _ | Closure _ | Handler _ | Tag _ | Tuple _ | String _ | Ref _) ->
       false


type topenv = env

let exec m = m

module Json =
struct

  let rec value v =
    match v with

    | IsTerm e -> Json.tag "IsTerm" [Jdg.Json.abstraction Jdg.Json.is_term e]

    | IsType t -> Json.tag "IsType" [Jdg.Json.abstraction Jdg.Json.is_type t]

    | EqType eq -> Json.tag "EqType" [Jdg.Json.abstraction Jdg.Json.eq_type eq]

    | EqTerm eq -> Json.tag "EqTerm" [Jdg.Json.abstraction Jdg.Json.eq_term eq]

    | Closure _ -> Json.tag "<fun>" []

    | Handler _ -> Json.tag "<handler>" []

    | Tag (c, lst) -> Json.tag "Tag" [Name.Json.ident c; Json.List (List.map value lst)]

    | Tuple lst -> Json.tag "Tuple" [Json.List (List.map value lst)]

    | Ref r -> Json.tag "<ref>" []

    | Dyn r -> Json.tag "<dyn>" []

    | String s -> Json.tag "String" [Json.String s]

end
