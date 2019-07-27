(** Runtime values and computations *)

type ml_ref = Store.Ref.key
type ml_dyn = Store.Dyn.key

type coercible =
  | NotCoercible
  | Convertible of Nucleus.eq_type_abstraction
  | Coercible of Nucleus.is_term_abstraction

(** In the future we should be able to drop the path and just use an ID, or even an integer. *)
type ml_constructor = Ident.t

(** This module defines 2 monads:
    - the computation monad [comp], providing operations and an environment of which part is dynamically scoped.
      Primitives are like [add_value].
    - the toplevel monad [toplevel], a standard state monad with restricted accessors.
      Primitives are like [top_add_value].
      Some modifications of the environment may only be done at the top level, for instance declaring constants.
    For internal use, functions which work on the environment may be defined, eg [add_value0].

    Finally in a small number of restricted circumstances the environment is accessed outside the monads.
*)

module SymbolTable :
sig
  type 'v t

  val initial : 'v t
  val add_ml_value : 'v -> 'v t -> 'v t
  val get_ml_value : Path.t -> 'v t -> 'v

  val push_ml_module : 'v t -> 'v t
  val pop_ml_module : 'v t -> 'v t
end =
struct
  module TableMap = Map.Make(
                     struct
                       type t = int
                       let compare = Pervasives.compare
                     end)

  type 'v table = {
      table_map : 'v TableMap.t;
      table_next : int;
    }

  let add info {table_map; table_next} =
    { table_map = TableMap.add table_next info table_map ;
      table_next = table_next + 1 }

  let get k {table_map; table_next} = TableMap.find k table_map

  let get_last {table_map; table_next} = TableMap.find (table_next - 1) table_map

  let set_last info ({table_map; table_next} as tbl) =
    { tbl with table_map = TableMap.add (table_next - 1) info tbl.table_map }

  type 'v ml_module = {
      ml_modules : ('v ml_module) table;
      ml_values : 'v table;
  }

  let empty_ml_module =
    let empty = { table_map = TableMap.empty; table_next = 0 } in
    { ml_modules = empty;
      ml_values = empty
    }

  type 'a t = {
      top_module : 'a ml_module ;
      current_depth : int;
    }

  let initial =
    { top_module = empty_ml_module;
      current_depth = 0
    }

  let at_current adder tbl =
    let rec update mdl = function

      | 0 -> adder mdl

      | depth ->
         let mdl' = get_last mdl.ml_modules in
         let mdl' = update mdl' (depth-1) in
         { mdl with ml_modules = set_last mdl' mdl.ml_modules }

    in
    { tbl with top_module = update tbl.top_module tbl.current_depth }

  let add_ml_value info tbl =
    at_current (fun mdl -> { mdl with ml_values = add info mdl.ml_values }) tbl

  let rec get_ml_module pth mdl =
    match pth with

    | Path.Direct (Path.Level (_, lvl)) -> get lvl mdl.ml_modules

    | Path.Module (mdl_path, Path.Level (_, lvl)) ->
       let mdl = get_ml_module mdl_path mdl in
       get lvl mdl.ml_modules

  let get_path getter pth tbl =
    match pth with

    | Path.Direct lvl -> getter lvl tbl.top_module

    | Path.Module (mdl_path, lvl) ->
       let mdl = get_ml_module mdl_path tbl.top_module in
       getter lvl mdl

  let get_ml_value pth tbl =
    get_path (fun (Path.Level (_, k)) mdl -> get k mdl.ml_values) pth tbl

  let push_ml_module tbl =
    let tbl = at_current (fun mdl -> { mdl with ml_modules = add empty_ml_module mdl.ml_modules }) tbl in
    { tbl with current_depth = tbl.current_depth + 1 }

  let pop_ml_module tbl =
    { tbl with current_depth = tbl.current_depth - 1 }
end

(** Printing environment *)
type penv = {
  forbidden : Name.set ;
  opens : Path.set
}

let penv_forbid x penv =
  { penv with forbidden = Name.set_add x penv.forbidden }

let penv_open pth penv =
  { penv with opens = Path.set_add pth penv.opens }

let mk_nucleus_penv {forbidden;opens} =
  { Nucleus.forbidden = forbidden ;
    Nucleus.opens = opens ;
    Nucleus.debruijn = [] }

(** Runtime environment. *)
type env = {
  dynamic : dynamic;
  lexical : lexical;
  state   : state  ;
}

and dynamic = {
  (* Toplevel constant declarations *)
  signature : Nucleus.signature;

  (* Current values of dynamic variables *)
  vars : value Store.Dyn.t
}

and lexical = {
  table : value SymbolTable.t ;

  (* Current printing environment *)
  penv : penv;

  (* values to which de Bruijn indices are bound *)
  current_values : value list;

  (* current continuation if we're handling an operation *)
  ml_yield : value continuation option;
}

and state = value Store.Ref.t

and value =
  | Judgement of Nucleus.judgement_abstraction
  | Boundary of Nucleus.boundary_abstraction
  | Closure of (value, value) closure
  | Handler of handler
  | Tag of ml_constructor * value list
  | Tuple of value list
  | Ref of ml_ref
  | Dyn of ml_dyn
  | String of string

(* It's important not to confuse the closure and the underlying ocaml function *)
and ('a, 'b) closure = Clos of ('a -> 'b comp)

and 'a result =
  | Return of 'a
  | Operation of Ident.t * value list * Nucleus.boundary_abstraction option * dynamic * 'a continuation

and 'a comp = env -> 'a result * state

and operation_args = { args : value list; checking : Nucleus.boundary_abstraction option }

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (value continuation -> (operation_args, value) closure) Ident.map;
  handler_finally: (value,value) closure option;
}

and 'a continuation = Continuation of (value -> state -> 'a result * state)

type 'a toplevel = env -> 'a * env

(** Error reporting *)
type error =
  | ExpectedAtom of Nucleus.is_term
  | UnknownExternal of string
  | UnknownConfig of string
  | Inapplicable of value
  | AnnotationMismatch of Nucleus.is_type * Nucleus.is_type_abstraction
  | TypeMismatchCheckingMode of Nucleus.judgement_abstraction * Nucleus.boundary_abstraction
  | UnexpectedAbstraction
  | TermEqualityFail of Nucleus.is_term * Nucleus.is_term
  | TypeEqualityFail of Nucleus.is_type * Nucleus.is_type
  | UnannotatedAbstract of Name.t
  | MatchFail of value
  | FailureFail of value
  | InvalidComparison
  | InvalidEqualTerm of Nucleus.is_term * Nucleus.is_term
  | InvalidEqualType of Nucleus.is_type * Nucleus.is_type
  | BoolExpected of value
  | ListExpected of value
  | OptionExpected of value
  | IsTypeExpected of value
  | IsTermExpected of value
  | EqTypeExpected of value
  | EqTermExpected of value
  | AbstractionExpected
  | JudgementExpected of value
  | ClosureExpected of value
  | HandlerExpected of value
  | RefExpected of value
  | DynExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | InvalidConvert of Nucleus.judgement_abstraction * Nucleus.eq_type_abstraction
  | InvalidCoerce of Nucleus.judgement_abstraction * Nucleus.boundary_abstraction
  | UnhandledOperation of Ident.t * value list
  | InvalidPatternMatch of value
  | InvalidHandlerMatch

exception Error of error Location.located

let error ~loc err = raise (Error (Location.locate err loc))

let equal_tag = Ident.equal

(** Make values *)

let mk_judgement jdg = Judgement jdg
let mk_boundary bdry = Boundary bdry
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
  let x, state = Store.Ref.fresh v env.state in
  Return (Ref x), state

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
  | Return v, state ->
     f v { env with state }
  | Operation (op, vs, jt, d, k), state ->
     let env = { env with state } in
     let k = mk_cont (fun x -> bind (apply_cont k x) f) env in
     Operation (op, vs, jt, d, k), env.state

let (>>=) = bind

let top_bind m f env =
  let x, env = m env in
  f x env

(** Returns *)
let top_return x env = x, env

let top_return_closure f env = mk_closure0 f env, env

let return x env = Return x, env.state

let return_judgement jdg = return (Judgement jdg)

let return_boundary bdry = return (Boundary bdry)

let return_closure f env = Return (Closure (mk_closure0 f env)), env.state

let return_handler handler_val handler_ops handler_finally env =
  let option_map g = function None -> None | Some x -> Some (g x) in
  let h = {
    handler_val = option_map (fun v -> mk_closure0 v env) handler_val ;
    handler_ops = Ident.map (fun f ->
      fun k -> mk_closure0 f {env with lexical = {env.lexical with ml_yield = Some k}}) handler_ops ;
    handler_finally = option_map (fun v -> mk_closure0 v env) handler_finally ;
  } in
  Return (Handler h), env.state

let return_unit = return (Tuple [])

let rec top_fold f acc = function
  | [] -> top_return acc
  | x::rem -> top_bind (f acc x) (fun acc -> top_fold f acc rem)

let as_ml_module m ({lexical;_} as env) =
  let table = SymbolTable.push_ml_module lexical.table in
  let r, env = m { env with lexical = { lexical with table } } in
  r, { env with lexical = { lexical with table = SymbolTable.pop_ml_module env.lexical.table } }

let name_of v =
  match v with
    | Judgement abstr -> Nucleus.name_of_judgement abstr
    | Boundary abstr -> Nucleus.name_of_boundary abstr
    | Closure _ -> "a function"
    | Handler _ -> "a handler"
    | Tag _ -> "a data tag"
    | Tuple _ -> "a tuple"
    | Ref _ -> "a reference"
    | Dyn _ -> "a dynamic variable"
    | String _ -> "a string"

(** Coerce values *)

let as_not_abstract ~loc abstr =
  match Nucleus.as_not_abstract abstr with
  | Some x -> x
  | None -> error ~loc UnexpectedAbstraction

let as_abstract ~loc abstr =
  match Nucleus.as_abstract abstr with
  | Some x -> x
  | None -> error ~loc AbstractionExpected

let as_is_type ~loc = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementIsType t) -> t
     | Some Nucleus.(JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _)
     | None -> error ~loc (IsTypeExpected v)
     end
  | (Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (IsTypeExpected v)

let as_is_term ~loc = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementIsTerm e) -> e
     | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _)
     | None -> error ~loc (IsTermExpected v)
     end
  | (Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (IsTermExpected v)

let as_eq_type ~loc = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementEqType eq) -> eq
     | Some Nucleus.(JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _)
     | None -> error ~loc (EqTypeExpected v)
     end
  | (Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTypeExpected v)

let as_eq_term ~loc = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementEqTerm eq) -> eq
     | Some Nucleus.(JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _)
     | None -> error ~loc (EqTermExpected v)
     end
  | (Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTermExpected v)

let as_judgement ~loc = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some jdg -> jdg
     | None -> error ~loc (JudgementExpected v)
     end
  | (Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTermExpected v)

let as_is_type_abstraction ~loc v =
  match v with
  | Judgement abstr ->
     begin match Nucleus.as_is_type_abstraction abstr with
     | Some abstr -> abstr
     | None -> error ~loc AbstractionExpected
     end
  | Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _ ->
    error ~loc AbstractionExpected

let as_is_term_abstraction ~loc v =
  match v with
  | Judgement abstr ->
     begin match Nucleus.as_is_term_abstraction abstr with
     | Some abstr -> abstr
     | None -> error ~loc AbstractionExpected
     end
  | Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _ ->
    error ~loc AbstractionExpected

let as_eq_type_abstraction ~loc v =
  match v with
  | Judgement abstr ->
     begin match Nucleus.as_eq_type_abstraction abstr with
     | Some abstr -> abstr
     | None -> error ~loc AbstractionExpected
     end
  | Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _ ->
    error ~loc AbstractionExpected

let as_eq_term_abstraction ~loc v =
  match v with
  | Judgement abstr ->
     begin match Nucleus.as_eq_term_abstraction abstr with
     | Some abstr -> abstr
     | None -> error ~loc AbstractionExpected
     end
  | Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _ ->
    error ~loc AbstractionExpected

let as_judgement_abstraction ~loc v =
  match v with
  | Judgement abstr -> abstr
  | Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _ ->
    error ~loc AbstractionExpected

let as_boundary_abstraction ~loc v =
  match v with
  | Boundary abstr -> abstr
  | Judgement _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _ ->
    error ~loc AbstractionExpected

let as_closure ~loc = function
  | Closure f -> f
  | (Judgement _ | Boundary _ |
     Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (ClosureExpected v)

let as_handler ~loc = function
  | Handler h -> h
  | (Judgement _ | Boundary _ |
     Closure _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (HandlerExpected v)

let as_ref ~loc = function
  | Ref v -> v
  | (Judgement _ | Boundary _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Dyn _ | String _) as v ->
    error ~loc (RefExpected v)

let as_dyn ~loc = function
  | Dyn v -> v
  | (Judgement _ | Boundary _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~loc (DynExpected v)

let as_string ~loc = function
  | String v -> v
  | (Judgement _ | Boundary _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Dyn _ | Ref _) as v ->
    error ~loc (StringExpected v)

(** Operations *)

let operation op ?checking vs env =
  Operation (op, vs, checking, env.dynamic, mk_cont return env), env.state

(** Interact with the environment *)

let get_env env = Return env, env.state

let with_env env m {state; _} = m {env with state}

let top_get_env env = env, env

let get_signature env = env.dynamic.signature

let lookup_signature env =
  Return env.dynamic.signature, env.state

let add_rule rname rule env =
  let signature = Nucleus.Signature.add_rule rname rule env.dynamic.signature
  and penv =
    penv_forbid
    (match Ident.path rname with
     | Path.Direct (Path.Level (name, _)) -> name
     | Path.Module (_, Path.Level (name, _)) -> name
    ) env.lexical.penv in
  let env = { env
              with dynamic = { env.dynamic with signature }
                 ; lexical = { env.lexical with penv }
            } in
  (), env

let get_bound (Path.Index (_, k)) env = List.nth env.lexical.current_values k

let lookup_bound k env =
  let v = get_bound k env in
  Return v, env.state

let get_ml_value pth env = SymbolTable.get_ml_value pth env.lexical.table

let lookup_ml_value k env =
  Return (get_ml_value k env), env.state

let hypotheses env =
  let v = get_ml_value Desugar.Builtin.hypotheses env in
  let hyps = as_dyn ~loc:Location.unknown v in
  Return hyps, env.state

let get_dyn dyn env = Store.Dyn.lookup dyn env.dynamic.vars

let lookup_dyn dyn env =
  Return (get_dyn dyn env), env.state

let add_bound0 v env =
  { env with lexical = { env.lexical with
                         current_values = v :: env.lexical.current_values } }

let add_free x jt m env =
  let jy = Nucleus.fresh_atom x jt in
  let y_val = mk_judgement Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom jy))) in
  let env = add_bound0 y_val env in
  m jy env


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

let add_ml_value0 v env =
  { env with lexical = { env.lexical with table = SymbolTable.add_ml_value v env.lexical.table } }

let add_ml_value v ({lexical;_} as env) =
  let env = add_ml_value0 v env in
  (), env

let now0 x v env =
  { env with dynamic = { env.dynamic with vars = Store.Dyn.update x v env.dynamic.vars } }

let now x v m env =
  let env = now0 x v env in
  m env

let top_now x v env =
  let env = now0 x v env in
  (), env

let add_dynamic0 x v env =
  let y, vars = Store.Dyn.fresh v env.dynamic.vars in
  let env = add_ml_value0 (Dyn y) env in
  { env with dynamic = {env.dynamic with vars } }

let add_dynamic x v env = (), add_dynamic0 x v env

let add_ml_value_rec0 lst env =
  let r = ref env in
  let env =
    List.fold_left
      (fun env g ->
        let v = Closure (mk_closure_ref g r) in
        add_ml_value0 v env)
      env lst
  in
  r := env ;
  env

let add_ml_value_rec lst env =
  let env = add_ml_value_rec0 lst env in
  (), env

let continue v ({lexical={ml_yield;_};_} as env) =
  match ml_yield with
    | Some cont -> apply_cont cont v env
    | None -> assert false

(** Printers *)

(** Generate a printing environment from runtime environment *)
let get_penv env = env.lexical.penv

let get_nucleus_penv env =
  mk_nucleus_penv (get_penv env)

let lookup_penv env =
  Return (get_penv env), env.state

let top_lookup_penv env =
  get_penv env, env

let top_lookup_opens env =
  let penv = get_penv env in
  penv.opens, env

let top_open_path pth env =
  let env = { env with lexical = { env.lexical with penv = penv_open pth env.lexical.penv } } in
  (), env

let top_lookup_signature env =
  get_signature env, env

(* A hack, until we have proper type-driven printing routines. At that point we should consider
   equipping type definitions with custom printers, so that not only lists but other datatypes
   can have their own printers. (And we're not going to implement Haskell classes.) *)
(* let rec as_list_opt =
 *   let (_, tag_nil) = Desugar.Builtin.nil
 *   and (_, tag_cons) = Desugar.Builtin.cons in
 *   function
 *   | Tag (t, []) when equal_tag t tag_nil -> Some []
 *   | Tag (t, [x;xs]) when equal_tag t tag_cons ->
 *      begin
 *        match as_list_opt xs with
 *        | None -> None
 *        | Some xs -> Some (x :: xs)
 *      end
 *   | (IsTerm _ | IsType _ | EqTerm _ | EqType _ |
 *      Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) ->
 *      None *)

(** In the future this routine will be type-driven. One consequence is that
    constructor tags will be printed by looking up their names in type
    definitions. *)
let rec print_value ?max_level ~penv v ppf =
  match v with

  | Judgement jdg -> Nucleus.print_judgement_abstraction ~penv:(mk_nucleus_penv penv) ?max_level jdg ppf

  | Boundary bdry -> Nucleus.print_boundary_abstraction ~penv:(mk_nucleus_penv penv) ?max_level bdry ppf

  | Closure f -> Format.fprintf ppf "<function>"

  | Handler h -> Format.fprintf ppf "<handler>"

  | Tag (t, lst) ->
     print_tag ?max_level ~penv t lst ppf
     (* begin *)
     (*   match as_list_opt v with *)
     (*   | Some lst -> Format.fprintf ppf "@[<hov 1>[%t]@]" *)
     (*                   (Print.sequence (print_value ~max_level:Level.highest ~names) ";" lst) *)
     (*   | None ->  print_tag ?max_level ~names t lst ppf *)
     (* end *)

  | Tuple lst -> Format.fprintf ppf "@[<hov 1>(%t)@]"
                  (Print.sequence (print_value ~max_level:Level.highest ~penv) "," lst)

  | Ref v -> Print.print ?max_level ~at_level:Level.highest ppf "ref<%t>"
                  (Store.Ref.print_key v)

  | Dyn v -> Print.print ?max_level ~at_level:Level.highest ppf "dyn<%t>"
                  (Store.Dyn.print_key v)

  | String s -> Format.fprintf ppf "\"%s\"" s

and print_tag ?max_level ~penv t lst ppf =
  match Ident.path t, lst with

  | Path.Direct (Path.Level ({Name.fixity=Name.Prefix; name} as x,_)), [v] ->
     (* prefix tag applied to one argument *)
     (* Although it is reasonable to parse prefix operators as
        binding very tightly, it can be confusing to see
            f !! x instead of f (!! x).
        So we print out unary tags, at least, with the
        same parenthesization as application, i.e.,
        Level.app and Level.app_right instead of
        Level.prefix and Level.prefix_arg *)
     Print.print ppf ?max_level ~at_level:Level.prefix "%t@ %t"
                 (Name.print ~parentheses:false x)
                 (print_value ~max_level:Level.prefix_arg ~penv v)

  | Path.Direct (Path.Level ({Name.fixity=Name.Infix fixity;_} as x, _)), [v1; v2] ->
     (* infix tag applied to two arguments *)
     let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
     Print.print ppf ?max_level ~at_level:lvl_op "%t@ %t@ %t"
                 (print_value ~max_level:lvl_left ~penv v1)
                 (Name.print ~parentheses:false x)
                 (print_value ~max_level:lvl_right ~penv v2)

  | _ ->
     (* print as application *)
     begin
       match lst with
       | [] -> Ident.print ~opens:penv.opens ~parentheses:true t ppf
       | (_::_) -> Print.print ?max_level ~at_level:Level.ml_tag ppf "@[<hov 2>%t@ %t@]"
                     (Ident.print ~opens:penv.opens ~parentheses:true t)
                     (Print.sequence (print_value ~max_level:Level.ml_tag_arg ~penv) "" lst)
     end

let print_operation ~penv op vs ppf =
  match op, vs with

  | Path.Direct (Path.Level ({Name.fixity=Name.Prefix;_} as name, _)), [v] ->
     (* prefix op applied to one argument *)
     Print.print ppf ~at_level:Level.prefix "%t@ %t"
       (Name.print ~parentheses:false name)
       (print_value ~max_level:Level.prefix_arg ~penv v)

  | Path.Direct (Path.Level ({Name.fixity=Name.Infix fixity;_} as name, _)), [v1; v2] ->
     (* infix op applied to two arguments *)
     let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
     Print.print ppf ~at_level:lvl_op "%t@ %t@ %t"
       (print_value ~max_level:lvl_left ~penv v1)
       (Name.print ~parentheses:false name)
       (print_value ~max_level:lvl_right ~penv v2)

  | (Path.Direct _ | Path.Module _), _ ->
     (* print as application *)
     begin
       match vs with
       | [] -> Path.print ~opens:penv.opens ~parentheses:true op ppf
       | (_::_) -> Print.print ~at_level:Level.ml_operation ppf "@[<hov 2>%t@ %t@]"
                     (Path.print ~opens:penv.opens ~parentheses:true op)
                     (Print.sequence (print_value ~max_level:Level.ml_operation_arg ~penv) "" vs)
     end

let print_error ~penv err ppf =
  match err with

  | ExpectedAtom j ->
     Format.fprintf ppf "expected an atom but got@ %t"
       (Nucleus.print_is_term ~penv:(mk_nucleus_penv penv) j)

  | UnknownExternal s ->
     Format.fprintf ppf "unknown external@ %s" s

  | UnknownConfig s ->
    Format.fprintf ppf "unknown config@ %s" s

  | Inapplicable v ->
     Format.fprintf ppf "cannot apply@ %s" (name_of v)


  | AnnotationMismatch (t1, t2) ->
     let penv = mk_nucleus_penv penv in
     Format.fprintf ppf
       "the type annotation is@ %t@ but the surroundings imply it should be@ %t"
                    (Nucleus.print_is_type ~penv t1)
                    (Nucleus.print_is_type_abstraction ~penv t2)

  | TypeMismatchCheckingMode (jdg, bdry) ->
     let penv = mk_nucleus_penv penv in
     Format.fprintf ppf "the term@ %t@ is expected by its surroundings to have type@ %t"
                    (Nucleus.print_judgement_abstraction ~penv jdg)
                    (Nucleus.print_boundary_abstraction ~penv bdry)

  | UnexpectedAbstraction  ->
      Format.fprintf ppf "unexpected abstraction"

  | TermEqualityFail (e1, e2) ->
     let penv = mk_nucleus_penv penv in
     Format.fprintf ppf "failed to check that@ %t@ and@ %t@ are equal"
                    (Nucleus.print_is_term ~penv e1)
                    (Nucleus.print_is_term ~penv e2)

  | TypeEqualityFail (t1, t2) ->
     let penv = mk_nucleus_penv penv in
     Format.fprintf ppf "failed to check that@ %t@ and@ %t@ are equal"
                    (Nucleus.print_is_type ~penv t1)
                    (Nucleus.print_is_type ~penv t2)

  | UnannotatedAbstract x ->
     Format.fprintf ppf "cannot infer the type of@ %t@ in abstraction" (Name.print x)

  | MatchFail v ->
     Format.fprintf ppf "no matching pattern found for value@ %t"
                    (print_value ~penv v)

  | FailureFail v ->
     Format.fprintf ppf "expected to fail but computed@ %t"
                    (print_value ~penv v)

  | InvalidComparison ->
     Format.fprintf ppf "invalid comparison"

  | InvalidEqualTerm (e1, e2) ->
     let penv = mk_nucleus_penv penv in
     Format.fprintf ppf "this should be equality of terms@ %t@ and@ %t"
                    (Nucleus.print_is_term ~penv e1)
                    (Nucleus.print_is_term ~penv e2)

  | InvalidEqualType (t1, t2) ->
     let penv = mk_nucleus_penv penv in
     Format.fprintf ppf "this should be equality of types %t@ and@ %t"
                    (Nucleus.print_is_type ~penv t1)
                    (Nucleus.print_is_type ~penv t2)

  | BoolExpected v ->
     Format.fprintf ppf "expected a boolean but got %s" (name_of v)

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

  | AbstractionExpected ->
     Format.fprintf ppf "this should be an abstraction"

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

  | InvalidConvert (jdg, eq) ->
     let penv = mk_nucleus_penv penv in
     Format.fprintf ppf
       "cannot convert@ %t along@ %t"
       (Nucleus.print_judgement_abstraction ~penv jdg)
       (Nucleus.print_eq_type_abstraction ~penv eq)

  | InvalidCoerce (jdg, bdry) ->
     let penv = mk_nucleus_penv penv in
     Format.fprintf ppf "expected a judgement with boundary@ %t@ but got@ %t"
                    (Nucleus.print_boundary_abstraction ~penv bdry)
                    (Nucleus.print_judgement_abstraction ~penv jdg)

  | UnhandledOperation (op, vs) ->
     Format.fprintf ppf "unhandled operation %t"
                    (print_operation ~penv (Ident.path op) vs)

  | InvalidPatternMatch v ->
     Format.fprintf ppf "this pattern cannot match@ %t"
                    (print_value ~penv v)

  | InvalidHandlerMatch ->
     Format.fprintf ppf "wrong number of arguments in handler case"


let empty = {
  lexical = {
    table = SymbolTable.initial ;
    penv = { forbidden = Name.set_empty ; opens = Path.set_empty } ;
    current_values = [] ;
    ml_yield = None ;
  } ;
  dynamic = {
    signature = Nucleus.Signature.empty ;
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
         let f = (Ident.find op handler_ops) cont in
         (apply_closure f {args=vs;checking=jt}) env
       with
         Not_found ->
           Operation (op, vs, jt, dynamic, cont), env.state
     end
  end >>= fun v ->
  match handler_finally with
    | Some f -> apply_closure f v
    | None -> return v

let top_handle ~loc c env =
  let r = c env in
  match r with
    | Return v, state -> v, { env with state }
    | Operation (op, vs, _, _, _), _ ->
       error ~loc (UnhandledOperation (op, vs))

(** Equality *)
let rec equal_value v1 v2 =
  match v1, v2 with
    | Judgement jdg1, Judgement jdg2 ->
       Nucleus.alpha_equal_abstraction Nucleus.alpha_equal_judgement jdg1 jdg2

    | Boundary bdry1, Boundary bdry2 ->
       Nucleus.alpha_equal_abstraction Nucleus.alpha_equal_boundary bdry1 bdry2

    | Tag (t1, vs1), Tag (t2, vs2) ->
      equal_tag t1 t2 &&
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
    | Judgement _, (Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Boundary _, (Judgement _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Closure _, (Judgement _ | Boundary _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Handler _, (Judgement _ | Boundary _ | Closure _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Tag _, (Judgement _ | Boundary _ | Closure _ | Handler _ | Tuple _ | Ref _ | Dyn _ | String _)
    | Tuple _, (Judgement _ | Boundary _ | Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | String _)
    | String _, (Judgement _ | Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _)
    | Ref _, (Judgement _ | Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | String _ | Dyn _)
    | Dyn _, (Judgement _ | Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | String _ | Ref _) ->
       false

type topenv = env

let exec m env = m env


module Json =
struct

  let rec value v =
    match v with

    | Judgement jdg -> Json.tag "Judgement" [Nucleus.Json.judgement_abstraction jdg]

    | Boundary bdry -> Json.tag "Boundary" [Nucleus.Json.boundary_abstraction bdry]

    | Closure _ -> Json.tag "<fun>" []

    | Handler _ -> Json.tag "<handler>" []

    | Tag (t, lst) -> Json.tag "Tag" [Ident.Json.ident t; Json.List (List.map value lst)]

    | Tuple lst -> Json.tag "Tuple" [Json.List (List.map value lst)]

    | Ref r -> Json.tag "<ref>" []

    | Dyn r -> Json.tag "<dyn>" []

    | String s -> Json.tag "String" [Json.String s]

end
