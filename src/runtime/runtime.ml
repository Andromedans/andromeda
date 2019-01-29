(** Runtime values and computations *)

type ml_ref = Store.Ref.key
type ml_dyn = Store.Dyn.key

type coercible =
  | NotCoercible
  | Convertible of Nucleus.eq_type_abstraction
  | Coercible of Nucleus.is_term_abstraction

(** In the future we should be able to drop the name part *)
type ml_constructor = Path.level

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

  let add_ml_value info =
    at_current (fun mdl -> { mdl with ml_values = add info mdl.ml_values })

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



(** Run-time environment. *)
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

  (* names of inference rules (to avoid shadowing them) *)
  current_names : Name.t list;

  (* values to which de Bruijn indices are bound *)
  current_values : value list;

  (* current continuation if we're handling an operation *)
  ml_yield : value continuation option;
}

and state = value Store.Ref.t

and value =
  | IsTerm of Nucleus.is_term_abstraction
  | IsType of Nucleus.is_type_abstraction
  | EqTerm of Nucleus.eq_term_abstraction
  | EqType of Nucleus.eq_type_abstraction
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
  | Operation of Ident.t * value list * Nucleus.is_type_abstraction option * dynamic * 'a continuation

and 'a comp = env -> 'a result * state

and operation_args = { args : value list; checking : Nucleus.is_type_abstraction option }

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
  | TypeMismatchCheckingMode of Nucleus.is_term_abstraction * Nucleus.is_type_abstraction
  | UnexpectedAbstraction of Nucleus.is_type
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
  | IsTypeAbstractionExpected of value
  | IsTermAbstractionExpected of value
  | EqTypeAbstractionExpected of value
  | EqTermAbstractionExpected of value
  | AbstractionExpected of value
  | JudgementExpected of value
  | ClosureExpected of value
  | HandlerExpected of value
  | RefExpected of value
  | DynExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | InvalidConvertible of Nucleus.is_type_abstraction * Nucleus.is_type_abstraction * Nucleus.eq_type_abstraction
  | InvalidCoerce of Nucleus.is_type_abstraction * Nucleus.is_term_abstraction
  | UnhandledOperation of Ident.t * value list
  | InvalidPatternMatch of value
  | InvalidHandlerMatch

exception Error of error Location.located

let error ~loc err = raise (Error (Location.locate err loc))

let equal_tag (Path.Level (_, i)) (Path.Level (_, j)) = (i = j)

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
    handler_ops = Ident.map (fun f ->
      fun k -> mk_closure0 f {env with lexical = {env.lexical with ml_yield = Some k}}) handler_ops ;
    handler_finally = option_map (fun v -> mk_closure0 v env) handler_finally ;
  } in
  Return (Handler h), env.state

let return_unit = return (Tuple [])

let rec top_fold f acc = function
  | [] -> top_return acc
  | x::rem -> top_bind (f acc x) (fun acc ->
    top_fold f acc rem)

let as_ml_module m ({lexical;_} as env) =
  let table = SymbolTable.push_ml_module lexical.table in
  let r, env = m { env with lexical = { lexical with table } } in
  r, { env with lexical = { lexical with table = SymbolTable.pop_ml_module env.lexical.table } }


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

let as_is_type ~loc = function
  | IsType t as v ->
     begin match Nucleus.as_not_abstract t with
     | Some t -> t
     | None -> error ~loc (IsTermExpected v)
     end
  | (IsTerm _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (IsTypeExpected v)

let as_is_term ~loc = function
  | IsTerm e as v ->
     begin match Nucleus.as_not_abstract e with
     | Some e -> e
     | None -> error ~loc (IsTermExpected v)
     end
  | (IsType _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (IsTermExpected v)

let as_eq_type ~loc = function
  | EqType eq as v ->
     begin match Nucleus.as_not_abstract eq with
     | Some eq -> eq
     | None -> error ~loc (EqTypeExpected v)
     end
  | (IsType _ | IsTerm _ | EqTerm _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTypeExpected v)

let as_eq_term ~loc = function
  | EqTerm eq as v ->
     begin match Nucleus.as_not_abstract eq with
     | Some eq -> eq
     | None -> error ~loc (EqTermExpected v)
     end
  | (IsType _ | IsTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTermExpected v)

let as_is_type_abstraction ~loc = function
  | IsType t -> t
  | (IsTerm _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (IsTypeAbstractionExpected v)

let as_is_term_abstraction ~loc = function
  | IsTerm e -> e
  | (IsType _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (IsTermAbstractionExpected v)

let as_eq_type_abstraction ~loc = function
  | EqType eq -> eq
  | (IsType _ | IsTerm _ | EqTerm _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTypeAbstractionExpected v)

let as_eq_term_abstraction ~loc = function
  | EqTerm eq -> eq
  | (IsType _ | IsTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
    error ~loc (EqTermAbstractionExpected v)

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

let with_env env m {state; _} = m {env with state}

let top_get_env env = env, env

let get_signature env = env.dynamic.signature

let hypotheses env =
  failwith "get_hypotheses"

let lookup_signature env =
  Return env.dynamic.signature, env.state

let add_rule add_rule_to_signature rname rule env =
  let signature = add_rule_to_signature rname rule env.dynamic.signature
  and current_names = Ident.name rname :: env.lexical.current_names in
  let env = { env
              with dynamic = { env.dynamic with signature }
                 ; lexical = { env.lexical with current_names }
            } in
  (), env

let add_rule_is_type = add_rule Nucleus.Signature.add_rule_is_type
let add_rule_is_term = add_rule Nucleus.Signature.add_rule_is_term
let add_rule_eq_type = add_rule Nucleus.Signature.add_rule_eq_type
let add_rule_eq_term = add_rule Nucleus.Signature.add_rule_eq_term

let get_bound (Path.Index (_, k)) env = List.nth env.lexical.current_values k

let lookup_bound k env =
  let v = get_bound k env in
  Return v, env.state

let get_ml_value pth env = SymbolTable.get_ml_value pth env.lexical.table

let lookup_ml_value k env =
  Return (get_ml_value k env), env.state

let get_dyn dyn env = Store.Dyn.lookup dyn env.dynamic.vars

let lookup_dyn dyn env =
  Return (get_dyn dyn env), env.state

let add_bound0 v env =
  { env with lexical = { env.lexical with
                         current_values = v :: env.lexical.current_values } }

let add_free x jt m env =
  let jy = Nucleus.fresh_atom x jt in
  let y_val = mk_is_term (Nucleus.abstract_not_abstract (Nucleus.form_is_term_atom jy)) in
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

let add_ml_value v ({lexical;_} as env) =
  (),
  { env with lexical = { lexical with table = SymbolTable.add_ml_value v lexical.table } }

let now0 x v env =
  { env with dynamic = {env.dynamic with vars = Store.Dyn.update x v env.dynamic.vars } }

let now x v m env =
  let env = now0 x v env in
  m env

let top_now x v env =
  let env = now0 x v env in
  (), env

let add_dynamic0 x v env =
  let y,vars = Store.Dyn.fresh v env.dynamic.vars in
  { env with dynamic = {env.dynamic with vars };
             lexical = {env.lexical with
                        current_values = Dyn y :: env.lexical.current_values } }

let add_dynamic x v env = (), add_dynamic0 x v env

let add_ml_value_rec lst env =
  failwith "add_ml_value_rec is not implemented"
  (* let env = add_value_rec0 lst env in *)
  (* (), env *)

let continue v ({lexical={ml_yield;_};_} as env) =
  match ml_yield with
    | Some cont -> apply_cont cont v env
    | None -> assert false

(** Printers *)

(** Generate a printing environment from runtime environment *)
let get_names env = env.lexical.current_names

let lookup_names env =
  Return (get_names env), env.state

let top_lookup_names env =
  get_names env, env

let top_lookup_signature env =
  get_signature env, env

(* A hack, until we have proper type-driven printing routines. At that point we should consider
   equipping type definitions with custom printers, so that not only lists but other datatypes
   can have their own printers. (And we're not going to implement Haskell classes.) *)
let rec as_list_opt =
  let (_, tag_nil) = Desugar.Builtin.nil
  and (_, tag_cons) = Desugar.Builtin.cons in
  function
  | Tag (t, []) when equal_tag t tag_nil -> Some []
  | Tag (t, [x;xs]) when equal_tag t tag_cons ->
     begin
       match as_list_opt xs with
       | None -> None
       | Some xs -> Some (x :: xs)
     end
  | (IsTerm _ | IsType _ | EqTerm _ | EqType _ |
     Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) ->
     None

(** In the future this routine will be type-driven. One consequence is that
    constructor tags will be printed by looking up their names in type
    definitions. *)
let rec print_value ?max_level ~names v ppf =
  match v with

  | IsTerm e -> Nucleus.print_is_term_abstraction ~names ?max_level e ppf

  | IsType t -> Nucleus.print_is_type_abstraction ~names ?max_level t ppf

  | EqTerm eq -> Nucleus.print_eq_term_abstraction ~names ?max_level eq ppf

  | EqType eq -> Nucleus.print_eq_type_abstraction ~names ?max_level eq ppf

  | Closure f -> Format.fprintf ppf "<function>"

  | Handler h -> Format.fprintf ppf "<handler>"

  | Tag (t, lst) as v ->
     begin
       match as_list_opt v with
       | Some lst -> Format.fprintf ppf "@[<hov 1>[%t]@]"
                       (Print.sequence (print_value ~max_level:Level.highest ~names) ";" lst)
       | None ->  print_tag ?max_level ~names t lst ppf
     end

  | Tuple lst -> Format.fprintf ppf "@[<hov 1>(%t)@]"
                  (Print.sequence (print_value ~max_level:Level.highest ~names) "," lst)

  | Ref v -> Print.print ?max_level ~at_level:Level.highest ppf "ref<%t>"
                  (Store.Ref.print_key v)

  | Dyn v -> Print.print ?max_level ~at_level:Level.highest ppf "dyn<%t>"
                  (Store.Dyn.print_key v)

  | String s -> Format.fprintf ppf "\"%s\"" s

and print_tag ?max_level ~names t lst ppf =
  match t, lst with

  | Path.Level ({Name.fixity=Name.Prefix; name} as x,_), [v] ->
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
                 (print_value ~max_level:Level.prefix_arg ~names v)

  | Path.Level ({Name.fixity=Name.Infix fixity;_} as x, _), [v1; v2] ->
     (* infix tag applied to two arguments *)
     let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
     Print.print ppf ?max_level ~at_level:lvl_op "%t@ %t@ %t"
                 (print_value ~max_level:lvl_left ~names v1)
                 (Name.print ~parentheses:false x)
                 (print_value ~max_level:lvl_right ~names v2)

  | _ ->
     (* print as application *)
     begin
       let (Path.Level (x, _)) = t in
       match lst with
       | [] -> Name.print x ppf
       | (_::_) -> Print.print ?max_level ~at_level:Level.ml_tag ppf "@[<hov 2>%t@ %t@]"
                     (Name.print x)
                     (Print.sequence (print_value ~max_level:Level.ml_tag_arg ~names) "" lst)
     end

let print_operation ~names op vs ppf =
  match op, vs with

  | {Name.fixity=Name.Prefix;_}, [v] ->
     (* prefix op applied to one argument *)
     Print.print ppf ~at_level:Level.prefix "%t@ %t"
       (Name.print ~parentheses:false op)
       (print_value ~max_level:Level.prefix_arg ~names v)

  | {Name.fixity=Name.Infix fixity;_}, [v1; v2] ->
     (* infix op applied to two arguments *)
     let (lvl_op, lvl_left, lvl_right) = Level.infix fixity in
     Print.print ppf ~at_level:lvl_op "%t@ %t@ %t"
       (print_value ~max_level:lvl_left ~names v1)
       (Name.print ~parentheses:false op)
       (print_value ~max_level:lvl_right ~names v2)

  | _ ->
     (* print as application *)
     begin
       match vs with
       | [] -> Name.print op ppf
       | (_::_) -> Print.print ~at_level:Level.ml_operation ppf "[@<hov 2>%t@ %t@]"
                     (Name.print op)
                     (Print.sequence (print_value ~max_level:Level.ml_operation_arg ~names) "" vs)
     end

let print_error ~names err ppf =
  match err with

  | ExpectedAtom j ->
     Format.fprintf ppf "expected an atom but got@ %t"
       (Nucleus.print_is_term ~names j)

  | UnknownExternal s ->
     Format.fprintf ppf "unknown external@ %s" s

  | UnknownConfig s ->
    Format.fprintf ppf "unknown config@ %s" s

  | Inapplicable v ->
     Format.fprintf ppf "cannot apply@ %s" (name_of v)


  | AnnotationMismatch (t1, t2) ->
      Format.fprintf ppf
      "the type annotation is@ %t@ but the surroundings imply it should be@ %t"
                    (Nucleus.print_is_type ~names t1)
                    (Nucleus.print_is_type_abstraction ~names t2)

  | TypeMismatchCheckingMode (v, t) ->
      Format.fprintf ppf "the term@ %t@ is expected by its surroundings to have type@ %t"
                    (Nucleus.print_is_term_abstraction ~names v)
                    (Nucleus.print_is_type_abstraction ~names t)

  | UnexpectedAbstraction t ->
      Format.fprintf ppf "this term is an abstraction but the surroundings imply it shoule be@ %t"
                    (Nucleus.print_is_type ~names t)

  | TermEqualityFail (e1, e2) ->
     Format.fprintf ppf "failed to check that@ %t@ and@ %t@ are equal"
                    (Nucleus.print_is_term ~names e1)
                    (Nucleus.print_is_term ~names e2)

  | TypeEqualityFail (t1, t2) ->
     Format.fprintf ppf "failed to check that@ %t@ and@ %t@ are equal"
                    (Nucleus.print_is_type ~names t1)
                    (Nucleus.print_is_type ~names t2)

  | UnannotatedAbstract x ->
     Format.fprintf ppf "cannot infer the type of@ %t@ in abstraction" (Name.print x)

  | MatchFail v ->
     Format.fprintf ppf "no matching pattern found for value@ %t"
                    (print_value ~names v)

  | FailureFail v ->
     Format.fprintf ppf "expected to fail but computed@ %t"
                    (print_value ~names v)

  | InvalidComparison ->
     Format.fprintf ppf "invalid comparison"

  | InvalidEqualTerm (e1, e2) ->
     Format.fprintf ppf "this should be equality of terms@ %t@ and@ %t"
                    (Nucleus.print_is_term ~names e1)
                    (Nucleus.print_is_term ~names e2)

  | InvalidEqualType (t1, t2) ->
     Format.fprintf ppf "this should be equality of types %t@ and@ %t"
                    (Nucleus.print_is_type ~names t1)
                    (Nucleus.print_is_type ~names t2)

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

  | IsTypeAbstractionExpected v ->
     Format.fprintf ppf "expected a possibly abstracted type but got %s" (name_of v)

  | IsTermAbstractionExpected v ->
     Format.fprintf ppf "expected a possibly abstracted term but got %s" (name_of v)

  | EqTypeAbstractionExpected v ->
     Format.fprintf ppf "expected a possibly abstracted type equality but got %s" (name_of v)

  | EqTermAbstractionExpected v ->
     Format.fprintf ppf "expected a possibly abstracted term equality but got %s" (name_of v)

  | AbstractionExpected v ->
     Format.fprintf ppf "expected an abstraction but got %s" (name_of v)

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
     Format.fprintf ppf
       "expected an equality between@ %t@ and@ %t@ but got@ %t"
                    (Nucleus.print_is_type_abstraction ~names t1)
                    (Nucleus.print_is_type_abstraction ~names t2)
                    (Nucleus.print_eq_type_abstraction ~names eq)

  | InvalidCoerce (t, e) ->
     Format.fprintf ppf "expected a term of type@ %t@ but got@ %t"
                    (Nucleus.print_is_type_abstraction ~names t)
                    (Nucleus.print_is_term_abstraction ~names e)

  | UnhandledOperation (op, vs) ->
     Format.fprintf ppf "unhandled operation %t"
                    (print_operation ~names (Ident.name op) vs)

  | InvalidPatternMatch v ->
     Format.fprintf ppf "this pattern cannot match@ %t"
                    (print_value ~names v)

  | InvalidHandlerMatch ->
     Format.fprintf ppf "wrong number of arguments in handler case"


let empty = {
  lexical = {
    table = SymbolTable.initial ;
    current_names = [] ;
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
    | Return v, state -> v, env
    | Operation (op, vs, _, _, _), _ ->
       error ~loc (UnhandledOperation (op, vs))

(** Equality *)
let rec equal_value v1 v2 =
  match v1, v2 with
    | IsTerm e1, IsTerm e2 ->
      Nucleus.alpha_equal_abstraction Nucleus.alpha_equal_term e1 e2

    | IsType t1, IsType t2 ->
      Nucleus.alpha_equal_abstraction Nucleus.alpha_equal_type t1 t2

    | EqTerm eq1, EqTerm eq2 ->
       (* XXX: should we even compare equality judgements for equality? That will lead to comparison of contexts. *)
       eq1 == eq2

    | EqType eq1, EqType eq2 ->
       (* XXX: should we even compare equality judgements for equality? That will lead to comparison of contexts. *)
       eq1 == eq2

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

let exec m env = m env


module Json =
struct

  let rec value v =
    match v with

    | IsTerm e -> Json.tag "IsTerm" [Nucleus.Json.abstraction Nucleus.Json.is_term e]

    | IsType t -> Json.tag "IsType" [Nucleus.Json.abstraction Nucleus.Json.is_type t]

    | EqType eq -> Json.tag "EqType" [Nucleus.Json.abstraction Nucleus.Json.eq_type eq]

    | EqTerm eq -> Json.tag "EqTerm" [Nucleus.Json.abstraction Nucleus.Json.eq_term eq]

    | Closure _ -> Json.tag "<fun>" []

    | Handler _ -> Json.tag "<handler>" []

    | Tag (Path.Level (c, _), lst) -> Json.tag "Tag" [Name.Json.name c; Json.List (List.map value lst)]

    | Tuple lst -> Json.tag "Tuple" [Json.List (List.map value lst)]

    | Ref r -> Json.tag "<ref>" []

    | Dyn r -> Json.tag "<dyn>" []

    | String s -> Json.tag "String" [Json.String s]

end
