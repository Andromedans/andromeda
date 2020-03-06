(** Runtime values and computations *)

(** In the future we should be able to drop the path and just use an ID, or even an integer. *)
type ml_constructor = Ident.t

(** This module defines 2 monads:
    - the computation monad [comp], providing operations and an environment of which part
      is dynamically scoped.Primitives are like [add_value].
    - the toplevel monad [toplevel], a standard state monad with restricted accessors.
      Primitives are like [top_add_value].
      Some modifications of the environment may only be done at the top level, for
      instance declaring constants.

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
                       let compare = Stdlib.compare
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
  opens : Path.set;
  signature : Nucleus.signature
}

let penv_forbid x penv =
  { penv with forbidden = Name.set_add x penv.forbidden }

let penv_open pth penv =
  { penv with opens = Path.set_add pth penv.opens }

let mk_nucleus_penv {forbidden;opens;_} =
  { Nucleus.forbidden = forbidden ;
    Nucleus.opens = opens ;
    Nucleus.debruijn_var = [] ;
    Nucleus.debruijn_meta = [] }

(** Runtime environment. *)
type env = {
  dynamic : dynamic;
  lexical : lexical
}

and dynamic = {
  (* Current printing environment *)
  penv : penv;
}

and lexical = {
  (* lookup table for globally defined values *)
  table : value SymbolTable.t ;

  (* values to which de Bruijn indices are bound *)
  current_values : value list;
}

and value =
  | Judgement of Nucleus.judgement_abstraction
  | Boundary of Nucleus.boundary_abstraction
  | Derivation of Nucleus.derivation
  | External of external_value
  | Closure of (value, value) closure
  | Handler of handler
  | Exc of exc
  | Tag of ml_constructor * value list
  | Tuple of value list
  | Ref of value ref
  | String of string

and exc = Ident.t * value option

and external_value =
  | EqualityChecker of Eqchk.checker

(* It's important not to confuse the closure and the underlying ocaml function *)
and ('a, 'b) closure = Clos of ('a -> 'b comp)

and 'a result =
  | Return of 'a
  | Exception of exc
  | Operation of { op_id : Ident.t
                 ; op_args : value list
                 ; op_boundary : Nucleus.boundary_abstraction option
                 ; op_dynamic_env : dynamic
                 ; op_cont : 'a continuation }

and 'a comp = env -> 'a result

and operation_args = { args : value list; checking : Nucleus.boundary_abstraction option }

and handler = {
  handler_val : (value, value) closure option ;
  handler_ops : (operation_args, value) closure Ident.map ;
  handler_exc : (exc, value) closure
}

and 'a continuation =
  { cont_val : (value, 'a) closure
  ; cont_exc : (exc, 'a) closure }

type topenv = {
  top_runtime : env ;
  top_handler : (operation_args, value) closure Ident.map ;
}

type 'a toplevel = topenv -> 'a * topenv

(** Error reporting *)
type error =
  | TooFewArguments
  | TooManyArguments
  | ExpectedAtom of Nucleus.is_term
  | UnknownExternal of string
  | UnknownConfig of string
  | Inapplicable of value
  | TypeMismatchCheckingMode of Nucleus.judgement_abstraction * Nucleus.boundary_abstraction
  | UnexpectedAbstraction
  | TermEqualityFail of Nucleus.is_term * Nucleus.is_term
  | TypeEqualityFail of Nucleus.is_type * Nucleus.is_type
  | UnannotatedAbstract of Name.t
  | MetaWithoutBoundary of Name.t option
  | MatchFail of value
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
  | IsTypeAbstractionExpected of value
  | IsTermAbstractionExpected of value
  | EqTypeAbstractionExpected of value
  | EqTermAbstractionExpected of value
  | BoundaryAbstractionExpected of value
  | JudgementAbstractionExpected of value
  | JudgementExpected of value
  | JudgementOrBoundaryExpected of value
  | EqualityCheckerExpected of value
  | DerivationExpected of value
  | ClosureExpected of value
  | HandlerExpected of value
  | RefExpected of value
  | ExceptionExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | InvalidConvert of Nucleus.judgement_abstraction * Nucleus.eq_type_abstraction
  | InvalidCoerce of Nucleus.judgement_abstraction * Nucleus.boundary_abstraction
  | UnhandledOperation of Ident.t * value list
  | UncaughtException of Ident.t * value option
  | InvalidPatternMatch of value

exception Error of error Location.located

let error ~at err = raise (Error (Location.mark ~at err))

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

let mk_closure_external f = Closure (Clos f)

let apply_closure (Clos f) v env = f v env

let rec bind_cont (r : value comp) ({cont_val=f_val; cont_exc=f_exc} as cont) : 'a comp =
  fun env ->
  match r env with
  | Return v -> apply_closure f_val v env

  | Exception exc -> apply_closure f_exc exc env

  | Operation ({op_cont={cont_val=g_val; cont_exc=g_exc};_} as op_data) ->
     let op_cont = { cont_val = mk_closure0 (fun v -> bind_cont (apply_closure g_val v) cont) env ;
                     cont_exc = mk_closure0 (fun exc -> bind_cont (apply_closure g_exc exc) cont) env }
     in
     Operation {op_data with op_cont}

(** References *)
let mk_ref v _env =
  let x = ref v in
  Return (Ref x)

let lookup_ref x _env =
  let v = !x in
  Return v

let update_ref x v env =
  x := v ;
  Return ()

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind r f env =
  match r env with
  | Return v -> (f v env : 'b result)

  | Exception _ as r -> r

  | Operation ({op_cont={cont_val=g_val; cont_exc=g_exc};_} as op_data) ->
     let op_cont = { cont_val = mk_closure0 (fun v -> bind (apply_closure g_val v) f) env ;
                     cont_exc = mk_closure0 (fun exc -> bind (apply_closure g_exc exc) f) env }
     in
     Operation {op_data with op_cont}

let top_bind m f topenv =
  let x, topenv = m topenv in
  f x topenv

(** Returns *)
let top_return x topenv = x, topenv

let top_return_closure f topenv = mk_closure0 f topenv.top_runtime, topenv

let return x _env = Return x

let raise_exception exc _env = Exception exc

let return_judgement jdg = return (Judgement jdg)

let return_boundary bdry = return (Boundary bdry)

let return_closure f env = Return (Closure (mk_closure0 f env))

let return_handler handler_val handler_ops handler_exc env =
  let option_map g = function None -> None | Some x -> Some (g x) in
  let h = {
    handler_val = option_map (fun v -> mk_closure0 v env) handler_val ;
    handler_ops = Ident.map (fun f -> mk_closure0 f env) handler_ops ;
    handler_exc = mk_closure0 handler_exc env
  } in
  Return (Handler h)

let return_unit = return (Tuple [])

let rec top_fold f acc = function
  | [] -> top_return acc
  | x::rem -> top_bind (f acc x) (fun acc -> top_fold f acc rem)

let top_as_ml_module (m : unit toplevel) ({top_runtime=({lexical;_} as env);_} as topenv) =
  (* push a new module onto the stack of currently evaluating modules *)
  let table = SymbolTable.push_ml_module lexical.table in
  (* Whatever gets defined by [m] goes to the newly started module *)
  let r, topenv = m { topenv with top_runtime = { env with lexical = { lexical with table } } } in
  (* seal the newly created module *)
  let table = SymbolTable.pop_ml_module topenv.top_runtime.lexical.table in
  (* continue in the updated module *)
  r, { topenv with top_runtime = { topenv.top_runtime with lexical = { lexical with table }} }

let name_of_external = function
  | EqualityChecker _ -> "equality checker"

let name_of v =
  match v with
    | Judgement abstr -> Nucleus.name_of_judgement abstr
    | Boundary abstr -> Nucleus.name_of_boundary abstr
    | Derivation _ -> "a derivation"
    | Closure _ -> "a function"
    | Handler _ -> "a handler"
    | Exc _ -> "an exception"
    | Tag _ -> "an ML constructor"
    | Tuple _ -> "a tuple"
    | Ref _ -> "a reference"
    | String _ -> "a string"
    | External v -> name_of_external v

(** Coerce values *)

let as_equality_checker ~at = function
  | External (EqualityChecker chk) -> chk

  | (Judgement _ | Boundary _ | Derivation _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (EqualityCheckerExpected v)

let as_derivation ~at = function
  | Derivation drv -> drv

  | (Judgement _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (DerivationExpected v)

let as_not_abstract ~at abstr =
  match Nucleus.as_not_abstract abstr with
  | Some x -> x
  | None -> error ~at UnexpectedAbstraction

let as_is_type ~at = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementIsType t) -> t
     | Some Nucleus.(JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _)
     | None -> error ~at (IsTypeExpected v)
     end
  | (Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (IsTypeExpected v)

let as_is_term ~at = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementIsTerm e) -> e
     | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _)
     | None -> error ~at (IsTermExpected v)
     end
  | (Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (IsTermExpected v)

let as_eq_type ~at = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementEqType eq) -> eq
     | Some Nucleus.(JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _)
     | None -> error ~at (EqTypeExpected v)
     end
  | (Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (EqTypeExpected v)

let as_eq_term ~at = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementEqTerm eq) -> eq
     | Some Nucleus.(JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _)
     | None -> error ~at (EqTermExpected v)
     end
  | (Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (EqTermExpected v)

let as_judgement ~at = function
  | Judgement abstr as v ->
     begin match Nucleus.as_not_abstract abstr with
     | Some jdg -> jdg
     | None -> error ~at (JudgementExpected v)
     end
  | (Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (EqTermExpected v)

let as_is_type_abstraction ~at v =
  match v with
  | Judgement abstr ->
     begin match Nucleus.as_is_type_abstraction abstr with
     | Some abstr -> abstr
     | None -> error ~at (IsTypeAbstractionExpected v)
     end
  | Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _ ->
    error ~at (IsTypeAbstractionExpected v)

let as_is_term_abstraction ~at v =
  match v with
  | Judgement abstr ->
     begin match Nucleus.as_is_term_abstraction abstr with
     | Some abstr -> abstr
     | None -> error ~at (IsTermAbstractionExpected v)
     end
  | Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _ ->
    error ~at (IsTermAbstractionExpected v)

let as_eq_type_abstraction ~at v =
  match v with
  | Judgement abstr ->
     begin match Nucleus.as_eq_type_abstraction abstr with
     | Some abstr -> abstr
     | None -> error ~at (EqTypeAbstractionExpected v)
     end
  | Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _ ->
    error ~at (EqTypeAbstractionExpected v)

let as_eq_term_abstraction ~at v =
  match v with
  | Judgement abstr ->
     begin match Nucleus.as_eq_term_abstraction abstr with
     | Some abstr -> abstr
     | None -> error ~at (EqTermAbstractionExpected v)
     end
  | Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _ ->
    error ~at (EqTermAbstractionExpected v)

let as_judgement_abstraction ~at v =
  match v with
  | Judgement abstr -> abstr
  | Derivation _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _ ->
    error ~at (JudgementAbstractionExpected v)

let as_boundary_abstraction ~at v =
  match v with
  | Boundary abstr -> abstr
  | Derivation _ | Judgement _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _ ->
    error ~at (BoundaryAbstractionExpected v)

let as_closure ~at = function
  | Closure f -> f
  | (Judgement _ | Boundary _ | Derivation _ | External _ |
     Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (ClosureExpected v)

let as_handler ~at = function
  | Handler h -> h
  | (Judgement _ | Boundary _ | Derivation _ | External _ |
     Closure _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
    error ~at (HandlerExpected v)

let as_exception ~at = function
  | Exc (exc, vopt) -> (exc, vopt)
  | (Judgement _ | Boundary _ | Derivation _ | External _ |
     Closure _ | Handler _ | Ref _ | Tag _ | Tuple _ | String _) as v ->
    error ~at (ExceptionExpected v)

let as_ref ~at = function
  | Ref v -> v
  | (Judgement _ | Boundary _ | Derivation _ | External _ |
     Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | String _) as v ->
    error ~at (RefExpected v)

let as_string ~at = function
  | String v -> v
  | (Judgement _ | Boundary _ | Derivation _ | External _ |
     Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _) as v ->
    error ~at (StringExpected v)

let as_bool ~at v =
  let (tag_true, _, _) = Typecheck.Builtin.mltrue
  and (tag_false, _, _) = Typecheck.Builtin.mlfalse in
  match v with
  | Tag (t, []) when equal_tag t tag_true -> true
  | Tag (t, []) when equal_tag t tag_false -> false
  | (Judgement _ | Boundary _ | Derivation _ | External _ |
     Closure _ | Handler _ | Exc _ | Tag _ | String _ | Tuple _ | Ref _) as v ->
    error ~at (BoolExpected v)

(** Operations *)

(** Generic operation *)
let operation op_id ?checking vs env =
  Operation {
    op_id ;
    op_args = vs ;
    op_boundary = checking ;
    op_dynamic_env = env.dynamic ;
    op_cont = {cont_val = mk_closure0 return env ; cont_exc = mk_closure0 raise_exception env }
  }

(** Interact with the environment *)

let get_env env = Return env

let with_env env m _env' = m env

let top_get_env topenv = topenv.top_runtime, topenv

let get_signature env = env.dynamic.penv.signature

let lookup_signature env =
  Return env.dynamic.penv.signature

let top_add_rule rname rule ({top_runtime=env;_} as topenv) =
  let signature = Nucleus.Signature.add_rule rname rule env.dynamic.penv.signature
  and penv =
    penv_forbid
    (match Ident.path rname with
     | Path.Direct (Path.Level (name, _)) -> name
     | Path.Module (_, Path.Level (name, _)) -> name
    ) env.dynamic.penv in
  let env = { env with dynamic = {penv = {penv with signature = signature}} } in
  (), {topenv with top_runtime=env}

let get_bound (Path.Index (_, k)) env = List.nth env.lexical.current_values k

let lookup_bound k env =
  let v = get_bound k env in
  Return v

let get_ml_value pth env = SymbolTable.get_ml_value pth env.lexical.table

let lookup_ml_value k env =
  Return (get_ml_value k env)

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

let top_add_ml_value v ({top_runtime=({lexical;_} as env);_} as topenv) =
  let env = add_ml_value0 v env in
  (), {topenv with top_runtime=env}

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

let top_add_ml_value_rec lst ({top_runtime=env;_} as topenv) =
  let env = add_ml_value_rec0 lst env in
  (), {topenv with top_runtime=env}

(** Printers *)

(** Generate a printing environment from runtime environment *)

let get_penv env = env.dynamic.penv

let top_get_penv {top_runtime;_} = get_penv top_runtime

let top_get_nucleus_penv {top_runtime;_} =
  mk_nucleus_penv (get_penv top_runtime)

let lookup_penv env =
  Return (get_penv env)

let lookup_nucleus_penv env =
  let penv = mk_nucleus_penv (get_penv env) in
  Return penv

let top_lookup_penv topenv =
  top_get_penv topenv, topenv

let top_lookup_opens topenv =
  let penv = top_get_penv topenv in
  penv.opens, topenv

let top_open_path pth ({top_runtime;_} as topenv) =
  let top_runtime =
    { top_runtime with
      dynamic = {
        penv = penv_open pth top_runtime.dynamic.penv } }
  in
  (), { topenv with top_runtime }

let top_lookup_signature topenv =
  get_signature topenv.top_runtime, topenv

let print_external ?max_level ~penv v ppf =
  match v with
  | EqualityChecker _ -> Format.fprintf ppf "<checker>"

(** In the future this routine will be type-driven. One consequence is that
    constructor tags will be printed by looking up their names in type
    definitions. *)
let rec print_value ?max_level ~penv v ppf =
  match v with

  | Judgement jdg ->
     let abstr = Nucleus.abstracted_judgement_with_boundary penv.signature jdg in
     Nucleus.print_judgement_with_boundary_abstraction ~penv:(mk_nucleus_penv penv) ?max_level abstr ppf

  | Boundary bdry -> Nucleus.print_boundary_abstraction ~penv:(mk_nucleus_penv penv) ?max_level bdry ppf

  | Derivation drv -> Nucleus.print_derivation ~penv:(mk_nucleus_penv penv) ?max_level drv ppf

  | External v -> print_external ?max_level ~penv v ppf

  | Closure f -> Format.fprintf ppf "<function>"

  | Handler h -> Format.fprintf ppf "<handler>"

  | Exc (exc, vopt) ->
     print_exception ?max_level ~penv (Ident.path exc) vopt ppf

  | Tag (t, lst) ->
     print_tag ?max_level ~penv t lst ppf
     (* begin *)
     (*   match as_list_opt v with *)
     (*   | Some lst -> Format.fprintf ppf "@[<hov 1>[%t]@]" *)
     (*                   (Print.sequence (print_value ~max_level:Level.highest ~names) ";" lst) *)
     (*   | None ->  print_tag ?max_level ~names t lst ppf *)
     (* end *)

  | Tuple lst -> Print.print ?max_level ~at_level:Level.ml_tuple ppf "@[<hov 1>(%t)@]"
                  (Print.sequence (print_value ~max_level:Level.ml_tuple_arg ~penv) "," lst)

  | Ref x -> Print.print ?max_level ~at_level:Level.highest ppf "ref@ %t"
                  (print_value ~max_level:Level.ml_tag ~penv (!x))

  | String s -> Format.fprintf ppf "\"%s\"" s

and print_exception ?max_level ~penv exc vopt ppf =
  match exc, vopt with

  | Path.Direct (Path.Level ({Name.fixity=Name.Prefix;_} as name, _)), Some v ->
     (* prefix exception applied to one argument *)
     Print.print ppf ?max_level ~at_level:Level.prefix "%t@ %t"
       (Name.print ~parentheses:false name)
       (print_value ~max_level:Level.prefix_arg ~penv v)

  | (Path.Direct _ | Path.Module _), None ->
     (* print as identifier *)
     Path.print ~opens:penv.opens ~parentheses:true exc ppf

  | (Path.Direct _ | Path.Module _), Some v ->
     (* print as application *)
     Print.print ?max_level ~at_level:Level.ml_operation ppf "%t@ %t"
                     (Path.print ~opens:penv.opens ~parentheses:true exc)
                     (print_value ~max_level:Level.ml_operation_arg ~penv v)

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

  | TooFewArguments ->
     Format.fprintf ppf "too few arguments"

  | TooManyArguments ->
     Format.fprintf ppf "too many arguments"

  | ExpectedAtom j ->
     Format.fprintf ppf "expected an atom but got@ %t"
       (Nucleus.print_is_term ~penv:(mk_nucleus_penv penv) j)

  | UnknownExternal s ->
     Format.fprintf ppf "unknown external@ %s" s

  | UnknownConfig s ->
    Format.fprintf ppf "unknown config@ %s" s

  | Inapplicable v ->
     Format.fprintf ppf "cannot apply@ %s" (name_of v)

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

  | MetaWithoutBoundary (Some x) ->
     Format.fprintf ppf "meta-variable %t appears without a boundary"
                    (Name.print x)

  | MetaWithoutBoundary None ->
     Format.fprintf ppf "this meta-variable appears without a boundary"

  | MatchFail v ->
     Format.fprintf ppf "no matching pattern found for value@ %t"
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
     Format.fprintf ppf "expected an abstraction"

  | JudgementAbstractionExpected v ->
     Format.fprintf ppf "expected an abstracted judgement but got %s" (name_of v)

  | BoundaryAbstractionExpected v ->
     Format.fprintf ppf "expected an abstracted boundary but got %s" (name_of v)

  | IsTypeAbstractionExpected v ->
     Format.fprintf ppf "expected a type abstraction but got %s" (name_of v)

  | IsTermAbstractionExpected v ->
     Format.fprintf ppf "expected a term abstraction but got %s" (name_of v)

  | EqTypeAbstractionExpected v ->
     Format.fprintf ppf "expected a type abstraction equality but got %s" (name_of v)

  | EqTermAbstractionExpected v ->
     Format.fprintf ppf "expected a term abstraction equality but got %s" (name_of v)

  | JudgementExpected v ->
     Format.fprintf ppf "expected a judgement but got %s" (name_of v)

  | JudgementOrBoundaryExpected v ->
     Format.fprintf ppf "expected a judgement or a boundary but got %s" (name_of v)

  | DerivationExpected v ->
     Format.fprintf ppf "expected a derivation but got %s" (name_of v)

  | EqualityCheckerExpected v ->
     Format.fprintf ppf "expected an equality checker but got %s" (name_of v)

  | ClosureExpected v ->
     Format.fprintf ppf "expected a function but got %s" (name_of v)

  | HandlerExpected v ->
     Format.fprintf ppf "expected a handler but got %s" (name_of v)

  | RefExpected v ->
     Format.fprintf ppf "expected a reference but got %s" (name_of v)

  | ExceptionExpected v ->
     Format.fprintf ppf "expected an exception but got %s" (name_of v)

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

  | UncaughtException (exc, vopt) ->
     Format.fprintf ppf "uncaught exception %t"
                    (print_exception ~penv (Ident.path exc) vopt)

  | InvalidPatternMatch v ->
     Format.fprintf ppf "this pattern cannot match@ %t"
                    (print_value ~penv v)

let empty_env = {
  lexical = {
    table = SymbolTable.initial ;
    current_values = [] ;
  } ;
  dynamic = {
    penv = { forbidden = Name.set_empty ; opens = Path.set_empty; signature = Nucleus.Signature.empty } ;
  }
}

let empty = {
  top_runtime = empty_env ;
  top_handler = Ident.empty
}

(** Handling *)
let rec handle_comp {handler_val; handler_ops; handler_exc} (r : value comp) : value comp =
  fun env -> match r env with

  | Return v ->
     begin match handler_val with
     | Some f -> apply_closure f v env
     | None -> Return v
     end

  | Exception exc ->
     apply_closure handler_exc exc env

  | Operation {op_id; op_args; op_boundary; op_dynamic_env; op_cont={cont_val; cont_exc}} ->
     let h = {handler_val; handler_ops; handler_exc} in
     let op_cont = { cont_val = mk_closure0 (fun v -> handle_comp h (apply_closure cont_val v)) env ;
                     cont_exc = mk_closure0 (fun exc -> handle_comp h (apply_closure cont_exc exc)) env }
     in
     begin
       match Ident.find_opt op_id handler_ops with
       | Some f_op ->
         let r = apply_closure f_op {args=op_args; checking=op_boundary} in
         bind_cont r op_cont env
       | None ->
          Operation {op_id; op_args; op_boundary; op_dynamic_env; op_cont}
     end

let top_add_handle ~at op_id op_case ({top_handler; top_runtime} as topenv) =
  let f_op =
    match Ident.find_opt op_id top_handler with
    | None ->
       (* the default handler just reports an unhandled operation (with the wrong location...) *)
       mk_closure0 (fun {args;_} _env -> error ~at (UnhandledOperation (op_id, args))) top_runtime
    | Some f_op -> f_op
  in
  let f_op = mk_closure0 (op_case (apply_closure f_op)) top_runtime in
  let top_handler = Ident.add op_id f_op top_handler in
  (), { topenv with top_handler }


let top_handle ~at c ({top_handler=hnd; top_runtime=env} as topenv) =
  let rec handle = function

    | Return v -> v, { topenv with top_runtime=env }

    | Exception (exc_id, v) ->
       error ~at (UncaughtException (exc_id, v))

    | Operation {op_id; op_args; op_boundary; op_dynamic_env; op_cont} ->
       begin match Ident.find_opt op_id hnd with

       | Some f_op ->
         let env' = {env with dynamic = op_dynamic_env} in
         let r = apply_closure f_op {args=op_args; checking=op_boundary} in
         handle (bind_cont r op_cont env')

       | None ->
          error ~at (UnhandledOperation (op_id, op_args))
       end
  in
  let r = c topenv.top_runtime in
  handle r

(** Equality *)

let equal_external_value v1 v2 =
  v1 == v2 ||
  match v1, v2 with
  | EqualityChecker c1, EqualityChecker c2 -> (c1 == c2)


let rec equal_value v1 v2 =
  v1 == v2 ||
  match v1, v2 with
    | Judgement jdg1, Judgement jdg2 ->
       Nucleus.alpha_equal_abstraction Nucleus.alpha_equal_judgement jdg1 jdg2

    | Boundary bdry1, Boundary bdry2 ->
       Nucleus.alpha_equal_abstraction Nucleus.alpha_equal_boundary bdry1 bdry2

    | Exc (exc1, v1opt), Exc (exc2, v2opt) ->
       Ident.equal exc1 exc2 &&
         (match v1opt, v2opt with
          | None, None -> true
          | Some v1, Some v2 -> equal_value v1 v2
          | None, Some _ | Some _, None -> false)

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

    | Ref x1, Ref x2 ->
       (* XXX should we compare references by value instead? *)
       x1 == x2

    | String s1, String s2 ->
      s1 = s2

    | Derivation _, Derivation _
    | Closure _, Closure _
    | Handler _, Handler _ ->
       v1 == v2

    | External v1, External v2 ->
       equal_external_value v1 v2

    (* At some level the following is a bit ridiculous *)
    | Judgement _, (Boundary _ | Derivation _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _)
    | Derivation _, (Judgement _ | Boundary _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _)
    | Boundary _, (Judgement _ | Derivation _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _)
    | External _, (Judgement _ | Boundary _ | Derivation _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _)
    | Closure _, (Judgement _ | Boundary _ | External _ | Derivation _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _)
    | Handler _, (Judgement _ | Boundary _ | Derivation _ | External _ | Closure _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _)
    | Tag _, (Judgement _ | Boundary _ | Derivation _ | External _ | Closure _ | Handler _ | Tuple _ | Ref _ | Exc _ | String _)
    | Exc _, (Judgement _ | Boundary _ | Derivation _ | External _ | Closure _ | Handler _ | Tuple _ | Ref _ | Tag _ | String _)
    | Tuple _, (Judgement _ | Boundary _ | Derivation _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Ref _ | String _)
    | String _, (Judgement _ | Boundary _ | Derivation _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _)
    | Ref _, (Judgement _ | Boundary _ | Derivation _ | External _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | String _) ->
       false

let exec m env = m env

module Json =
struct

  let rec value v =
    match v with

    | Judgement jdg -> Json.tag "Judgement" [Nucleus.Json.judgement_abstraction jdg]

    | Boundary bdry -> Json.tag "Boundary" [Nucleus.Json.boundary_abstraction bdry]

    | Derivation drv -> Json.tag "Derivation" []

    | Closure _ -> Json.tag "Function" []

    | Handler _ -> Json.tag "Handler" []

    | Exc (exc, None) -> Json.tag "Exc" [Ident.Json.ident exc]

    | Exc (exc, Some v) -> Json.tag "Exc" [Ident.Json.ident exc; value v]

    | Tag (t, lst) -> Json.tag "Tag" [Ident.Json.ident t; Json.List (List.map value lst)]

    | Tuple lst -> Json.tag "Tuple" [Json.List (List.map value lst)]

    | Ref r -> Json.tag "Reference" []

    | String s -> Json.tag "String" [Json.String s]

    | External v -> Json.tag "External" []
end
