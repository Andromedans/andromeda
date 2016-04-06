
type meta = int

let fresh_meta : unit -> meta =
  let counter = ref 0 in
  fun () ->
    let m = !counter in
    incr counter;
    m

type ty =
  | Jdg
  | String
  | Meta of meta
  | Tuple of ty list
  | Arrow of ty * ty
  | Handler of ty * ty
  | App of Name.ident * Syntax.level * ty list
  | Ref of ty

let fresh_type () = Meta (fresh_meta ())

(** The metavariables are generalised in the following values. *)
type 'a forall = meta list * 'a

type ty_schema = ty forall

type constructor = Name.constructor * ty list

type ty_def =
  | Alias of ty forall
  | Sum of constructor list forall

(** Make a schema from a type without generalizing anything. *)
let ungeneralized_schema (t : ty) : ty_schema = [], t

type error =
  | InvalidApplication of ty * ty * ty
  | TypeMismatch of ty * ty
  | UnsolvedApp of ty * ty * ty
  | HandlerExpected of ty

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

let print_meta ~penv (m : meta) ppf =
  let s =
    try List.assoc m !penv
    with Not_found ->
      let l = List.length !penv in
      let s = Name.greek l in
      penv := (m, s) :: !penv;
      s
  in
  Format.fprintf ppf "%s" s

let rec print_ty ~penv ?max_level t ppf =
  match t with

  | Jdg -> Format.fprintf ppf "Judgement"

  | String -> Format.fprintf ppf "string"

  | Meta m -> print_meta ~penv m ppf

  | Tuple ts -> Print.print ?max_level ppf "%t"
                            (Print.sequence (print_ty ~penv ~max_level:Level.ml_prod_arg) " *" ts)

  | Arrow (t1, t2) ->
     Print.print ?max_level ~at_level:(Level.ml_arr) ppf "%t@ %s@ %t"
                 (print_ty ~penv ~max_level:(Level.ml_arr_left) t1)
                 (Print.char_arrow ())
                 (print_ty ~penv ~max_level:(Level.ml_arr_right) t2)

  | Handler (t1, t2) ->
     Print.print ?max_level ~at_level:(Level.ml_handler) ppf "%t@ %s@ %t"
                 (print_ty ~penv ~max_level:(Level.ml_handler_left) t1)
                 (Print.char_darrow ())
                 (print_ty ~penv ~max_level:(Level.ml_handler_right) t2)

  | App (x, _, ts) ->
     Print.print ?max_level ~at_level:Level.ml_app ppf "%t@ %t"
                 (Name.print_ident x)
                 (Print.sequence (print_ty ~penv ~max_level:Level.ml_app_arg) "" ts)

  | Ref t -> Print.print ?max_level ~at_level:Level.ml_app ppf "ref@ %t"
                         (print_ty ~penv ~max_level:Level.ml_app_arg t)

let print_error err ppf =
  let penv = ref [] in
  match err with
  | InvalidApplication (h, arg, out) ->
    Format.fprintf ppf "Invalid application of %t to %t producing %t"
      (print_ty ~penv h)
      (print_ty ~penv arg)
      (print_ty ~penv out)
  | TypeMismatch (t1, t2) ->
    Format.fprintf ppf "Expected %t but got %t"
      (print_ty ~penv t2)
      (print_ty ~penv t1)
  | UnsolvedApp (h, arg, out) ->
    Format.fprintf ppf "Unsolved application of %t to %t producing %t"
      (print_ty ~penv h)
      (print_ty ~penv arg)
      (print_ty ~penv out)
  | HandlerExpected t ->
    Format.fprintf ppf "Expected a handler but got %t"
      (print_ty ~penv t)

let rec occurs m = function
  | Jdg | String -> false
  | Meta m' -> m = m'
  | Tuple ts  | App (_, _, ts) ->
    List.exists (occurs m) ts
  | Arrow (t1, t2) | Handler (t1, t2) ->
    occurs m t1 || occurs m t2
  | Ref t -> occurs m t

module MetaSet = Set.Make(struct
  type t = meta
  let compare = compare
  end)

let rec occuring = function
  | Jdg | String -> MetaSet.empty
  | Meta m -> MetaSet.singleton m
  | Tuple ts  | App (_, _, ts) ->
    List.fold_left (fun s t -> MetaSet.union s (occuring t)) MetaSet.empty ts
  | Arrow (t1, t2) | Handler (t1, t2) ->
    MetaSet.union (occuring t1) (occuring t2)
  | Ref t -> occuring t

let occuring_schema ((ms, t) : ty_schema) : MetaSet.t =
  let s = occuring t in
  List.fold_left (fun s m -> MetaSet.remove m s) s ms

module Substitution : sig
  type t

  val empty : t

  val lookup : meta -> t -> ty option

  val apply : t -> ty -> ty

  val freshen_metas : meta list -> t * meta list

  val from_lists : meta list -> ty list -> t

  val add : meta -> ty -> t -> t option

  val gather_known : t -> MetaSet.t
end = struct
  module MetaMap = Map.Make(struct
    type t = meta
    let compare = compare
    end)

  type t = ty MetaMap.t

  let lookup m s =
    try Some (MetaMap.find m s)
    with Not_found -> None

  let apply (s : t) t =
    if MetaMap.is_empty s then t
    else
    let rec aux = function
      | Jdg | String as t -> t
      | Meta m as orig ->
        begin match lookup m s with
          | Some t -> t
          | None -> orig
        end
      | Tuple ts ->
        let ts = List.map aux ts in
        Tuple ts
      | Arrow (t1, t2) ->
        let t1 = aux t1
        and t2 = aux t2 in
        Arrow (t1, t2)
      | Handler (t1, t2) ->
        let t1 = aux t1
        and t2 = aux t2 in
        Handler (t1, t2)
      | App (x, k, ts) ->
        let ts = List.map aux ts in
        App (x, k, ts)
      | Ref t ->
        let t = aux t in
        Ref t
    in
    aux t

  let empty : t = MetaMap.empty

  let freshen_metas ms =
    let s, ms' = List.fold_left (fun (s, ms') m ->
        let m' = fresh_meta () in
        MetaMap.add m (Meta m') s, m' :: ms')
      (empty, []) ms
    in
    s, List.rev ms'

  let from_lists ms ts =
    List.fold_left2 (fun s m t ->
        MetaMap.add m t s)
      empty ms ts

  let add m t s =
    let t = apply s t in
    if occurs m t
    then
      None
    else
      Some (MetaMap.add m t s)

  let gather_known s =
    MetaMap.fold (fun m _t known ->
        MetaSet.add m known)
      s MetaSet.empty
end

type constrain =
  | AppConstraint of Location.t * ty * ty * ty

type generalizable =
  | Generalizable
  | Ungeneralizable

let rec generalizable c = match c.Location.thing with
(* yes *)
  | Syntax.Bound _ | Syntax.Function _ | Syntax.Handler _ -> Generalizable
  | Syntax.Constructor (_, cs) | Syntax.Tuple cs ->
    if List.for_all (fun c -> generalizable c = Generalizable) cs
    then Generalizable
    else Ungeneralizable

(* who knows *)
  | Syntax.Let _ | Syntax.LetRec _ | Syntax.Sequence _ -> Ungeneralizable

(* no *)
  | _ -> Ungeneralizable

module Ctx : sig
  type t

  val empty : t

  val lookup_var : Syntax.bound -> t -> ty

  val lookup_op : Name.operation -> t -> ty list * ty

  val lookup_constructor : Name.constructor -> t -> ty list * ty

  val lookup_continuation : t -> ty * ty

  val add_var : Name.ident -> ty_schema -> t -> t

  val add_tydef : Name.ident -> ty_def -> t -> t

  val add_operation : Name.operation -> ty list * ty -> t -> t

  val add_lets : (Name.ident * generalizable * ty) list -> MetaSet.t -> Substitution.t -> t -> t

  (** Creates the context for evaluating the operation handling of [op] *)
  val op_cases : Name.operation -> output:ty -> t -> ty list * t

  val unfold : t -> Syntax.level -> ty list -> ty option

  val gather_known : t -> MetaSet.t
end = struct
  module OperationMap = Name.IdentMap

  type t = {
    types : (Name.ident * ty_def) list; (* types are accessed by De Bruijn level, the name is for printing only. *)
    variables : (Name.ident * ty_schema) list; (* variables are accessed by De Bruijn index, the name is for printing only. *)
    operations : (ty list * ty) OperationMap.t;
    continuation : (ty * ty) option;
  }

  let empty = {
    types = [];
    variables = [];
    operations = OperationMap.empty;
    continuation = None;
  }

  let lookup_var k {variables;_} =
    let _, (ms, t) = List.nth variables k in
    let s, _ = Substitution.freshen_metas ms in
    Substitution.apply s t

  let lookup_op op {operations;_} =
    OperationMap.find op operations

  let lookup_constructor c {types;_} =
    let rec fold = function
      | [] -> raise Not_found
      | (_, Alias _) :: types -> fold types
      | (x, Sum (ms, constructors)) :: types ->
        let rec search = function
          | [] -> fold types
          | (c', ts) :: _ when Name.eq_ident c c' ->
            let s, ms' = Substitution.freshen_metas ms in
            let ts = List.map (Substitution.apply s) ts
            and out = App (x, List.length types, List.map (fun m -> Meta m) ms') in
            ts, out
          | _ :: rem -> search rem
        in
        search constructors
    in
    fold types

  let lookup_continuation {continuation;_} =
    match continuation with
      | Some cont -> cont
      | None -> assert false

  let add_var x t ctx =
    let variables = (x, t) :: ctx.variables in
    {ctx with variables}

  let add_tydef t d ctx =
    let types = (t, d) :: ctx.types in
    {ctx with types}

  let add_operation op opty ctx =
    let operations = OperationMap.add op opty ctx.operations in
    {ctx with operations}

  let remove_known ~known s =
    MetaSet.fold MetaSet.remove known s

  let add_let known s ctx (x, gen, t) =
    let t = Substitution.apply s t in
    let s = match gen with
      | Ungeneralizable -> ungeneralized_schema t
      | Generalizable ->
        let gen = occuring t in
        let gen = remove_known ~known gen in
        let gen = MetaSet.elements gen in
        gen, t
    in
    let variables = (x, s) :: ctx.variables in
    {ctx with variables}
      

  let add_lets xts known s ctx =
    List.fold_left (add_let known s) ctx xts

  let op_cases op ~output ctx =
    let (args, opout) = OperationMap.find op ctx.operations in
    let continuation = Some (opout, output) in
    args, {ctx with continuation}

  let unfold ctx x ts =
    let _, def = List.nth (List.rev ctx.types) x in
    match def with
      | Sum _ -> None
      | Alias (ms, t) ->
        let s = Substitution.from_lists ms ts in
        Some (Substitution.apply s t)

  let gather_known {types = _; variables; operations = _; continuation} =
    let known = List.fold_left (fun known (_, s) -> MetaSet.union known (occuring_schema s)) MetaSet.empty variables in
    let known = match continuation with
      | Some (t1, t2) -> MetaSet.union known (MetaSet.union (occuring t1) (occuring t2))
      | None -> known
    in
    known
end

module TopEnv = struct
  type t = {
    topctx : Ctx.t;
    topsubst : Substitution.t;
  }
  
  let empty = {
    topctx = Ctx.empty;
    topsubst = Substitution.empty;
  }

  let add_tydef t d env =
    let topctx = Ctx.add_tydef t d env.topctx in
    {env with topctx}

  let add_operation op opty env =
    let topctx = Ctx.add_operation op opty env.topctx in
    {env with topctx}

  let gather_known env =
    MetaSet.union (Ctx.gather_known env.topctx) (Substitution.gather_known env.topsubst)

  let add_lets xts env =
    let known = gather_known env in
    let topctx = Ctx.add_lets xts known env.topsubst env.topctx in
    {env with topctx}
end

module Env : sig
  type 'a mon

  val return : 'a -> 'a mon

  val (>>=) : 'a mon -> ('a -> 'b mon) -> 'b mon

  val at_toplevel : TopEnv.t -> 'a mon -> 'a * TopEnv.t

  val lookup_var : Syntax.bound -> ty mon

  val lookup_op : Name.operation -> (ty list * ty) mon

  val lookup_constructor : Name.constructor -> (ty list * ty) mon

  val lookup_continuation : (ty * ty) mon

  val add_var : Name.ident -> ty -> 'a mon -> 'a mon

  val add_equation : loc:Location.t -> ty -> ty -> unit mon

  val add_application : loc:Location.t -> ty -> ty -> ty -> unit mon

  val add_lets : (Name.ident * generalizable * ty) list -> 'a mon -> 'a mon

  val as_handler : loc:Location.t -> ty -> (ty * ty) mon

  val as_ref : loc:Location.t -> ty -> ty mon

  val op_cases : Name.operation -> output:ty -> (ty list -> 'a mon) -> 'a mon
end = struct
  type t = {
    context : Ctx.t;
    substitution : Substitution.t;
    unsolved : constrain list;
  }

  let of_topenv {TopEnv.topctx; topsubst} = {
    context = topctx;
    substitution = topsubst;
    unsolved = [];
  }

  type 'a mon = t -> 'a * Substitution.t * constrain list

  let return x env = x, env.substitution, env.unsolved

  let (>>=) m f env =
    let x, substitution, unsolved = m env in
    f x {env with substitution; unsolved}

  let lookup_var k env =
    let t = Ctx.lookup_var k env.context in
    return t env

  let lookup_op op env =
    return (Ctx.lookup_op op env.context) env

  let lookup_constructor c env =
    return (Ctx.lookup_constructor c env.context) env

  let lookup_continuation env =
    return (Ctx.lookup_continuation env.context) env

  let add_var x t m env =
    let context = Ctx.add_var x (ungeneralized_schema t) env.context in
    m {env with context}

  let gather_known env =
    let known = MetaSet.union (Ctx.gather_known env.context) (Substitution.gather_known env.substitution) in
    List.fold_left (fun known (AppConstraint (_, t1, t2, t3)) ->
        MetaSet.union known (MetaSet.union (occuring t1) (MetaSet.union (occuring t2) (occuring t3))))
      known env.unsolved

  let add_lets xts m env =
    let known = gather_known env in
    let context = Ctx.add_lets xts known env.substitution env.context in
    m {env with context}

  (* Whnf for meta instantiations and type aliases *)
  let rec whnf ctx s = function
    | Meta m as t ->
      begin match Substitution.lookup m s with
        | Some t -> whnf ctx s t
        | None -> t
      end
    | App (_, x, ts) as t ->
      begin match Ctx.unfold ctx x ts with
        | Some t -> whnf ctx s t
        | None -> t
      end
    | _ as t -> t

  let rec unifiable ctx s t t' =
    let (>?=) m f = match m with
      | Some x -> f x
      | None -> None
    in
    match whnf ctx s t, whnf ctx s t' with
      | Jdg, Jdg | String, String -> Some s
      | Meta m, Meta m' when m = m' -> Some s
      | Meta m, t -> Substitution.add m t s
      | t, Meta m -> Substitution.add m t s
      | Ref t, Ref t' -> unifiable ctx s t t'
      | Tuple ts, Tuple ts' ->
        let rec fold s ts ts' = match ts, ts' with
          | [], [] -> Some s
          | t :: ts, t' :: ts' ->
            unifiable ctx s t t' >?= fun s ->
            fold s ts ts'
          | [], _ :: _ | _ :: _, [] -> None
        in
        fold s ts ts'
      | Arrow (t1, t2), Arrow (t1', t2') ->
        unifiable ctx s t1 t1' >?= fun s ->
        unifiable ctx s t2 t2'
      | Handler (t1, t2), Handler (t1', t2') ->
        unifiable ctx s t1 t1' >?= fun s ->
        unifiable ctx s t2 t2'
      | App (_, x, ts), App (_, y, ts') when x = y ->
        let rec fold s ts ts' = match ts, ts' with
          | [], [] -> Some s
          | t :: ts, t' :: ts' ->
            unifiable ctx s t t' >?= fun s ->
            fold s ts ts'
          | [], _ :: _ | _ :: _, [] -> assert false
        in
        fold s ts ts'
      | (Jdg | String | Ref _ | Tuple _ | Arrow _ | Handler _ | App _), _ -> None

  let add_equation ~loc t t' env =
    match unifiable env.context env.substitution t t' with
      | Some s ->
        (* TODO process unsolved *)
        (), s, env.unsolved
      | None -> error ~loc (TypeMismatch (Substitution.apply env.substitution t,
                                          Substitution.apply env.substitution t'))

  let add_application ~loc h arg out env =
    let s = env.substitution in
    let h = whnf env.context s h
    and arg = whnf env.context s arg
    and out = whnf env.context s out in
    match h, arg, out with
      | Jdg, _, _ ->
        (>>=) (add_equation ~loc arg Jdg) (fun () -> add_equation ~loc out Jdg) env
      | Arrow (a, b), _, _ ->
        (>>=) (add_equation ~loc arg a) (fun () -> add_equation ~loc out b) env
      | Meta _, (Jdg | Meta _), (Jdg | Meta _) ->
        let unsolved = AppConstraint (loc, h, arg, out) :: env.unsolved in
        (), s, unsolved
      | Meta m, _, _ ->
        begin match Substitution.add m (Arrow (arg, out)) s with
          | Some s ->
            (), s, env.unsolved
          | None -> error ~loc (InvalidApplication (h, arg, out))
        end
      | _, _, _ -> error ~loc (InvalidApplication (h, arg, out))

  let as_handler ~loc t env =
    let t = whnf env.context env.substitution t in
    match t with
      | Handler (a, b) -> return (a, b) env
      | Meta m ->
        let a = fresh_type ()
        and b = fresh_type () in
        begin match Substitution.add m (Handler (a, b)) env.substitution with
          | Some substitution -> return (a, b) {env with substitution}
          | None -> assert false
        end
      | _ -> error ~loc (HandlerExpected t)

  let as_ref ~loc t = assert false (* TODO *)

  let op_cases op ~output m env =
    let argts, context = Ctx.op_cases op ~output env.context in
    m argts {env with context}

  let to_solved env =
    match env.unsolved with
      | [] -> {TopEnv.topctx = env.context; topsubst = env.substitution}
      | AppConstraint (loc, arg, h, out) :: unsolved ->
        let s = env.substitution in
        let h = Substitution.apply s h
        and arg = Substitution.apply s arg
        and out = Substitution.apply s out in
        error ~loc (UnsolvedApp (arg, h, out))

  let at_toplevel top m =
    let env = of_topenv top in
    let x, substitution, unsolved = m env in
    let top = to_solved {env with substitution; unsolved} in
    x, top
end

let rec tt_pattern xs {Location.thing = p; loc} =
  let (>>=) = Env.(>>=) in
  match p with
  | Syntax.Tt_Anonymous -> Env.return ()

  | Syntax.Tt_As (p, k) ->
    let _, t = List.nth xs k in
    Env.add_equation ~loc t Jdg >>= fun () ->
    tt_pattern xs p

  | Syntax.Tt_Bound k ->
    Env.lookup_var k >>= fun t ->
    Env.add_equation ~loc t Jdg

  | Syntax.Tt_Type -> Env.return ()

  | Syntax.Tt_Constant _ -> Env.return ()

  | Syntax.Tt_Lambda (x, _, popt, p)
  | Syntax.Tt_Prod (x, _, popt, p) ->
    begin match popt with
      | Some pt -> tt_pattern xs pt
      | None -> Env.return ()
    end >>= fun () ->
    Env.add_var x Jdg (tt_pattern xs p)

  | Syntax.Tt_Apply (p1, p2) 
  | Syntax.Tt_Eq (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2

  | Syntax.Tt_Refl p | Syntax.Tt_GenAtom p | Syntax.Tt_GenConstant p ->
    tt_pattern xs p
  

let rec pattern xs {Location.thing = p; loc} =
  let (>>=) = Env.(>>=) in
  match p with
  | Syntax.Patt_Anonymous -> Env.return (fresh_type ())

  | Syntax.Patt_As (p, k) ->
    let _, t = List.nth xs k in
    check_pattern xs p t >>= fun () ->
    Env.return t

  | Syntax.Patt_Bound k -> Env.lookup_var k

  | Syntax.Patt_Jdg (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2 >>= fun () ->
    Env.return Jdg

  | Syntax.Patt_Constructor (c, ps) ->
    Env.lookup_constructor c >>= fun (ts, out) ->
    let tps = List.combine ts ps in
    let rec fold = function
      | [] ->
        Env.return out
      | (t, p) :: tps ->
        check_pattern xs p t >>= fun () ->
        fold tps
    in
    fold tps

  | Syntax.Patt_Tuple ps ->
    let rec fold ts = function
      | [] ->
        let ts = List.rev ts in
        Env.return (Tuple ts)
      | p :: ps ->
        pattern xs p >>= fun t ->
        fold (t :: ts) ps
    in
    fold [] ps

and check_pattern xs p t =
  let (>>=) = Env.(>>=) in
  pattern xs p >>= fun t' ->
  Env.add_equation ~loc:p.Location.loc t' t

let match_case : type a. _ -> _ -> _ -> a Env.mon -> a Env.mon = fun xs p t m ->
  let (>>=) = Env.(>>=) in
  (* add a fresh type to each [x] *)
  let xs = List.map (fun x -> x, fresh_type ()) xs in
  check_pattern xs p t >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | (x, t) :: xs ->
      Env.add_var x t (add_vars xs)
  in
  add_vars xs

let match_op_case xs ps popt argts m =
  let (>>=) = Env.(>>=) in
  let xs = List.map (fun x -> x, fresh_type ()) xs in
  let pts = List.combine ps argts in
  let pts = match popt with
    | Some p -> (p, Jdg) :: pts
    | None -> pts
  in
  let rec fold = function
    | [] -> Env.return ()
    | (p, t) :: pts ->
      check_pattern xs p t >>= fun () ->
      fold pts
  in
  fold pts >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | (x, t) :: xs ->
      Env.add_var x t (add_vars xs)
  in
  add_vars xs  

let rec comp ({Location.thing=c; loc} : Syntax.comp) =
  let (>>=) = Env.(>>=) in
  match c with
  | Syntax.Type -> Env.return Jdg

  | Syntax.Bound k -> Env.lookup_var k

  | Syntax.Function (x, c) ->
    let a = fresh_type () in
    Env.add_var x a (comp c) >>= fun b ->
    Env.return (Arrow (a, b))

  | Syntax.Handler h -> handler ~loc h

  | Syntax.Constructor (c, cs) ->
    Env.lookup_constructor c >>= fun (ts, out) ->
    let tcs = List.combine ts cs in
    let rec fold = function
      | [] ->
        Env.return out
      | (t, c) :: tcs ->
        check_comp c t >>= fun () ->
        fold tcs
    in
    fold tcs

  | Syntax.Tuple cs ->
    let rec fold ts = function
      | [] ->
        let ts = List.rev ts in
        Env.return (Tuple ts)
      | c :: cs ->
        comp c >>= fun t ->
        fold (t :: ts) cs
    in
    fold [] cs

  | Syntax.Operation (op, cs) ->
    Env.lookup_op op >>= fun (expected, out) ->
    let tcs = List.combine expected cs in
    let rec fold = function
      | [] ->
        Env.return out
      | (t, c) :: tcs ->
        check_comp c t >>= fun () ->
        fold tcs
    in
    fold tcs

  | Syntax.With (h, c) ->
    comp h >>= fun th ->
    Env.as_handler ~loc:h.Location.loc th >>= fun (a, b) ->
    check_comp c a >>= fun () ->
    Env.return b

  | Syntax.Let (xcs, c) ->
    let rec fold xts = function
      | [] ->
        let xts = List.rev xts in
        Env.return xts
      | (x, c) :: xcs ->
        comp c >>= fun t ->
        let gen = generalizable c in
        fold ((x, gen, t) :: xts) xcs
    in
    fold [] xcs >>= fun xts ->
    Env.add_lets xts (comp c)

  | Syntax.LetRec (xycs, c) ->
    let abxycs = List.map (fun xyc -> fresh_type (), fresh_type (), xyc) xycs in
    let rec fold = function
      | [] -> Env.return ()
      | (a, b, (_, y, c)) :: rem ->
        Env.add_var y a (check_comp c b) >>= fun () ->
        fold rem
    in
    Env.add_lets (List.map (fun (a, b, (x, _, _)) -> x, Ungeneralizable, Arrow (a, b)) abxycs) (fold abxycs) >>= fun () ->
    Env.add_lets (List.map (fun (a, b, (x, _, _)) -> x, Generalizable, Arrow (a, b)) abxycs) (comp c)

  | Syntax.Now (x, c1, c2) ->
    Env.lookup_var x >>= fun tx ->
    check_comp c1 tx >>= fun () ->
    comp c2

  | Syntax.Lookup c ->
    comp c >>= fun t ->
    Env.as_ref ~loc:c.Location.loc t    

  | Syntax.Update (c1, c2) ->
    comp c1 >>= fun t1 ->
    Env.as_ref ~loc:c1.Location.loc t1 >>= fun t ->
    check_comp c2 t >>= fun () ->
    Env.return (Tuple [])

  | Syntax.Ref c ->
    comp c >>= fun t ->
    Env.return (Ref t)

  | Syntax.Sequence (c1, c2) ->
    comp c1 >>= fun _ ->
    (* TODO warn if not unit? *)
    comp c2

  | Syntax.Assume ((x, t), c) ->
    check_comp c Jdg >>= fun () ->
    Env.add_var x Jdg (comp c)

  | Syntax.Where (c1, c2, c3) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    check_comp c3 Jdg >>= fun () ->
    Env.return Jdg

  | Syntax.Match (c, cases) ->
    comp c >>= fun t ->
    match_cases ~loc t cases

  | Syntax.Ascribe (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    Env.return Jdg

  | Syntax.External _ -> Env.return (fresh_type ()) (* TODO *)

  | Syntax.Constant _ -> Env.return Jdg

  | Syntax.Lambda (x, copt, c) ->
    begin match copt with
      | Some ct -> check_comp ct Jdg
      | None -> Env.return ()
    end >>= fun () ->
    Env.add_var x Jdg (check_comp c Jdg) >>= fun () ->
    Env.return Jdg

  | Syntax.Apply (c1, c2) ->
    comp c1 >>= fun t1 ->
    comp c2 >>= fun t2 ->
    let out = fresh_type () in
    Env.add_application ~loc t1 t2 out >>= fun () ->
    Env.return out

  | Syntax.Prod (x, ct, c) ->
    check_comp ct Jdg >>= fun () ->
    Env.add_var x Jdg (check_comp c Jdg) >>= fun () ->
    Env.return Jdg

  | Syntax.Eq (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    Env.return Jdg    

  | Syntax.Refl c ->
    check_comp c Jdg >>= fun () ->
    Env.return Jdg

  | Syntax.Yield c ->
    Env.lookup_continuation >>= fun (a, b) ->
    check_comp c a >>= fun () ->
    Env.return b

  | Syntax.Hypotheses -> assert false (* TODO *)

  | Syntax.Congruence (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    assert false (* TODO *)    

  | Syntax.Extensionality (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    assert false (* TODO *)    

  | Syntax.Reduction c ->
    check_comp c Jdg >>= fun () ->
    assert false (* TODO *)    

  | Syntax.String _ -> Env.return String

  | Syntax.Occurs (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    assert false (* TODO *)

  | Syntax.Context c ->
    check_comp c Jdg >>= fun () ->
    assert false (* TODO *)    

and check_comp c t =
  let (>>=) = Env.(>>=) in
  comp c >>= fun t' ->
  Env.add_equation ~loc:c.Location.loc t' t

and handler ~loc {Syntax.handler_val=handler_val;handler_ops;handler_finally} =
  let (>>=) = Env.(>>=) in
  let input = fresh_type () in
  begin match handler_val with
    | [] -> Env.return input
    | _ :: _ -> match_cases ~loc input handler_val
  end >>= fun output ->
  begin match handler_finally with
    | [] -> Env.return output
    | _ :: _ -> match_cases ~loc output handler_finally
  end >>= fun final ->
  Name.IdentMap.fold (fun op cases m ->
      m >>= fun () ->
      match_op_cases op cases output)
    handler_ops (Env.return ()) >>= fun () ->
  Env.return (Handler (input, final))

and match_cases ~loc t cases =
  let (>>=) = Env.(>>=) in
  match cases with
    | [] -> assert false (* TODO *)
    | (xs, p, c) :: others ->
      match_case xs p t (comp c) >>= fun out ->
      let rec fold = function
        | [] -> Env.return out
        | (xs, p, c) :: others ->
          match_case xs p t (check_comp c out) >>= fun () ->
          fold others
      in
      fold others

and match_op_cases op cases output =
  let (>>=) = Env.(>>=) in
  Env.op_cases op ~output (fun argts ->
  let rec fold = function
    | [] -> Env.return ()
    | (xs, ps, popt, c) :: cases ->
      match_op_case xs ps popt argts (check_comp c output) >>= fun () ->
      fold cases
  in
  fold cases)

let rec ml_ty params {Location.thing=t; loc} =
  match t with
  | Syntax.ML_Arrow (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Arrow (t1, t2)
  | Syntax.ML_Prod ts ->
    let ts = List.map (ml_ty params) ts in
    Tuple ts
  | Syntax.ML_TyApply (x, k, ts) ->
    let ts = List.map (ml_ty params) ts in
    App (x, k, ts)
  | Syntax.ML_Handler (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Handler (t1, t2)
  | Syntax.ML_Judgment -> Jdg
  | Syntax.ML_Param p -> Meta (List.nth params p)


let add_tydef env (t, (params, def)) =
  let params = List.map (fun _ -> fresh_meta ()) params in
  match def with
    | Syntax.ML_Alias t' ->
      let t' = ml_ty params t' in
      TopEnv.add_tydef t (Alias (params, t')) env
    | Syntax.ML_Sum constructors ->
      let constructors = List.map (fun (c, ts) -> c, List.map (ml_ty params) ts) constructors in
      TopEnv.add_tydef t (Sum (params, constructors)) env

let add_operation op (args, out) env =
  let args = List.map (ml_ty []) args
  and out = ml_ty [] out in
  TopEnv.add_operation op (args, out) env

let rec toplevel env ({Location.thing=c; loc} : Syntax.toplevel) =
  match c with
  (* Desugar is the only place where recursion/nonrecursion matters *)
  | Syntax.DefMLType tydefs
  | Syntax.DefMLTypeRec tydefs ->
    List.fold_left add_tydef env tydefs

  | Syntax.DeclOperation (op, opty) ->
    add_operation op opty env

  | Syntax.DeclConstants (cs, t) ->
    let (), env = Env.at_toplevel env (check_comp t Jdg) in
    env

  | Syntax.TopHandle _ -> assert false (* TODO *)

  | Syntax.TopLet xcs ->
    let rec fold xts = function
      | [] ->
        let xts = List.rev xts in
        Env.return xts
      | (x, c) :: xcs ->
        Env.(comp c >>= fun t ->
        let gen = generalizable c in
        fold ((x, gen, t) :: xts) xcs)
    in
    let xts, env = Env.at_toplevel env (fold [] xcs) in
    TopEnv.add_lets xts env

  | Syntax.TopLetRec xycs ->
    let abxycs = List.map (fun xyc -> fresh_type (), fresh_type (), xyc) xycs in
    let rec fold = function
      | [] -> Env.return ()
      | (a, b, (_, y, c)) :: rem ->
        Env.(add_var y a (check_comp c b) >>= fun () ->
        fold rem)
    in
    let (), env = Env.at_toplevel env
      (Env.add_lets (List.map (fun (a, b, (x, _, _)) -> x, Ungeneralizable, Arrow (a, b)) abxycs) (fold abxycs))
    in
    TopEnv.add_lets (List.map (fun (a, b, (x, _, _)) -> x, Generalizable, Arrow (a, b)) abxycs) env

  | Syntax.TopDynamic (_,_) -> assert false (* TODO *)

  | Syntax.TopNow (_,_) -> assert false (* TODO *)

  | Syntax.TopDo c ->
    let _, env = Env.at_toplevel env (comp c) in
    env

  | Syntax.TopFail c ->
    let _, env = Env.at_toplevel env (comp c) in
    env

  | Syntax.Verbosity _ -> env

  | Syntax.Included cs ->
     List.fold_left
       (fun env (f, cs) -> List.fold_left toplevel env cs) env cs

