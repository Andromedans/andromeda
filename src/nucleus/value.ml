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

and 'a result =
  | Return of 'a
  | Perform of Name.ident * value list * dynamic * (value,'a) closure

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (value list * (value,value) closure, value) closure Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

(** Run-time environment. *)
type env = {
  bound : (Name.ident * value) list;
  continuation : (value,value) closure option;
  handle : (Name.ident * (value list,value) closure) list;
  files : string list;
  dynamic : dynamic;
}

let mk_closure' env f = (fun dyn v -> f {env with dynamic = dyn} v)
let mk_closure env f = Closure (mk_closure' env f)

let apply_closure env f v = f env.dynamic v

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind r f =
  match r with
  | Return v -> f v
  | Perform (op, vs, d, k) -> 
     let k d x = bind (k d x) f in
     Perform (op, vs, d, k)

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

let as_option ~loc = function
  | Term _ -> Error.runtime ~loc "expected an option but got a term"
  | Ty _ -> Error.runtime ~loc "expected an option but got a type"
  | Closure _ -> Error.runtime ~loc "expected an option but got a function"
  | Handler h -> Error.runtime ~loc "expected an option but got a handler"
  | Tag (t,[]) when (Name.eq_ident t name_none)  -> None
  | Tag (t,[x]) when (Name.eq_ident t name_some) -> Some x
  | Tag _ -> Error.runtime ~loc "expected an option but got a tag"

let from_option = function
  | None -> Tag (name_none, [])
  | Some v -> Tag (name_some, [v])

let from_pair (v1, v2) = Tag (name_pair, [v1; v2])

let from_unit () = Tag (name_unit, [])

let rec from_list = function
  | [] -> Tag (name_nil, [])
  | v :: vs -> Tag (name_cons, [v; from_list vs])

let mk_tag t lst = Tag (t, lst)

let return x = Return x

let return_term e = Return (Term e)

let return_ty t = Return (Ty t)

let return_closure env f = Return (mk_closure env f)

let return_handler env handler_val handler_ops handler_finally =
  let option_map g = function None -> None | Some x -> Some (g x) in
  let h = {
    handler_val = option_map (mk_closure' env) handler_val ;
    handler_ops = Name.IdentMap.map (fun f -> mk_closure' env f) handler_ops ;
    handler_finally = option_map (mk_closure' env) handler_finally ;
  } in
  Return (Handler h)

let perform op env vs =
  let k _ = return in
  Perform (op, vs, env.dynamic, k)

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

let perform_equal env v1 v2 =
  perform name_equal env [v1;v2]

let perform_abstract env v1 v2 =
  perform name_abstract env [v1;v2]

let perform_as_prod env v =
  perform name_as_prod env [v]
let perform_as_eq env v =
  perform name_as_eq env [v]
let perform_as_signature env v =
  perform name_as_signature env [v]

let to_value ~loc = function
  | Return v -> v
  | Perform (op, vs, _, _) ->
     Error.runtime ~loc "unhandled operation %t %t"
                   (Name.print_ident op)
                   (Print.sequence (print_value ~max_level:0 []) " " vs)

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


let (>>=) = bind

module AtomSet = Name.AtomSet

let mk_abstractable ~loc env ctx xs =
  let rec fold ctx abstracted zs es = function
    | [] ->
      return (ctx,zs,es)
    | x::xs ->
      begin match Context.lookup_ty x ctx with
        | None ->
          let abstracted = AtomSet.add x abstracted in
          fold ctx abstracted zs es xs
        | Some xty ->
          let rec xfold ctx zs' es' = function
            | [] ->
              let es = List.map (Tt.substitute zs' es') es in
              let zs = zs' @ zs and es = es' @ es in
              let abstracted = AtomSet.add x abstracted in
              fold ctx abstracted zs es xs
            | y::ys when (AtomSet.mem y abstracted) ->
              xfold ctx zs' es' ys
            | y::ys ->
              let yty = (match Context.lookup_ty y ctx with
                | Some ty -> ty
                | None -> Error.impossible
                  ~loc "cannot abstract %t as %t depends on it, but it does not appear in the context?"
                  (Name.print_atom x) (Name.print_atom y)) in
              let vx = Term (Judgement.mk_term ctx (Tt.mk_atom ~loc x) xty)
              and vy = Term (Judgement.mk_term ctx (Tt.mk_atom ~loc y) yty) in
              perform_abstract env vx vy >>= fun v ->
              begin match as_option ~loc v with
                | None ->
                  Error.runtime ~loc "Cannot abstract %t because %t depends on it in context@ %t."
                  (Name.print_atom x) (Name.print_atom y) (Context.print ctx)
                | Some v ->
                  let (ctxe,e,te) = as_term ~loc v in
                  if Tt.alpha_equal_ty yty te
                  then
                    let ctx = Context.join ~loc ctx ctxe in
                    let ehyps = Tt.assumptions_term e in
                    if AtomSet.is_empty (AtomSet.inter ehyps (Context.needed_by ~loc x ctx))
                    then
                      let ctx = Context.substitute ~loc y (ctx,e,te) in
                      xfold ctx (y::zs') (e::es') ys
                    else
                      Error.runtime ~loc "When abstracting %t in context %t, cannot replace %t with %t: it depends on %t"
                        (Name.print_atom x) (Context.print ctx) (Name.print_atom y) (Tt.print_term [] e)
                        (Print.sequence Name.print_atom " " (Name.AtomSet.elements ehyps))
                  else
                    Error.runtime ~loc "When abstracting %t, cannot replace %t : %t with %t : %t (types are not equal)"
                      (Name.print_atom x)
                      (Name.print_atom y) (Tt.print_ty [] yty)
                      (Tt.print_term [] e) (Tt.print_ty [] te)
              end
          in
          let needed_by = Context.needed_by ~loc x ctx in
          let sorted = Context.sort ctx in
          xfold ctx [] [] (List.filter (fun x -> AtomSet.mem x needed_by) sorted)
      end
  in
  fold ctx AtomSet.empty [] [] xs


let context_abstract ~loc env ctx xs ts =
  mk_abstractable ~loc env ctx xs >>= fun (ctx,ys,es) ->
  let ctx = Context.abstract ~loc ctx xs ts in
  return (ctx,ys,es)

module Env = struct
  type t = env

  (** The empty environment *)
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

  let set_dynamic env dyn = {env with dynamic = dyn}

  let bound_names env = List.map fst env.bound

  let used_names env =
    List.map fst env.bound @ List.map fst env.dynamic.decls

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

  let lookup_constant x env =
    match lookup_decl x env with
    | None -> None
    | Some (Constant c) -> Some c
    | Some (Data _ | Operation _) -> None

  let lookup_abstracting env = env.dynamic.abstracting

  let lookup_bound ~loc k env =
    try
      snd (List.nth env.bound k)
    with
    | Failure _ -> Error.impossible ~loc "invalid de Bruijn index %d" k

  let is_declared x env =
    match lookup_decl x env with
    | None -> false
    | Some _ -> true

  let add_operation ~loc x k env =
    if is_declared x env
    then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
    else { env with dynamic = {env.dynamic with decls = (x, Operation k) :: env.dynamic.decls }}

  let add_data ~loc x k env =
    if is_declared x env
    then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
    else { env with dynamic = {env.dynamic with decls = (x, Data k) :: env.dynamic.decls }}

  let add_constant ~loc x ytsu env =
    if is_declared x env
    then Error.runtime ~loc "%t is already declared" (Name.print_ident x)
    else { env with dynamic = {env.dynamic with decls = (x, Constant ytsu) :: env.dynamic.decls }}

  let add_bound x v env =
    { env with bound = (x, v) :: env.bound }

  (** generate a fresh atom of type [t] and bind it to [x]
     NB: This is an effectful computation. *)
  let add_free ~loc env x (ctx, t) =
    let y, ctx = Context.add_fresh ctx x t in
    let yt = Term (ctx, Tt.mk_atom ~loc y, t) in
    let env = add_bound x yt env in
    ctx, y, env

  (** generate a fresh atom of type [t] and bind it to [x],
      and record that the atom will be abstracted.
      NB: This is an effectful computation. *)
  let add_abstracting ~loc env x (ctx, t) =
    let y, ctx = Context.add_fresh ctx x t in
    let ya = Tt.mk_atom ~loc y in
    let jyt = Judgement.mk_term ctx ya t in
    let env = add_bound x (Term jyt) env in
    let env = { env with
                dynamic = { env.dynamic with
                            abstracting = jyt :: env.dynamic.abstracting } }
    in
    ctx, y, env

  let add_handle op xsc env =
    { env with handle = (op, xsc) :: env.handle }

  let lookup_handle op {handle=lst;_} =
    try
      Some (List.assoc op lst)
    with Not_found -> None

  let set_continuation c env =
    { env with continuation = Some c }

  let lookup_continuation {continuation;_} =
    continuation

  let add_file f env =
    { env with files = (Filename.basename f) :: env.files }

  let included f env = List.mem (Filename.basename f) env.files

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


  (** Matching *)

  exception Match_fail

  let application_pop {Tt.term=e;loc;_} =
    match e with
    | Tt.Spine (lhs,(absl,out),rhs) ->
       let rec fold es xts = function
         | [x,tx], [e2] ->
            let xts = List.rev xts in
            let u = Tt.mk_prod_ty ~loc [x,tx] out in
            let e1 = Tt.mk_spine ~loc lhs xts u (List.rev es) in
            let t1 = Tt.instantiate_ty es u in
            let t2 = Tt.instantiate_ty es tx in
            e1,t1,e2,t2
         | (x,tx)::absl, e::rhs ->
            fold (e::es) ((x,tx)::xts) (absl, rhs)
         | [],[] | [],_::_ | _::_,[] ->
                              Error.impossible ~loc "impossible spine encountered in application_pop"
       in
       fold [] [] (absl,rhs)
    | _ -> raise Match_fail

  let rec collect_tt_pattern env xvs (p',_) ctx ({Tt.term=e';loc;_} as e) t =
    match p', e' with
    | Syntax.Tt_Anonymous, _ -> xvs

    | Syntax.Tt_As (p,k), _ ->
       let v = Term (ctx,e,t) in
       let xvs = try
           let v' = List.assoc k xvs in
           if equal_value v v'
           then xvs
           else raise Match_fail
         with | Not_found ->
                 (k,v) :: xvs
       in
       collect_tt_pattern env xvs p ctx e t

    | Syntax.Tt_Bound k, _ ->
       let v' = lookup_bound ~loc k env in
       if equal_value (Term (ctx,e,t)) v'
       then xvs
       else raise Match_fail

    | Syntax.Tt_Type, Tt.Type ->
       xvs

    | Syntax.Tt_Constant x, Tt.Constant (y,lst) ->
       if lst = [] && Name.eq_ident x y
       then xvs
       else raise Match_fail

    | Syntax.Tt_Lambda (x,bopt,popt,p), Tt.Lambda ((x',ty)::abs,(te,out)) ->
       let Tt.Ty t = ty in
       let {Tt.loc=loc;_} = t in
       let xvs = match popt with
         | Some pt -> collect_tt_pattern env xvs pt ctx t (Tt.mk_type_ty ~loc)
         | None -> xvs
       in
       (* XXX should we use [add_abstracting] instead of [add_free]? *)
       let y, ctx = Context.add_fresh ctx x ty in
       let yt = Term (ctx, Tt.mk_atom ~loc y, ty) in
       let env = add_bound x yt env in
       let te = Tt.mk_lambda ~loc:(e.Tt.loc) abs te out in
       let te = Tt.unabstract [y] te in
       let t = Tt.mk_prod_ty ~loc:(e.Tt.loc) abs out in
       let t = Tt.unabstract_ty [y] t in
       let xvs = match bopt with
         | None -> xvs
         | Some k ->
            begin try
                let v' = List.assoc k xvs in
                if equal_value yt v'
                then xvs
                else raise Match_fail
              with
              | Not_found -> (k,yt)::xvs
            end
       in
       let xvs = collect_tt_pattern env xvs p ctx te t in
       xvs

    | Syntax.Tt_App (p1,p2), _ ->
       let te1, ty1, te2, ty2 = application_pop e in
       let xvs = collect_tt_pattern env xvs p1 ctx te1 ty1 in
       let xvs = collect_tt_pattern env xvs p2 ctx te2 ty2 in
       xvs

    | Syntax.Tt_Prod (x,bopt,popt,p), Tt.Prod ((x',ty)::abs,out) ->
       let Tt.Ty t = ty in
       let {Tt.loc=loc;_} = t in
       let xvs = match popt with
         | Some pt -> collect_tt_pattern env xvs pt ctx t (Tt.mk_type_ty ~loc)
         | None -> xvs
       in
       (* Should we use [add_abstracting] instead of [add_fresh]? *)
       let y, ctx = Context.add_fresh ctx x ty in
       let yt = Term (ctx, Tt.mk_atom ~loc y, ty) in
       let env = add_bound x yt env in
       let t = Tt.mk_prod ~loc:(e.Tt.loc) abs out in
       let t = Tt.unabstract [y] t in
       let xvs = match bopt with
         | None -> xvs
         | Some k ->
            begin try
                let v' = List.assoc k xvs in
                if equal_value yt v'
                then xvs
                else raise Match_fail
              with
              | Not_found -> (k,yt)::xvs
            end
       in
       let xvs = collect_tt_pattern env xvs p ctx t (Tt.mk_type_ty ~loc:(e.Tt.loc)) in
       xvs

    | Syntax.Tt_Eq (p1,p2), Tt.Eq (ty,te1,te2) ->
       let xvs = collect_tt_pattern env xvs p1 ctx te1 ty in
       let xvs = collect_tt_pattern env xvs p2 ctx te2 ty in
       xvs

    | Syntax.Tt_Refl p, Tt.Refl (ty,te) ->
       let xvs = collect_tt_pattern env xvs p ctx te ty in
       xvs

    | Syntax.Tt_Signature xps, Tt.Signature xts ->
       let rec fold env xvs ys ctx xps xts =
         match xps, xts with
         | [], [] ->
            xvs
         | (l,x,bopt,p)::xps, (l',x',t)::xts ->
            if Name.eq_ident l l'
            then
              let t = Tt.unabstract_ty ys t in
              let Tt.Ty t' = t in
              let {Tt.loc=loc;_} = t' in
              let xvs = collect_tt_pattern env xvs p ctx t' (Tt.mk_type_ty ~loc) in
              (* XXX should we use [add_abstracting] instead of [add_fresh]? *)
              let y, ctx = Context.add_fresh ctx x t in
              let yt = Term (ctx, Tt.mk_atom ~loc y, t) in
              let env = add_bound x yt env in
              let xvs = match bopt with
                | None -> xvs
                | Some k ->
                   begin try
                       let v' = List.assoc k xvs in
                       if equal_value yt v'
                       then xvs
                       else raise Match_fail
                     with
                     | Not_found -> (k,yt)::xvs
                   end
              in
              fold env xvs (y::ys) ctx xps xts
            else raise Match_fail
         | _::_, [] | [], _::_ ->
                       raise Match_fail
       in
       fold env xvs [] ctx xps xts

    | Syntax.Tt_Structure xps, Tt.Structure xts ->
       let rec fold env xvs ys ctx xps xts =
         match xps, xts with
         | [], [] ->
            xvs
         | (l,x,bopt,p)::xps, (l',x',t,te)::xts ->
            if Name.eq_ident l l'
            then
              let t = Tt.unabstract_ty ys t in
              let te = Tt.unabstract ys te in
              let xvs = collect_tt_pattern env xvs p ctx te t in
              (* Should we use [add_abstracting] instead of [add_fresh]? *)
              let y, ctx = Context.add_fresh ctx x t in
              let Tt.Ty {Tt.loc=loc;_} = t in
              let yt = Term (ctx, Tt.mk_atom ~loc y, t) in
              let env = add_bound x yt env in
              let xvs = match bopt with
                | None -> xvs
                | Some k ->
                   begin try
                       let v' = List.assoc k xvs in
                       if equal_value yt v'
                       then xvs
                       else raise Match_fail
                     with
                     | Not_found -> (k,yt)::xvs
                   end
              in
              fold env xvs (y::ys) ctx xps xts
            else raise Match_fail
         | _::_, [] | [], _::_ ->
                       raise Match_fail
       in
       fold env xvs [] ctx xps xts

    | Syntax.Tt_Projection (p,l), Tt.Projection (te,xts,l') ->
       if Name.eq_ident l l'
       then
         let {Tt.loc=loc;_} = e in
         let xvs = collect_tt_pattern env xvs p ctx te (Tt.mk_signature_ty ~loc xts) in
         xvs
       else raise Match_fail

    | (Syntax.Tt_Type | Syntax.Tt_Constant _ | Syntax.Tt_Lambda _
       | Syntax.Tt_Prod _ | Syntax.Tt_Eq _ | Syntax.Tt_Refl _
       | Syntax.Tt_Signature _ | Syntax.Tt_Structure _
       | Syntax.Tt_Projection _) , _ ->
       raise Match_fail

  let rec collect_pattern env xvs (p,loc) v =
    match p, v with 
    | Syntax.Patt_Anonymous, _ -> xvs

    | Syntax.Patt_As (p,k), v ->
       let xvs = try
           let v' = List.assoc k xvs in
           if equal_value v v'
           then xvs
           else raise Match_fail
         with Not_found -> (k,v) :: xvs
       in
       collect_pattern env xvs p v

    | Syntax.Patt_Bound k, v ->
       let v' = lookup_bound ~loc k env in
       if equal_value v v'
       then xvs
       else raise Match_fail

    | Syntax.Patt_Jdg (pe, pt), Term (ctx, e, t) ->
       let Tt.Ty t' = t in
       let {Tt.loc=loc;_} = t' in
       let xvs = collect_tt_pattern env xvs pt ctx t' (Tt.mk_type_ty ~loc) in
       collect_tt_pattern env xvs pe ctx e t

    | Syntax.Patt_Tag (tag, ps), Tag (tag', vs) when Name.eq_ident tag tag' ->
      multicollect_pattern env xvs ps vs

    | Syntax.Patt_Jdg _, (Ty _ | Closure _ | Handler _ | Tag _)
    | Syntax.Patt_Tag _, (Term _ | Ty _ | Closure _ | Handler _ | Tag _) ->
       raise Match_fail

  and multicollect_pattern env xvs ps vs =
    let rec fold xvs = function
      | [], [] -> xvs
      | p::ps, v::vs ->
        let xvs = collect_pattern env xvs p v in
        fold xvs (ps, vs)
      | ([], _::_ | _::_, []) ->
        raise Match_fail
    in
    fold xvs (ps, vs)

  let match_pattern env p v =
    (* collect values of pattern variables *)
    try
      let xvs = collect_pattern env [] p v in
      (* return in decreasing de bruijn order: ready to fold with add_bound *)
      let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
      let xvs = List.rev_map snd xvs in
      Some xvs
    with Match_fail -> None

  let multimatch_pattern env ps vs =
    try
      let xvs = multicollect_pattern env [] ps vs in
      (* return in decreasing de bruijn order: ready to fold with add_bound *)
      let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
      let xvs = List.rev_map snd xvs in
      Some xvs
    with Match_fail -> None

end (* [module Env] *)

let rec handle_result env {handler_val; handler_ops; handler_finally} r =
  begin match r with
  | Return v ->
     begin match handler_val with
     | Some f -> apply_closure env f v
     | None -> r
     end
  | Perform (op, vs, dyn, cont) ->
     let env = Env.set_dynamic env dyn in
     let h = {handler_val; handler_ops; handler_finally=None} in
     let cont = mk_closure' env (fun env v -> handle_result env h (apply_closure env cont v)) in
     begin
       try
         let f = Name.IdentMap.find op handler_ops in
         f dyn (vs, cont)
       with
         Not_found ->
           Perform (op, vs, dyn, cont)
     end
  end >>=
  (fun v ->
     match handler_finally with
     | Some f -> apply_closure env f v
     | None -> Return v)

let rec top_handle ~loc env = function
  | Return v -> v
  | Perform (op, vs, dyn, k) ->
     let env = Env.set_dynamic env dyn in
     begin match Env.lookup_handle op env with
      | None -> Error.runtime ~loc "unhandled operation %t" (Name.print_op op)
      | Some f ->
        let r = apply_closure env f vs >>=
          apply_closure env k
        in
        top_handle ~loc env r
     end

