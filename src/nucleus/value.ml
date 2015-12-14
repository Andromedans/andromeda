(** Runtime values and results *)

type value =
  | Term of Judgement.term
  | Ty of Judgement.ty
  | Closure of closure
  | Handler of handler
  | Tag of Name.ident * value list

and closure = value -> value result

and 'a result =
  | Return of 'a
  | Operation of string * value * (value -> 'a result)

and handler = {
  handler_val: closure option;
  handler_ops: (string * (value -> value -> value result)) list;
  handler_finally: closure option;
}

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind r f =
  match r with
  | Return v -> f v
  | Operation (op, v, k) -> Operation (op, v, fun x -> (bind (k x) f))


let print_closure xs _ ppf =
  Print.print ~at_level:0 ppf "<function>"

let print_handler xs h ppf =
  Print.print ~at_level:0 ppf "<handler>" (* XXX improve in your spare time *)

let rec print_tag ?max_level xs t lst ppf =
  match lst with
  | [] -> Print.print ?max_level ~at_level:0 ppf "'%t" (Name.print_ident t)
  | (_::_) -> Print.print ?max_level ~at_level:1 ppf "'%t %t"
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

let tsome = Name.make "some"
let tnone = Name.make "none"

let as_option ~loc = function
  | Term _ -> Error.runtime ~loc "expected an option but got a term"
  | Ty _ -> Error.runtime ~loc "expected an option but got a type"
  | Closure _ -> Error.runtime ~loc "expected an option but got a function"
  | Handler h -> Error.runtime ~loc "expected an option but got a handler"
  | Tag (t,[]) when (Name.eq_ident t tnone)  -> None
  | Tag (t,[x]) when (Name.eq_ident t tsome) -> Some x
  | Tag _ -> Error.runtime ~loc "expected an option but got a tag"

let return x = Return x

let return_term e = Return (Term e)

let return_ty t = Return (Ty t)

let operate op v = Operation (op,v,return)

let to_value ~loc = function
  | Return v -> v
  | Operation (op, v, _) ->
     Error.runtime ~loc "unhandled operation %t %t" (Name.print_op op) (print_value ~max_level:0 [] v)

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

let mk_abstractable ~loc ctx xs =
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
              let vpair = Tag (Name.make "pair", [vx;vy]) in
              operate "abstract" vpair >>= fun v ->
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
                      Error.runtime "When abstracting %t in context %t, cannot replace %t with %t: it depends on %t"
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


let context_abstract ~loc ctx xs ts =
  mk_abstractable ~loc ctx xs >>= fun (ctx,ys,es) ->
  let ctx = Context.abstract ~loc ctx xs ts in
  return (ctx,ys,es)

