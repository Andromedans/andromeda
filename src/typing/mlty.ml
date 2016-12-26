type meta = int

type param = int

module MetaSet = Set.Make(struct
  type t = meta
  let compare = compare
  end)

let fresh_meta : unit -> meta =
  let counter = ref 0 in
  fun () ->
    let m = !counter in
    incr counter;
    m

let fresh_param : unit -> param =
  let counter = ref 0 in
  fun () ->
    let p = !counter in
    incr counter;
    p

module MetaOrd = struct
  type t = meta

  let compare = compare
end

type ty =
  | Judgment
  | String
  | Meta of meta
  | Param of param
  | Prod of ty list
  | Arrow of ty * ty
  | Handler of ty * ty
  | App of Name.ident * Dsyntax.level * ty list
  | Ref of ty
  | Dynamic of ty

let unit_ty = Prod []

let fresh_type () = Meta (fresh_meta ())

(** Type parameters are generalised in the following values. *)
type 'a forall = param list * 'a

type ty_schema = ty forall

type constructor = Name.constructor * ty list

type ty_def =
  | Alias of ty forall
  | Sum of constructor list forall

type error =
  | InvalidApplication of ty * ty * ty
  | TypeMismatch of ty * ty
  | UnsolvedApp of ty * ty * ty
  | HandlerExpected of ty
  | RefExpected of ty
  | DynamicExpected of ty
  | UnknownExternal of string
  | ValueRestriction
  | Ungeneralizable of param list * ty

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

type print_env = {
  mutable metas : (meta * string) list ;
  mutable params : (param * string) list
}

let fresh_penv () = { metas = []; params = [] }

let print_meta ~penv (m : meta) ppf =
  let s =
    try List.assoc m penv.metas
    with Not_found ->
      let l = List.length penv.metas in
      let s = Name.greek l in
      penv.metas <- (m, s) :: penv.metas;
      s
  in
  Format.fprintf ppf "?%s" s

let print_param ~penv (p : param) ppf =
  let s =
    try List.assoc p penv.params
    with Not_found ->
      let l = List.length penv.params in
      let s = Name.greek l in
      penv.params <- (p, s) :: penv.params;
      s
  in
  Format.fprintf ppf "%s" s

let rec print_ty ~penv ?max_level t ppf =
  match t with

  | Judgment -> Format.fprintf ppf "judgment"

  | String -> Format.fprintf ppf "mlstring"

  | Meta m -> print_meta ~penv m ppf

  | Param p -> print_param ~penv p ppf

  | Prod [] -> Format.fprintf ppf "mlunit"

  | Prod ts -> Print.print ?max_level ~at_level:Level.ml_prod ppf "%t"
                 (Print.sequence (print_ty ~penv ~max_level:Level.ml_prod_arg) " *" ts)

  | Arrow (t1, t2) ->
     Print.print ?max_level ~at_level:Level.ml_arr ppf "@[%t@ %s@ %t@]"
                 (print_ty ~penv ~max_level:(Level.ml_arr_left) t1)
                 (Print.char_arrow ())
                 (print_ty ~penv ~max_level:(Level.ml_arr_right) t2)

  | Handler (t1, t2) ->
     Print.print ?max_level ~at_level:(Level.ml_handler) ppf "@[%t@ %s@ %t@]"
                 (print_ty ~penv ~max_level:(Level.ml_handler_left) t1)
                 (Print.char_darrow ())
                 (print_ty ~penv ~max_level:(Level.ml_handler_right) t2)

  | App (x, _, []) ->
     Format.fprintf ppf "%t" (Name.print_ident x)

  | App (x, _, ts) ->
     Print.print ?max_level ~at_level:Level.ml_app ppf "@[<hov>%t@ %t@]"
                 (Name.print_ident x)
                 (Print.sequence (print_ty ~penv ~max_level:Level.ml_app_arg) "" ts)

  | Ref t -> Print.print ?max_level ~at_level:Level.ml_app ppf "@[ref@ %t@]"
                        (print_ty ~penv ~max_level:Level.ml_app_arg t)

  | Dynamic t -> Print.print ?max_level~at_level:Level.ml_app ppf "@[dynamic@ %t@]"
                        (print_ty ~penv ~max_level:Level.ml_app_arg t)

let print_ty_schema ~penv ?max_level (ms, t) ppf =
  match ms with
    | [] ->
      print_ty ~penv ?max_level t ppf
    | _ :: _ ->
      Format.fprintf ppf "@[<hov>%s %t, %t@]"
                     (Print.char_forall ())
                     (Print.sequence (print_param ~penv) "" ms)
                     (print_ty ~penv ~max_level:Level.ml_forall_r t)

let print_error err ppf =
  let penv = fresh_penv () in
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
  | RefExpected t ->
    Format.fprintf ppf "Expected a reference but got %t"
      (print_ty ~penv t)
  | DynamicExpected t ->
    Format.fprintf ppf "Expected a dynamic but got %t"
      (print_ty ~penv t)
  | UnknownExternal s ->
    Format.fprintf ppf "Unknown external %s" s
  | ValueRestriction ->
     Format.fprintf ppf "This computation cannot be polymorphic (value restriction)"
  | Ungeneralizable (ps, ty) ->
     Format.fprintf ppf "Cannot generalize %t in %t"
                    (Print.sequence (print_param ~penv) "," ps)
                    (print_ty ~penv ty)

let rec occurs m = function
  | Judgment | String | Param _ -> false
  | Meta m' -> m = m'
  | Prod ts  | App (_, _, ts) ->
    List.exists (occurs m) ts
  | Arrow (t1, t2) | Handler (t1, t2) ->
    occurs m t1 || occurs m t2
  | Ref t | Dynamic t -> occurs m t

let rec occuring = function
  | Judgment | String | Param _ -> MetaSet.empty
  | Meta m -> MetaSet.singleton m
  | Prod ts  | App (_, _, ts) ->
    List.fold_left (fun s t -> MetaSet.union s (occuring t)) MetaSet.empty ts
  | Arrow (t1, t2) | Handler (t1, t2) ->
    MetaSet.union (occuring t1) (occuring t2)
  | Ref t | Dynamic t -> occuring t

let occuring_schema ((_, t) : ty_schema) : MetaSet.t =
  occuring t

let instantiate pus t =
  let rec inst = function

    | Judgment | String | Meta _ as t -> t

    | Param p as t ->
       begin
         try
           List.assoc p pus
         with Not_found -> t
       end

    | Prod ts ->
       let ts = List.map inst ts in
       Prod ts

    | Arrow (t1, t2) ->
       let t1 = inst t1
       and t2 = inst t2 in
       Arrow (t1, t2)

    | Handler (t1, t2) ->
       let t1 = inst t1
       and t2 = inst t2 in
       Handler (t1, t2)

    | App (x, lvl, ts) ->
       let ts = List.map inst ts in
       App (x, lvl, ts)

    | Ref t ->
       let t = inst t in
       Ref t

    | Dynamic t ->
       let t = inst t in
       Dynamic t

  in
  inst t

let params_occur ps t =
  let rec occurs = function
  | Judgment | String | Meta _ -> false
  | Param p -> List.mem p ps
  | Prod ts  | App (_, _, ts) ->
    List.exists occurs ts
  | Arrow (t1, t2) | Handler (t1, t2) ->
    occurs t1 || occurs t2
  | Ref t | Dynamic t -> occurs t
  in
  occurs t
