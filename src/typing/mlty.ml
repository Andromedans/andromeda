type meta = int

let fresh_meta : unit -> meta =
  let counter = ref 0 in
  fun () ->
    let m = !counter in
    incr counter;
    m

module MetaOrd = struct
  type t = meta

  let compare = compare
end

type ty =
  | Jdg
  | String
  | Meta of meta
  | Prod of ty list
  | Arrow of ty * ty
  | Handler of ty * ty
  | App of Name.ident * Syntax.level * ty list
  | Ref of ty

let unit_ty = Prod []

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
  | RefExpected of ty
  | UnknownExternal of string

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

type print_env = (meta * string) list ref

let fresh_penv () = ref []

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

  | Jdg -> Format.fprintf ppf "judgment"

  | String -> Format.fprintf ppf "string"

  | Meta m -> print_meta ~penv m ppf

  | Prod [] -> Format.fprintf ppf "unit"

  | Prod ts -> Print.print ?max_level ppf "%t"
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

  | App (x, _, []) ->
     Format.fprintf ppf "%t" (Name.print_ident x)

  | App (x, _, ts) ->
     Print.print ?max_level ~at_level:Level.ml_app ppf "@[<hov>%t@ %t@]"
                 (Name.print_ident x)
                 (Print.sequence (print_ty ~penv ~max_level:Level.ml_app_arg) "" ts)

  | Ref t -> Print.print ?max_level ~at_level:Level.ml_app ppf "ref@ %t"
                         (print_ty ~penv ~max_level:Level.ml_app_arg t)

let print_ty_schema ~penv ?max_level (ms, t) ppf =
  match ms with
    | [] ->
      print_ty ~penv ?max_level t ppf
    | _ :: _ ->
      Format.fprintf ppf "%s %t, %t"
                     (Print.char_forall ())
                     (Print.sequence (print_meta ~penv) " " ms)
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
  | UnknownExternal s ->
    Format.fprintf ppf "Unknown external %s" s

let rec occurs m = function
  | Jdg | String -> false
  | Meta m' -> m = m'
  | Prod ts  | App (_, _, ts) ->
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
  | Prod ts  | App (_, _, ts) ->
    List.fold_left (fun s t -> MetaSet.union s (occuring t)) MetaSet.empty ts
  | Arrow (t1, t2) | Handler (t1, t2) ->
    MetaSet.union (occuring t1) (occuring t2)
  | Ref t -> occuring t

let occuring_schema ((ms, t) : ty_schema) : MetaSet.t =
  let s = occuring t in
  List.fold_left (fun s m -> MetaSet.remove m s) s ms
