(** Conversion to JSON *)

open Nucleus_types

let assumptions { free_var ; free_meta ; bound_var ; bound_meta } =
  let free_var =
    if Nonce.map_is_empty free_var
    then []
    else [("free_var", Nonce.Json.map free_var)]
  and free_meta =
    if Nonce.map_is_empty free_meta
    then []
    else [("free_meta", Nonce.Json.map free_meta)]
  and bound_var =
    if Bound_set.is_empty bound_var
    then []
    else [("bound_var", Json.List (List.map (fun k -> Json.Int k) (Bound_set.elements bound_var)))]
  and bound_meta =
    if Bound_set.is_empty bound_meta
    then []
    else [("bound_meta", Json.List (List.map (fun k -> Json.Int k) (Bound_set.elements bound_meta)))]
  in
  Json.record (free_var @ free_meta @ bound_var @ bound_meta)

let rec is_term e =
  let e =
    match e with

    | TermAtom {atom_nonce=x; atom_type=t} -> Json.tag "TermAtom" [Nonce.Json.nonce x; is_type t]

    | TermBoundVar b -> Json.tag "TermBoundVar" [Json.Int b]

    | TermConstructor (c, lst) -> Json.tag "TermConstructor" (Ident.Json.ident c :: arguments lst)

    | TermMeta (mv, lst) ->
       Json.tag "TermMeta" (meta mv :: (List.map is_term lst))

    | TermConvert (e, asmp, t) -> Json.tag "TermConvert" [is_term e; assumptions asmp; is_type t]

  in Json.tag "IsTerm" [e]

and is_type t =
  let t =
    match t with
    | TypeConstructor (c, lst) -> Json.tag "TypeConstructor" (Ident.Json.ident c :: arguments lst)
    | TypeMeta (mv, lst) ->
       Json.tag "TypeMeta" (meta mv :: (List.map is_term lst))
  in Json.tag "IsType" [t]

and meta = function
  | MetaFree {meta_nonce; _} -> Json.tag "MetaFree" [Nonce.Json.nonce meta_nonce]
  | MetaBound k -> Json.tag "MetaBound" [Json.Int k]

and argument arg =
  let rec fold xs = function
  | Arg_Abstract (x, arg) -> fold (x :: xs) arg
  | Arg_NotAbstract jdg ->
     let xs = List.map Name.Json.name (List.rev xs) in
     Json.tag "Argument" [Json.tuple xs ; judgement jdg]
  in
  fold [] arg

and arguments lst = List.map argument lst

and judgement = function
  | JudgementIsType t -> Json.tag "JudgementIsType" [is_type t]
  | JudgementIsTerm e -> Json.tag "JudgementIsTerm" [is_term e]
  | JudgementEqType _ -> Json.tag "JudgementEqType" []
  | JudgementEqTerm _ -> Json.tag "JudgementEqTerm" []

let rec abstraction json_u xts =
    function
    | Abstract (x, t, abstr) ->
       abstraction json_u ((x, t) :: xts) abstr
    | NotAbstract u ->
       let xts = List.map (fun (x, t) -> Json.List [Name.Json.name x; is_type t]) (List.rev xts) in
       [Json.tuple xts ; json_u u]

let boundary = function
  | BoundaryIsType _abstr ->
     Json.tag "BoundaryIsType" []

  | BoundaryIsTerm t ->
     Json.tag "BoundaryIsTerm" [is_type t]

  | BoundaryEqType (t1, t2) ->
     Json.tag "BoundaryIsType" [is_type t1; is_type t2]

  | BoundaryEqTerm (e1, e2, t) ->
     Json.tag "BoundaryEqTerm" [is_term e1; is_term e2; is_type t]

let judgement_abstraction abstr = Json.List (abstraction judgement [] abstr)

let boundary_abstraction abstr = Json.List (abstraction boundary [] abstr)
