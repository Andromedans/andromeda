(** Conversion to JSON *)

open Nucleus_types

let assumptions { free_var ; free_meta ; bound_var } =
  let free =
    if Nonce.map_is_empty free_var
    then []
    else [("free", Nonce.Json.map free_var)]
  and meta =
    if Nonce.map_is_empty free_meta
    then []
    else [("meta", Nonce.Json.map free_meta)]
  and bound =
    if Bound_set.is_empty bound_var
    then []
    else [("bound", Json.List (List.map (fun k -> Json.Int k) (Bound_set.elements bound_var)))]
  in
  Json.record (free @ meta @ bound)

let rec is_term e =
  let e =
    match e with

    | TermAtom {atom_nonce=x; atom_type=t} -> Json.tag "TermAtom" [Nonce.Json.nonce x; is_type t]

    | TermBoundVar b -> Json.tag "TermBoundVar" [Json.Int b]

    | TermConstructor (c, lst) -> Json.tag "TermConstructor" (Ident.Json.ident c :: arguments lst)

    | TermMeta ({meta_nonce; _}, lst) ->
       Json.tag "TermMeta" (Nonce.Json.nonce meta_nonce :: (List.map is_term lst))

    | TermConvert (e, asmp, t) -> Json.tag "TermConvert" [is_term e; assumptions asmp; is_type t]

  in Json.tag "IsTerm" [e]

and is_type t =
  let t =
    match t with
    | TypeConstructor (c, lst) -> Json.tag "TypeConstructor" (Ident.Json.ident c :: arguments lst)
    | TypeMeta ({meta_nonce; _}, lst) ->
       Json.tag "TypeMeta" (Nonce.Json.nonce meta_nonce :: (List.map is_term lst))
  in Json.tag "IsType" [t]

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
  | BoundaryIsType abstr ->
     Json.tag "BoundaryIsType" []

  | BoundaryIsTerm t ->
     Json.tag "BoundaryIsTerm" [is_type t]

  | BoundaryEqType (t1, t2) ->
     Json.tag "BoundaryIsType" [is_type t1; is_type t2]

  | BoundaryEqTerm (e1, e2, t) ->
     Json.tag "BoundaryEqTerm" [is_term e1; is_term e2; is_type t]

let judgement_abstraction abstr = Json.List (abstraction judgement [] abstr)

let boundary_abstraction abstr = Json.List (abstraction boundary [] abstr)
