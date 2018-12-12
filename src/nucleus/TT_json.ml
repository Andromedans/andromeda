(** Conversion to JSON *)

open Jdg_typedefs

module Json =
struct

  let rec term e =
    match e with

      | TermAtom {atom_name=x; atom_type=t} -> Json.tag "TermAtom" [Name.Json.atom x; ty t]

      | TermBound b -> Json.tag "TermBound" [Json.Int b]

      | TermConstructor (c, lst) -> Json.tag "TermConstructor" (Name.Json.ident c :: args lst)

      | TermMeta ({meta_name; _}, lst) ->
         Json.tag "TermMeta" (Name.Json.meta meta_name :: (List.map term lst))

      | TermConvert (e, asmp, t) -> Json.tag "TermConvert" [term e; Assumption.Json.assumptions asmp; ty t]

  and ty = function
      | TypeConstructor (c, lst) -> Json.tag "TypeConstructor" (Name.Json.ident c :: args lst)
      | TypeMeta ({meta_name; _}, lst) ->
         Json.tag "TypeMeta" (Name.Json.meta meta_name :: (List.map term lst))

  and args lst =
    (List.map
       (function
        | ArgIsTerm abstr -> Json.tag "ArgIsTerm" (abstraction term [] abstr)
        | ArgIsType abstr -> Json.tag "ArgIsType" (abstraction ty [] abstr)
        | ArgEqType _ -> Json.tag "ArgIsType" []
        | ArgEqTerm _ -> Json.tag "ArgEqTerm" [])
       lst)

  and abstraction : 'a . ('a -> Json.t) -> (Name.ident * ty) list -> 'a abstraction -> Json.t list =
    fun json_u xts ->
    function
    | Abstract (x, t, abstr) ->
       abstraction json_u ((x,t) :: xts) abstr
    | NotAbstract u ->
       let xts = List.map (fun (x, t) -> Json.List [Name.Json.ident x; ty t])  (List.rev xts) in
       [Json.tuple xts ; json_u u]
end
