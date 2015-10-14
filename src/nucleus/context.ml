module AtomMap = Map.Make (struct
                      type t = Name.atom
                      let compare = Name.compare_atom
                    end)

module AtomSet = Set.Make (struct
                    type t = Name.atom
                    let compare = Name.compare_atom
                  end)

let lookup x ctx =
  try
    Some (AtomMap.find x ctx)
  with Not_found -> None
  
(* A context is a map which assigns to an atom its type and the set of atoms that depend
   on it. We can think of it as a directed graph whose vertices are the atoms, labelled by
   the type, and the set of atoms are the *incoming* edges. *)
type t = (Tt.ty list * AtomSet.t) AtomMap.t

let empty = AtomMap.empty

let cone ctx x (t : Tt.ty) =
  let y = Name.fresh x in
  let ctx = AtomMap.map (fun (u, deps) -> (u, AtomSet.add y deps)) ctx in
  let ctx = AtomMap.add y ([t], AtomSet.empty) ctx in
  y, ctx

let join ctx1 ctx2 = 
  let ctx =
    AtomMap.merge
      (fun x tdeps1 tdeps2 ->
       match tdeps1, tdeps2 with
       | None, None -> None (* XXX this should happen *)
       | Some (ts, deps), None
       | None, Some (ts, deps) -> Some (ts, deps)
       | Some (ts1, deps1), Some (ts2, deps2) ->
          let ts =
            List.fold_left
              (fun ts t -> 
               if List.exists (Tt.alpha_equal_ty t) ts
               then ts
               else t :: ts)
              ts1 ts2
          in
          Some (ts, AtomSet.union deps1 deps2))
      ctx1 ctx2
  in
  let eqs = [] in (* XXX prove a theorem or put in some equations *)
  ctx, eqs

let abstract1 ~loc ctx x =
  match lookup x ctx with
  | None ->
     ctx
  | Some (t, deps) -> 
     if AtomSet.is_empty deps
     then
       let ctx = AtomMap.remove x ctx in
       let ctx = AtomMap.map (fun (t, deps) -> (t, AtomSet.remove x deps)) ctx in
       ctx
     else
       Error.runtime ~loc "cannot abstract %t because %t depend on it"
                     (Name.print_atom x)
                     (Print.sequence (Name.print_atom) "," (AtomSet.elements deps))

let abstract ~loc ctx xs = List.fold_left (abstract1 ~loc) ctx xs

let print ctx (ppf : Format.formatter) =
  if AtomMap.is_empty ctx then
    Print.print ppf ""
  else
    begin
      let equal_char = " " ^ Print.char_equal () in
      AtomMap.iter
        (fun x (ts, deps) ->
         Print.print ppf "%t : [%t] @[%t@]\n"
                       (Name.print_atom x)
                       (Print.sequence Name.print_atom "" (AtomSet.elements deps))
                       (Print.sequence (Tt.print_ty []) equal_char ts)
        )
        ctx ;
      Print.print ppf "----------------------\n"
    end
      
