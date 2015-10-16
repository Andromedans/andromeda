type renaming = (Name.atom * Name.atom) list

module AtomMap = Map.Make (struct
                      type t = Name.atom
                      let compare = Name.compare_atom
                    end)

module AtomSet = Set.Make (struct
                    type t = Name.atom
                    let compare = Name.compare_atom
                  end)


(* A context is a map which assigns to an atom its type and the set of atoms that depend
   on it. We can think of it as a directed graph whose vertices are the atoms, labelled by
   the type, and the set of atoms are the *incoming* edges. *)
type t = (Tt.ty * AtomSet.t) AtomMap.t

let empty = AtomMap.empty

let print_dependencies deps ppf =
  if not !Config.print_dependencies || AtomSet.is_empty deps
  then Format.fprintf ppf ""
  else Format.fprintf ppf "@ [%t]"
                      (Print.sequence Name.print_atom "," (AtomSet.elements deps))

let print_entry ppf x (t, deps) =
  Format.fprintf ppf "%t : @[<hov>%t@ @[<h>%t@]@]@ "
    (Name.print_atom x)
    (Tt.print_ty [] t)
    (print_dependencies deps)

let print ctx ppf =
  Format.pp_open_vbox ppf 0 ;
  AtomMap.iter (print_entry ppf) ctx ;
  Format.pp_close_box ppf ()

let lookup x (ctx : t) =
  try Some (AtomMap.find x ctx)
  with Not_found -> None

let lookup_ty x ctx =
  match lookup x ctx with None -> None | Some (t, _) -> Some t

let cone ctx x (t : Tt.ty) =
  let y = Name.fresh x in
  let ctx = AtomMap.map (fun (u, deps) -> (u, AtomSet.add y deps)) ctx in
  let ctx = AtomMap.add y (t, AtomSet.empty) ctx in
  y, ctx


let abstract1 ~loc (ctx : t) x =
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
       let deps = AtomSet.elements deps in
       Error.runtime
         ~loc "cannot abstract %t because %t depend%s on it.\nContext:@ %t"
                     (Name.print_atom x)
                     (Print.sequence (Name.print_atom) "," deps)
                     (match deps with [_] -> "s" | _ -> "")
                     (print ctx)

let abstract ~loc ctx xs = List.fold_left (abstract1 ~loc) ctx xs

let rename (ctx : t) s =
  let a_s, b_s = List.split s in
  AtomMap.fold
    (fun a (t, deps) ctx ->
       let b = try List.assoc a s with Not_found -> a
       and t = Tt.abstract_ty a_s 0 t |> Tt.unabstract_ty b_s 0
       and deps =
         AtomSet.fold
           (fun x deps -> AtomSet.add (try List.assoc x s with Not_found -> x) deps)
           deps AtomSet.empty
       in
       let r = AtomMap.add b (t, deps) ctx in r)
    ctx
    empty

let refresh ctx =
  let a_s = AtomMap.bindings ctx |> List.map fst in
  let b_s = List.map Name.refresh_atom a_s in
  (rename ctx (List.combine a_s b_s),
   (List.combine b_s a_s))


let substitute ctx a e = failwith "todo"


let join ctx1 ctx2 =
  let rec fold (ctx : t) eqs handled = function
    | [] -> ctx, eqs, handled
    | x :: xs ->
       if AtomSet.mem x handled then
         ctx, eqs, handled
       else
         let t, deps, eqs =
           match lookup x ctx1, lookup x ctx2 with
           | None, None -> assert false
           | Some (t, deps), None
           | None, Some (t, deps) -> t, deps, eqs
           | Some (t1, deps1), Some (t2, deps2) ->
              t1, AtomSet.union deps1 deps2, (x, t1, t2) :: eqs in
         let handled = AtomSet.add x handled in

         let ctx, eqs, handled = fold ctx eqs handled (AtomSet.elements deps) in

         let deps = AtomSet.fold
             (fun y deps_of_x -> match lookup y ctx with
               | None -> assert false
               | Some (_, deps_of_y) -> AtomSet.union deps_of_y deps_of_x)
             deps
             deps in
         let ctx = AtomMap.add x (t, deps) ctx in
         fold ctx eqs handled xs
  in
  let xs = (AtomMap.fold (fun x _ xs -> x :: xs) ctx2 []) in
  let ctx, eqs, handled = fold ctx1 [] AtomSet.empty xs in
  ctx, eqs
