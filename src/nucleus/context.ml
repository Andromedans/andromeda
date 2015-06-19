(** Typing context and runtime environment *)

module HintMap = Map.Make(struct
    type t = Pattern.hint_key
    let compare = Pervasives.compare
  end)
module GeneralMap = Map.Make(struct
    type t = Pattern.hint_key * Pattern.hint_key * Pattern.hint_key
    let compare = Pervasives.compare
  end)

(** A context holds free variables with their types and an
    environment of runtime bindings. *)
type t = {
  free : (Name.t * Tt.ty) list;
  primitive : (Name.t * Tt.primsig) list;
  bound : (Name.t * Value.value) list;
  beta : Pattern.beta_hint list HintMap.t;
  eta : Pattern.eta_hint list HintMap.t;
  general : Pattern.general_hint list GeneralMap.t;
  inhabit : Pattern.inhabit_hint list;
  files : string list;
}

(** The empty context *)
let empty = {
  free = [];
  primitive = [];
  bound = [] ;
  beta = HintMap.empty ;
  eta = HintMap.empty ;
  general = GeneralMap.empty ;
  inhabit = [] ;
  files = [] ;
}

let find k hs = try HintMap.find k hs with Not_found -> []
let find3 k hs = try GeneralMap.find k hs with Not_found -> []

let eta_hints key {eta=hints} = find key hints

let beta_hints key {beta=hints} = find key hints

let general_hints key {general=hints} = find3 key hints

let inhabit_hints {inhabit=lst} = lst

let bound_names {bound=lst} = List.map fst lst

let primitives {primitive=lst} =
  List.map (fun (x, (yts, _)) -> (x, List.length yts)) lst

let used_names ctx =
  List.map fst ctx.free @ List.map fst ctx.bound @ List.map fst ctx.primitive

let lookup_free x {free=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq x y then Some v else lookup lst
  in
    lookup lst

let lookup_primitive x {primitive=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq x y then Some v else lookup lst
  in
    lookup lst

let lookup_bound k {bound=lst} =
  try
    snd (List.nth lst k)
  with
  | Failure _ -> Error.impossible "invalid de Bruijn index %d" k

let is_bound x ctx =
  match lookup_free x ctx with
  | None ->
    begin match lookup_primitive x ctx with
      | None -> false
      | Some _ -> true
    end
  | Some _ -> true

let add_free x t ctx =
  if is_bound x ctx
  then Error.runtime "%t already exists" (Name.print x)
  else { ctx with free = (x,t) :: ctx.free }

let add_primitive x ytsu ctx =
  if is_bound x ctx
  then Error.runtime "%t already exists" (Name.print x)
  else { ctx with primitive = (x, ytsu) :: ctx.primitive }

let add_beta (key, h) ctx =
  { ctx with
    beta =
      let l = find key ctx.beta in
      HintMap.add key (h :: l) ctx.beta
  }

let add_eta (key, h) ctx =
  { ctx with
    eta =
      let l = find key ctx.eta in
      HintMap.add key (h :: l) ctx.eta
  }

let add_general (key, h) ctx =
  { ctx with
    general =
      let l = find3 key ctx.general in
      GeneralMap.add key (h :: l) ctx.general
  }

let add_inhabit h ctx = { ctx with inhabit = h :: ctx.inhabit }

let add_fresh x t ctx =
  let y = Name.fresh x
  in y, { ctx with free = (y,t) :: ctx.free }

let add_bound x v ctx =
  { ctx with bound = (x, v) :: ctx.bound }

let add_file f ctx =
  { ctx with files = (Filename.basename f) :: ctx.files }

let included f { files } = List.mem (Filename.basename f) files

let print ctx ppf =
  let forbidden_names = used_names ctx in
  Print.print ppf "---CONTEXT---@." ;
  List.iter
    (fun (x, t) ->
     Print.print ppf "@[<hov 4>Parameter %t@;<1 -2>%t@]@\n" (Name.print x)
       (Tt.print_primsig forbidden_names t))
    (List.rev ctx.primitive) ;
  Print.print ppf "-----END-----@."
