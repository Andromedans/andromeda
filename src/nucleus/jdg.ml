module AtomSet = Name.AtomSet
module AtomMap = Name.AtomMap

(* A Ctx is a map which assigns to an atom its type and the dependencies and dependants respectively.
   We can think of it as a directed graph whose vertices are the atoms, labelled by
   the type, and the sets of atoms are the two directions of edges. *)

type node =
  { ty : Tt.ty; (* type of x *)
    needed_by : AtomSet.t } (* atoms which depend on x *)

type ctx = node AtomMap.t

type error =
  | AbstractDependency of Name.atom * Name.atom list
  | AbstractInvalidType of Name.atom * Tt.ty * Tt.ty
  | InvalidJoin of ctx * ctx * Name.atom
  | SubstitutionDependency of Name.atom * Tt.term * Name.atom
  | SubstitutionInvalidType of Name.atom * Tt.ty * Tt.ty
  | InvalidApplication
  | InvalidEquality
  | NotAType

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

module Ctx = struct
  type t = ctx

  let empty = AtomMap.empty

  let is_empty = AtomMap.is_empty

  let print_dependencies ~printer s v ppf =
    if not !Config.print_dependencies || AtomSet.is_empty v
    then Format.fprintf ppf ""
    else Format.fprintf ppf "@ %s[%t]" s
                        (Print.sequence (Name.print_atom ~printer) "," (AtomSet.elements v))

  let print_entry ~penv ppf x {ty; needed_by;} =
    Format.fprintf ppf "%t : @[<hov>%t@ @[<h>%t@]@]@ "
      (Name.print_atom ~printer:(penv.Tt.atoms) x)
      (Tt.print_ty ~penv ty)
      (print_dependencies ~printer:(penv.Tt.atoms) "needed_by" needed_by)

  let print ~penv ctx ppf =
    Format.pp_open_vbox ppf 0 ;
    AtomMap.iter (print_entry ~penv ppf) ctx ;
    Format.pp_close_box ppf ()

  let lookup x (ctx : t) =
    try Some (AtomMap.find x ctx)
    with Not_found -> None

  let lookup_ty x ctx =
    match lookup x ctx with None -> None | Some {ty;_} -> Some ty

  let is_subset ctx yts =
    AtomMap.fold
      (fun x node ok ->
       ok && 
       (try
           let t' = List.assoc x yts in
           Tt.alpha_equal_ty t' node.ty
        with Not_found -> false))
      ctx true

  let recursive_assumptions ctx aset =
    let rec fold visited = function
      | [] -> visited
      | x::rem ->
        if AtomSet.mem x visited
        then fold visited rem
        else
          let visited = AtomSet.add x visited in
          let {ty;_} = AtomMap.find x ctx in
          let aset = Tt.assumptions_ty ty in
          let rem = List.rev_append (AtomSet.elements aset) rem in
          fold visited rem
    in
    fold AtomSet.empty (AtomSet.elements aset)

  let add_fresh ctx x ty =
    let y = Name.fresh x in
    let aset = Tt.assumptions_ty ty in
    let needs = recursive_assumptions ctx aset in
    let ctx = AtomMap.mapi (fun z node ->
                            if AtomSet.mem z needs
                            then {node with needed_by = AtomSet.add y node.needed_by}
                            else node)
                           ctx
    in
    y, AtomMap.add y {ty;needed_by = AtomSet.empty;} ctx

  let restrict ctx aset =
    let domain = recursive_assumptions ctx aset in
    let res = AtomMap.fold (fun x node res ->
        if AtomSet.mem x domain
        then
          AtomMap.add x {node with needed_by = AtomSet.inter node.needed_by domain} res
        else res)
      ctx empty
    in
    res

  let abstract ~loc (ctx : t) x ty =
    match lookup x ctx with
    | None ->
       ctx
    | Some node ->
      if Tt.alpha_equal_ty node.ty ty
      then
        if AtomSet.is_empty node.needed_by
        then
          let ctx = AtomMap.remove x ctx in
          let ctx = AtomMap.map (fun node -> {node with needed_by = AtomSet.remove x node.needed_by}) ctx in
          ctx
        else
          let needed_by_l = AtomSet.elements node.needed_by in
          error ~loc (AbstractDependency (x, needed_by_l))
      else
        error ~loc (AbstractInvalidType (x, ty, node.ty))

  let join ~loc ctx1 ctx2 =
    AtomMap.fold (fun x node res ->
        match lookup x res with
          | Some node' ->
            if Tt.alpha_equal_ty node.ty node'.ty
            then
              (* for every node which needs x and is only in ctx2, we need to add it as a dependent. *)
              let extra = AtomSet.fold (fun y extra ->
                  if AtomMap.mem y ctx1
                  then extra
                  else AtomSet.add y extra)
                node.needed_by AtomSet.empty
              in
              if AtomSet.is_empty extra
              then res
              else AtomMap.add x {node' with needed_by = AtomSet.union node'.needed_by extra} res
            else
              error ~loc (InvalidJoin (ctx1, ctx2, x))
          | None ->
            (* dependencies are handled above *)
            AtomMap.add x node res)
      ctx2 ctx1

  let subst_ty ty x e =
    let ty = Tt.abstract_ty [x] ty in
    let ty = Tt.instantiate_ty [e] ty in
      ty

  (* substitute x by e in ctx *)
  let substitute ~loc x (ctx,e,t) =
    match lookup x ctx with
      | Some xnode ->
        if Tt.alpha_equal_ty xnode.ty t
        then
          (* NB: rec_assumptions(t) <= rec_assumptions(e) *)
          let deps = recursive_assumptions ctx (Tt.assumptions_term e) in
          let ctx = AtomSet.fold (fun y ctx ->
              let ynode = AtomMap.find y ctx in
              if AtomSet.mem y deps
              then
                error ~loc (SubstitutionDependency (x, e, y))
              else
                let ty = subst_ty ynode.ty x e in
                AtomMap.add y {ynode with ty} ctx)
            xnode.needed_by ctx
          in
          let ctx = AtomSet.fold (fun z ctx ->
              let znode = AtomMap.find z ctx in
              let needed_by = AtomSet.union znode.needed_by xnode.needed_by in
              AtomMap.add z {znode with needed_by} ctx)
            deps ctx
          in
          if AtomSet.mem x deps
          then ctx
          else
            (* we can remove x *)
            let ctx = AtomMap.remove x ctx in
            let ctx = AtomMap.map (fun node -> {node with needed_by = AtomSet.remove x node.needed_by}) ctx in
            ctx
        else
          error ~loc (SubstitutionInvalidType (x, xnode.ty, t))
      | None -> ctx


  let elements ctx =
    let rec process x ((handled, _) as handled_ys) =
      if AtomSet.mem x handled
      then handled_ys
      else
        let {needed_by;ty} = AtomMap.find x ctx in
        let (handled, xts) = AtomSet.fold process needed_by handled_ys  in
        (AtomSet.add x handled, (x,ty) :: xts)
    in
    let _, xts = AtomMap.fold (fun x _ -> process x) ctx (AtomSet.empty, []) in
    xts

end

type term = Term of Ctx.t * Tt.term * Tt.ty

type atom = JAtom of Ctx.t * Name.atom * Tt.ty

type ty = Ty of Ctx.t * Tt.ty

module Env = struct
  module ConstantMap = Name.IdentMap

  type t = {
    constants : Tt.ty ConstantMap.t;
  }

  let empty = {
    constants = ConstantMap.empty;
  }

  let constant_type c env =
    ConstantMap.find c env.constants

  let add_constant c t env =
    {constants = ConstantMap.add c t env.constants}

end

let print_error ~penv err ppf = match err with
  | InvalidApplication -> Format.fprintf ppf "Invalid application."

  | InvalidEquality -> Format.fprintf ppf "Invalid equality."

  | NotAType -> Format.fprintf ppf "Not a type."

  | AbstractDependency (x, needed_by_l) ->
     Format.fprintf ppf "cannot abstract@ %t@ because@ %t@ depend%s on it"
          (Name.print_atom ~printer:penv.Tt.atoms x)
          (Print.sequence (Name.print_atom ~printer:penv.Tt.atoms) "," needed_by_l)
          (match needed_by_l with [_] -> "s" | _ -> "")

  | AbstractInvalidType (x, t1, t2) ->
     Format.fprintf ppf "cannot abstract@ %t@ with type@ %t@ because it must have type@ %t"
        (Name.print_atom ~printer:penv.Tt.atoms x)
        (Tt.print_ty ~penv t1)
        (Tt.print_ty ~penv t2)

  | InvalidJoin (ctx1, ctx2, x) ->
     Format.fprintf ppf "cannot join contexts@ %t and@ %t at %t"
                    (Ctx.print ~penv ctx1)
                    (Ctx.print ~penv ctx2)
                    (Name.print_atom ~printer:penv.Tt.atoms x)

  | SubstitutionDependency (x, e, y) ->
     Format.fprintf ppf "cannot substitute@ %t@ with@ %t,@ dependency cycle at@ %t"
                (Name.print_atom ~printer:penv.Tt.atoms x)
                (Tt.print_term ~penv e)
                (Name.print_atom ~printer:penv.Tt.atoms y)

  | SubstitutionInvalidType (x, x_ty, t) ->
     Format.fprintf ppf "cannot substitute term of type %t for %t of type %t"
                    (Tt.print_ty ~penv t)
                    (Name.print_atom ~printer:penv.Tt.atoms x)
                    (Tt.print_ty ~penv x_ty)

(** Judgements *)

let typeof (Term (ctx, _, t)) =
  Ty (ctx, t)

let mk_atom ctx x =
  match Ctx.lookup_ty x ctx with
    | Some t -> JAtom (ctx,x,t)
    | None -> assert false

let atom_ty (JAtom (ctx,x,t)) =
  Ty (ctx,t)

let atom_term ~loc (JAtom (ctx,x,t)) =
  Term (ctx,Tt.mk_atom ~loc x,t)

let term_of_ty (Ty (ctx,Tt.Ty ({Tt.loc=loc;_} as t))) = Term (ctx,t,Tt.mk_type_ty ~loc)

let mk_term ctx e t = Term (ctx, e, t)

let mk_ty ctx t = Ty (ctx, t)

let ty_ty = Ty (Ctx.empty, Tt.typ)

let strengthen (Term (ctx,e,t)) =
  let hyps = Name.AtomSet.union (Tt.assumptions_term e) (Tt.assumptions_ty t) in
  let ctx = Ctx.restrict ctx hyps in
  Term (ctx,e,t)

let print_term ~penv ?max_level (Term (ctx, e, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hv>@[<hov>%t@]@;<1 -2>: @[<hov>%t@]@]"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (Tt.print_term ~penv ~max_level:Level.highest e)
              (Tt.print_ty ~penv ~max_level:Level.highest t)

let print_ty ~penv ?max_level (Ty (ctx, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hov>%t@]@ type"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (Tt.print_ty ~penv ~max_level:Level.highest t)

(** Destructors *)
type 'a abstraction = atom * 'a

type shape =
  | Type
  | Atom of atom
  | Constant of Name.constant
  | Prod of ty abstraction
  | Lambda of term abstraction
  | Apply of term * term
  | Eq of term * term
  | Refl of term

let mk_fresh x (Ty (ctx,a)) =
  let y,ctx = Ctx.add_fresh ctx x a in
  ctx,y,JAtom (ctx,y,a)

let shape ~loc (Term (ctx,e,t)) =
  match e.Tt.term with
    | Tt.Type -> Type

    | Tt.Atom x -> Atom (mk_atom ctx x)

    | Tt.Constant c -> Constant c

    | Tt.Prod ((x,a),b) ->
      let ja = mk_ty ctx a in
      let ctx,y,jy = mk_fresh x ja in
      let b = Tt.unabstract_ty [y] b in
      let jb = mk_ty ctx b in
      Prod (jy,jb)

    | Tt.Lambda ((x,a),(e,b)) ->
      let ja = mk_ty ctx a in
      let ctx,y,jy = mk_fresh x ja in
      let b = Tt.unabstract_ty [y] b
      and e = Tt.unabstract [y] e in
      let je = mk_term ctx e b in
      Lambda (jy,je)


    | Tt.Apply (e1,((x,a),b),e2) ->
      let je2 = mk_term ctx e2 a in
      let prod = Tt.mk_prod_ty ~loc:e.Tt.loc x a b in
      let je1 = mk_term ctx e1 prod in
      Apply (je1,je2)

    | Tt.Eq (a,e1,e2) ->
      let je1 = mk_term ctx e1 a
      and je2 = mk_term ctx e2 a in
      Eq (je1,je2)

    | Tt.Refl (a,e) ->
      let e = mk_term ctx e a in
      Refl e

    | Tt.Bound _ -> assert false

let shape_ty ~loc j = shape ~loc (term_of_ty j)

(** Construct judgements *)
let form ~loc env = function
  | Type ->
    Term (Ctx.empty, Tt.mk_type ~loc, Tt.mk_type_ty ~loc)

  | Atom x -> atom_term ~loc x

  | Constant c ->
    let t = Env.constant_type c env in
    Term (Ctx.empty,Tt.mk_constant ~loc c,t)

  | Prod ((JAtom (ctxa,x,a)),(Ty (ctxb,b))) ->
    let ctx = Ctx.join ~loc ctxb ctxa in
    let ctx = Ctx.abstract ~loc ctx x a in
    let b = Tt.abstract_ty [x] b in
    Term (ctx,Tt.mk_prod ~loc (Name.ident_of_atom x) a b,Tt.mk_type_ty ~loc)

  | Lambda ((JAtom (ctxa,x,a)),(Term (ctxe,e,b))) ->
    let ctx = Ctx.join ~loc ctxe ctxa in
    let ctx = Ctx.abstract ~loc ctx x a in
    let b = Tt.abstract_ty [x] b
    and e = Tt.abstract [x] e in
    let x = Name.ident_of_atom x in
    Term (ctx,Tt.mk_lambda ~loc x a e b,Tt.mk_prod_ty ~loc x a b)

  | Apply (Term (ctx1,e1,t1), Term (ctx2,e2,t2)) ->
    let ctx = Ctx.join ~loc ctx2 ctx1 in
    let Tt.Ty te1 = t1 in
    begin match te1.Tt.term with
      | Tt.Prod ((x,a),b) ->
        if Tt.alpha_equal_ty a t2
        then
          let out = Tt.instantiate_ty [e2] b in
          Term (ctx,Tt.mk_apply ~loc e1 x a b e2,out)
        else
          error ~loc InvalidApplication
      | _ -> error ~loc InvalidApplication
    end

  | Eq (Term (ctx1,e1,t1), Term (ctx2,e2,t2)) ->
    let ctx = Ctx.join ~loc ctx2 ctx1 in
    if Tt.alpha_equal_ty t1 t2
    then
      Term (ctx, Tt.mk_eq ~loc t1 e1 e2, Tt.mk_type_ty ~loc)
    else
      error ~loc InvalidEquality

  | Refl (Term (ctx,e,t)) ->
    Term (ctx,Tt.mk_refl ~loc t e,Tt.mk_eq_ty ~loc t e e)

let is_ty (Term (ctx,e,t)) =
  if Tt.alpha_equal_ty t Tt.typ
  then
    Ty (ctx,Tt.ty e)
  else
    error ~loc:e.Tt.loc NotAType

let form_ty ~loc env s =
  is_ty (form ~loc env s)

