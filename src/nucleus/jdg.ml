module AtomSet = Name.AtomSet
module AtomMap = Name.AtomMap

(** Start with the types. *)

(* A Ctx is a map which assigns to an atom its type and the dependencies and dependants respectively.
   We can think of it as a directed graph whose vertices are the atoms, labelled by
   the type, and the sets of atoms are the two directions of edges. *)

type node =
  { ty : Tt.ty; (* type of x *)
    needed_by : AtomSet.t } (* atoms which depend on x *)

type ctx = node AtomMap.t

type term = Term of ctx * Tt.term * Tt.ty

type atom = JAtom of ctx * Name.atom * Tt.ty

type ty = Ty of ctx * Tt.ty

(** The atom set is the hypotheses actually needed to prove the equality.
    Remember that strengthening is controlled by the runtime. *)
type eq_term = EqTerm of ctx * AtomSet.t * Tt.term * Tt.term * Tt.ty

type eq_ty = EqTy of ctx * AtomSet.t * Tt.ty * Tt.ty

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

  let lookup_atom x ctx =
    match lookup x ctx with
      | None -> None
      | Some {ty;_} -> Some (JAtom (ctx, x, ty))

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

  let add_fresh (Ty (ctx, ty)) x =
    let y = Name.fresh x in
    let aset = Tt.assumptions_ty ty in
    let needs = recursive_assumptions ctx aset in
    let ctx = AtomMap.mapi (fun z node ->
                            if AtomSet.mem z needs
                            then {node with needed_by = AtomSet.add y node.needed_by}
                            else node)
                           ctx
    in
    let ctx = AtomMap.add y {ty;needed_by = AtomSet.empty;} ctx in
    JAtom (ctx, y, ty)

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
  let substitute ~loc ctx x (Term (ctxe, e, t)) =
    let ctx = join ~loc ctx ctxe in
    match lookup x ctx with
      | None -> ctx
      | Some xnode ->
        if not (Tt.alpha_equal_ty xnode.ty t)
        then
          error ~loc (SubstitutionInvalidType (x, xnode.ty, t))
        else
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


  let elements ctx =
    let rec process x ((handled, _) as handled_ys) =
      if AtomSet.mem x handled
      then handled_ys
      else
        let {needed_by;ty} = AtomMap.find x ctx in
        let (handled, xts) = AtomSet.fold process needed_by handled_ys  in
        (AtomSet.add x handled, (JAtom (ctx, x, ty)) :: xts)
    in
    let _, xts = AtomMap.fold (fun x _ -> process x) ctx (AtomSet.empty, []) in
    xts

end

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

let atom_ty (JAtom (ctx,x,t)) =
  Ty (ctx,t)

let atom_term ~loc (JAtom (ctx,x,t)) =
  Term (ctx, Tt.mk_atom ~loc x, t)

let term_of_ty (Ty (ctx,Tt.Ty ({Tt.loc=loc;_} as t))) = Term (ctx,t,Tt.mk_type_ty ~loc)

let mk_term ctx e t = Term (ctx, e, t)

let mk_ty ctx t = Ty (ctx, t)

let ty_ty = Ty (Ctx.empty, Tt.typ)

let strengthen (Term (ctx,e,t)) =
  let hyps = Name.AtomSet.union (Tt.assumptions_term e) (Tt.assumptions_ty t) in
  let ctx = Ctx.restrict ctx hyps in
  Term (ctx,e,t)

let occurs (JAtom (_, x, _)) (Term (ctx, _, _)) =
  Ctx.lookup_atom x ctx

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

let print_eq_term ~penv ?max_level (EqTerm (ctx, _, e1, e2, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hv>@[<hov>%t@]@ %s@ @[<hov>%t@]@ :@ @[<hov>%t@]@]"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (Tt.print_term ~penv e1)
              (Print.char_equal ())
              (Tt.print_term ~penv e2)
              (Tt.print_ty ~penv t)

let print_eq_ty ~penv ?max_level (EqTy (ctx, _, t1, t2)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hv>@[<hov>%t@]@ %s@ @[<hov>%t@]@]"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (Tt.print_ty ~penv t1)
              (Print.char_equal ())
              (Tt.print_ty ~penv t2)

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

let shape (Term (ctx,e,t)) =
  match e.Tt.term with
    | Tt.Type -> Type

    | Tt.Atom x ->
      begin match Ctx.lookup_atom x ctx with
        | Some j -> Atom j
        | None -> assert false
      end

    | Tt.Constant c -> Constant c

    | Tt.Prod ((x,a),b) ->
      let ja = mk_ty ctx a in
      let JAtom (ctx, y, _) as jy = Ctx.add_fresh ja x in
      let b = Tt.unabstract_ty [y] b in
      let jb = mk_ty ctx b in
      Prod (jy,jb)

    | Tt.Lambda ((x,a),(e,b)) ->
      let ja = mk_ty ctx a in
      let JAtom (ctx, y, _) as jy = Ctx.add_fresh ja x in
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

let shape_ty j = shape (term_of_ty j)

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

let is_ty ~loc (Term (ctx,e,t)) =
  if Tt.alpha_equal_ty t Tt.typ
  then
    Ty (ctx,Tt.ty e)
  else
    error ~loc NotAType

let form_ty ~loc env s =
  is_ty ~loc (form ~loc env s)

(** Substitution *)
let substitute_ty ~loc (Ty (ctxt, t)) (JAtom (ctxa, a, _)) (Term (_, s, _) as js) =
  let ctxt = Ctx.join ~loc ctxt ctxa in
  let ctxt = Ctx.substitute ~loc ctxt a js in
  let t = Tt.substitute_ty [a] [s] t in
  Ty (ctxt, t)

let substitute ~loc (Term (ctxe, e, t)) (JAtom (_, a, _)) (Term (_, s, _) as js) =
  let ctxe = Ctx.substitute ~loc ctxe a js in
  let t = Tt.substitute_ty [a] [s] t
  and e = Tt.substitute [a] [s] e in
  Term (ctxe, e, t)

(** Conversion *)

type side = LEFT | RIGHT

let eq_term_side side (EqTerm (ctx, _, lhs, rhs, ty)) =
  let term = match side with LEFT -> lhs | RIGHT -> rhs in
  Term (ctx, term, ty)

let eq_term_at_ty (EqTerm (ctx, _, _, _, ty)) =
  Ty (ctx, ty)

let eq_ty_side side (EqTy (ctx, _, lhs, rhs)) : ty =
  let ty = match side with LEFT -> lhs | RIGHT -> rhs in
  Ty (ctx, ty)

let convert ~loc (Term (ctx1, e, t)) (EqTy (ctx2, hyps, t1, t2)) =
  assert (Tt.alpha_equal_ty t t1);
  let ctx = Ctx.join ~loc ctx2 ctx1 in
  let e = Tt.mention_atoms hyps e in
  Term (ctx, e, t2)

let convert_eq ~loc (EqTerm (ctx1, hyps1, e1, e2, ty)) (EqTy (ctx2, hyps2, t1, t2)) =
  assert (Tt.alpha_equal_ty ty t1);
  let e1 = Tt.mention_atoms hyps2 e1
  and e2 = Tt.mention_atoms hyps2 e2
  and ctx = Ctx.join ~loc ctx1 ctx2
  and hyps = AtomSet.union hyps1 hyps2 in
  EqTerm (ctx, hyps, e1, e2, t2)

(** Constructors *)

let reflexivity (Term (ctx, e, t)) =
  let hyps = Tt.assumptions_term e in
  EqTerm (ctx, hyps, e, e, t)

let reflexivity_ty (Ty (ctx, t)) =
  let hyps = Tt.assumptions_ty t in
  EqTy (ctx, hyps, t, t)

let alpha_equal ~loc (Term (ctx1, e1, t1)) (Term (ctx2, e2, t2)) =
  assert (Tt.alpha_equal_ty t1 t2);
  if Tt.alpha_equal e1 e2
  then
    let ctx = Ctx.join ~loc ctx1 ctx2 in
    (* XXX we use just one instead? *)
    let hyps = AtomSet.union (Tt.assumptions_term e1) (Tt.assumptions_term e2) in
    Some (EqTerm (ctx, hyps, e1, e2, t1))
  else
    None

let alpha_equal_ty ~loc (Ty (ctx1, t1)) (Ty (ctx2, t2)) =
  if Tt.alpha_equal_ty t1 t2
  then
    let ctx = Ctx.join ~loc ctx1 ctx2 in
    let hyps = AtomSet.union (Tt.assumptions_ty t1) (Tt.assumptions_ty t2) in
    Some (EqTy (ctx, hyps, t1, t2))
  else
    None

let symmetry_ty (EqTy (ctx, hyps, t1, t2)) = EqTy (ctx, hyps, t2, t1)

let is_type_equality (EqTerm (ctx, hyps, e1, e2, t)) =
  assert (Tt.alpha_equal_ty t Tt.typ);
  EqTy (ctx, hyps, Tt.ty e1, Tt.ty e2)

let reflect (Term (ctx, term, Tt.Ty t)) =
  match t.Tt.term with
    | Tt.Eq (a, e1, e2) ->
      let hyps = Tt.assumptions_term term in
      EqTerm (ctx, hyps, e1, e2, a)
    | _ -> assert false

(** Beta *)

let beta ~loc (EqTy (ctxa, hypsa, a1, a2))
              (JAtom (_, x, _)) (JAtom (_, y, _))
              (EqTy (ctxb, hypsb, b1, b2))
              (Term (ctx1, e1, t1))
              (Term (ctx2, e2, t2)) =
  assert (Tt.alpha_equal_ty b1 t1 && Tt.alpha_equal_ty a2 t2);
  let ctxb = Ctx.abstract ~loc ctxb x a1
  and hypsb = AtomSet.remove x hypsb
  and b1 = Tt.abstract_ty [x] b1
  and e1 = Tt.abstract [x] e1
  and b2 = Tt.abstract_ty [y] (Tt.substitute_ty [x] [Tt.mention_atoms hypsa (Tt.mk_atom ~loc y)] b2) in
  let ctx = Ctx.join ~loc ctxa ctxb
  and hyps = AtomSet.union hypsa hypsb
  and lam = Tt.mk_lambda ~loc (Name.ident_of_atom x) a1 e1 b1
  and e_s = Tt.mention_atoms hypsb (Tt.instantiate [Tt.mention_atoms hypsa e2] e1) in
  let app = Tt.mk_apply ~loc lam (Name.ident_of_atom y) a2 b2 e2
  and ty = Tt.instantiate_ty [e2] b2 in
  EqTerm (ctx, hyps, app, e_s, ty)
  

(** Congruence *)

let congr_prod ~loc (EqTy (ctxa, hypsa, ta1, ta2)) (JAtom (_, x, _)) (JAtom (_, y, _)) (EqTy (ctxb, hypsb, b1, b2)) =
  let ctxb = Ctx.abstract ~loc ctxb x ta1
  and hypsb = AtomSet.remove x hypsb
  and b1 = Tt.abstract_ty [x] b1
  and b2 = Tt.abstract_ty [y] (Tt.substitute_ty [x] [Tt.mention_atoms hypsa (Tt.mk_atom ~loc y)] b2) in
  let ctx = Ctx.join ~loc ctxa ctxb
  and hyps = AtomSet.union hypsa hypsb in
  let lhs = Tt.mk_prod ~loc (Name.ident_of_atom x) ta1 b1
  and rhs = Tt.mk_prod ~loc (Name.ident_of_atom y) ta2 b2 in
  EqTerm (ctx, hyps, lhs, rhs, Tt.typ)

let congr_prod_ty ~loc eq_a x y eq_b =
  is_type_equality (congr_prod ~loc eq_a x y eq_b)

let congr_lambda ~loc (EqTy (ctxa, hypsa, ta1, ta2))
                 (JAtom (_, x, _)) (JAtom (_, y, _))
                 (EqTy (ctxb, hypsb, b1, b2))
                 (EqTerm (ctxe, hypse, e1, e2, ty_e)) =
  assert (Tt.alpha_equal_ty b1 ty_e);
  let ctx = Ctx.join ~loc ctxa (Ctx.abstract ~loc (Ctx.join ~loc ctxb ctxe) x ta1) in
  let hypsb = AtomSet.remove x hypsb
  and hypse = AtomSet.remove x hypse in
  let hypsab = AtomSet.union hypsa hypsb in
  let hyps = AtomSet.union hypsab hypse in
  let y_mentions = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
  let e1 = Tt.abstract [x] e1
  and e2 = Tt.abstract [y] (Tt.substitute [x] [y_mentions] e2)
  and b1 = Tt.abstract_ty [x] b1
  and b2 = Tt.abstract_ty [x] (Tt.substitute_ty [x] [y_mentions] b2) in
  let lhs = Tt.mk_lambda ~loc (Name.ident_of_atom x) ta1 e1 b1
  and rhs = Tt.mention_atoms hypsab (Tt.mk_lambda ~loc (Name.ident_of_atom y) ta2 e2 b2)
  and ty = Tt.mk_prod_ty ~loc (Name.ident_of_atom x) ta1 b1 in
  EqTerm (ctx, hyps, lhs, rhs, ty)

let congr_apply ~loc (EqTy (ctxa, hypsa, ta1, ta2))
                (JAtom (_, x, _)) (JAtom (_, y, _))
                (EqTy (ctxb, hypsb, b1, b2))
                (EqTerm (ctxh, hypsh, h1, h2, ty_h))
                (EqTerm (ctxe, hypse, e1, e2, ty_e)) =
  let y_mentions = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
  let b1 = Tt.abstract_ty [x] b1
  and b2 = Tt.abstract_ty [y] (Tt.substitute_ty [x] [y_mentions] b2)
  and ctxb = Ctx.abstract ~loc ctxb x ta1
  and hypsb = AtomSet.remove x hypsb in
  let prod1 = Tt.mk_prod_ty ~loc (Name.ident_of_atom x) ta1 b1 in
  assert (Tt.alpha_equal_ty prod1 ty_h && Tt.alpha_equal_ty ta1 ty_e);
  let ctx = Ctx.join ~loc ctxa (Ctx.join ~loc ctxb (Ctx.join ~loc ctxh ctxe)) in
  let hypsab = AtomSet.union hypsa hypsb in
  let hypsabe = AtomSet.union hypsab hypse in
  let hyps = AtomSet.union hypsabe hypsh in
  let lhs = Tt.mk_apply ~loc h1 (Name.ident_of_atom x) ta1 b1 e1
  and rhs = Tt.mk_apply ~loc (Tt.mention_atoms hypsab h2) (Name.ident_of_atom y) ta2 (Tt.mention_atoms_ty hypsa b2) (Tt.mention_atoms hypsa e2)
  and ty = Tt.instantiate_ty [e1] b1 in
  let rhs = Tt.mention_atoms hypsabe rhs in
  EqTerm (ctx, hyps, lhs, rhs, ty)

let congr_eq ~loc (EqTy (ctxt, hypst, t1, t2))
             (EqTerm (ctxl, hypsl, l1, l2, ty_l))
             (EqTerm (ctxr, hypsr, r1, r2, ty_r)) =
  assert (Tt.alpha_equal_ty t1 ty_l && Tt.alpha_equal_ty t1 ty_r);
  let ctx = Ctx.join ~loc ctxt (Ctx.join ~loc ctxl ctxr)
  and hyps = AtomSet.union hypst (AtomSet.union hypsl hypsr) in
  let lhs = Tt.mk_eq ~loc t1 l1 (Tt.mention_atoms hypst r1)
  and rhs = Tt.mk_eq ~loc t2 l2 (Tt.mention_atoms hypst r2) in
  EqTerm (ctx, hyps, lhs, rhs, Tt.typ)

let congr_eq_ty ~loc eq_ty eq_l eq_r =
  is_type_equality (congr_eq ~loc eq_ty eq_l eq_r)

let congr_refl ~loc (EqTy (ctxt, hypst, t1, t2))
               (EqTerm (ctxe, hypse, e1, e2, ty_e)) =
  assert (Tt.alpha_equal_ty t1 ty_e);
  let ctx = Ctx.join ~loc ctxt ctxe
  and hyps = AtomSet.union hypst hypse in
  let lhs = Tt.mk_refl ~loc t1 e1
  and rhs = Tt.mention_atoms hyps (Tt.mk_refl ~loc t2 (Tt.mention_atoms hypst e2))
  and ty = Tt.mk_eq_ty ~loc t1 e1 e1 in
  EqTerm (ctx, hyps, lhs, rhs, ty)

(** Extensionality *)

let uip ~loc (Term (ctx1, e1, t1)) (Term (ctx2, e2, t2)) =
  assert (Tt.alpha_equal_ty t1 t2);
  let Tt.Ty t1_term = t1 in
  match t1_term.Tt.term with
    | Tt.Eq _ ->
      let ctx = Ctx.join ~loc ctx1 ctx2 in
      let hyps = AtomSet.union (Tt.assumptions_term e1) (Tt.assumptions_term e2) in
      EqTerm (ctx, hyps, e1, e2, t1)

    | _ -> assert false

let funext ~loc (EqTerm (ctx, hyps, lhs, rhs, _)) =
  match lhs.Tt.term, rhs.Tt.term with
    | Tt.Apply (h1, ((x,a1),b1), e1), Tt.Apply (h2, ((_,a2),b2), e2) ->
      assert (Tt.alpha_equal_ty a1 a2 && Tt.alpha_equal_ty b1 b2);
      assert (Tt.alpha_equal e1 e2);
      begin match e1.Tt.term with
        | Tt.Atom a ->
          let ctx = Ctx.abstract ~loc ctx a a1
          and hyps = AtomSet.remove a hyps
          and prod = Tt.mk_prod_ty ~loc x a1 b1 in
          EqTerm (ctx, hyps, h1, h2, prod)

        | Tt.Type | Tt.Bound _ | Tt.Constant _
        | Tt.Prod _ | Tt.Lambda _ | Tt.Apply _
        | Tt.Eq _ | Tt.Refl _ -> assert false
      end

   | _ -> assert false

(** Derivables *)

let natural_ty ~loc env ctx e =
  match e.Tt.term with
    | Tt.Type ->
      Tt.typ

    | Tt.Atom x ->
      begin match Ctx.lookup_atom x ctx with
        | Some (JAtom (_, _, t)) -> t
        | None -> assert false
      end

    | Tt.Constant c ->
      Env.constant_type c env

    | Tt.Prod _ ->
      Tt.typ

    | Tt.Lambda ((x,a),(_,b)) ->
      Tt.mk_prod_ty ~loc x a b

    | Tt.Apply (_,(_,b),e2) ->
      Tt.instantiate_ty [e2] b

    | Tt.Eq _ ->
      Tt.typ

    | Tt.Refl (a,e) ->
      Tt.mk_eq_ty ~loc a e e

    | Tt.Bound _ -> assert false

let natural_eq ~loc env (Term (ctx, e, derived)) =
  let natural = natural_ty ~loc env ctx e in
  EqTy (ctx, Tt.assumptions_term e, natural, derived)

let mk_refl ~loc (EqTerm (ctx1, hyps1, lhs1, rhs1, t1)) (EqTerm (ctx2, hyps2, lhs2, rhs2, t2)) =
  assert (Tt.alpha_equal_ty t1 t2 && Tt.alpha_equal lhs1 lhs2);
  let hyps = AtomSet.union hyps1 hyps2 in
  let ctx = Ctx.join ~loc ctx1 ctx2 in
  let term = Tt.mk_refl ~loc t1 lhs1 in
  let term = Tt.mention_atoms hyps term in
  Term (ctx, term, Tt.mk_eq_ty ~loc t1 rhs1 rhs2)

let refl_of_eq ~loc (EqTerm (ctx, hyps, lhs, rhs, ty)) =
  let term = Tt.mk_refl ~loc ty lhs in
  let term = Tt.mention_atoms hyps term in
  Term (ctx, term, Tt.mk_eq_ty ~loc ty lhs rhs)

