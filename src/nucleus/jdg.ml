module AtomSet = Name.AtomSet
module AtomMap = Name.AtomMap

(** Start with the types. *)

(* A Ctx is a map which assigns to an atom its type and the dependencies and dependants respectively.
   We can think of it as a directed graph whose vertices are the atoms, labelled by
   the type, and the sets of atoms are the two directions of edges. *)

(* XXX rename this to entry *)
type node =
  { ty : TT.ty; (* type of x *)
    needed_by : AtomSet.t } (* atoms which depend on x *)

type ctx = node AtomMap.t

(* Every judgement except the judgement that something is a valid context enforces that its context is minimal. *)

type term = Term of ctx * TT.term * TT.ty

type atom = JAtom of ctx * Name.atom * TT.ty

type ty = Ty of ctx * TT.ty

type closed_ty = TT.ty

type eq_term = EqTerm of ctx * TT.term * TT.term * TT.ty

type eq_ty = EqTy of ctx * TT.ty * TT.ty

(* The following do not guarantee a minimal context. *)
(* XXX: can we have a single type 'a term with some value for 'a guaranteeing strength? Then some functions like typeof can be polymorphic. *)
type weakty = WeakTy of ctx * TT.ty

type weakterm = WeakTerm of ctx * TT.term * TT.ty

type weakatom = WeakAtom of ctx * Name.atom * TT.ty

type error =
  | ConstantDependency
  | AbstractDependency of ctx * Name.atom * Name.atom list
  | AbstractInvalidType of Name.atom * TT.ty * TT.ty
  | InvalidJoin of ctx * ctx * Name.atom
  | SubstitutionDependency of Name.atom * TT.term * Name.atom
  | SubstitutionInvalidType of Name.atom * TT.ty * TT.ty
  | InvalidApplication
  | NotAType
  | AlphaEqualTypeMismatch of TT.ty * TT.ty
  | AlphaEqualTermMismatch of TT.term * TT.term
  | InvalidConvert of TT.ty * TT.ty
  | RuleInputMismatch of string * TT.ty * string * TT.ty * string

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

module Ctx = struct
  type t = ctx

  let empty = AtomMap.empty

  let is_empty = AtomMap.is_empty

  let print_entry ~penv ppf x {ty; needed_by;} =
    Format.fprintf ppf "%t : @[<hov>%t@]@ "
      (Name.print_atom ~printer:(penv.TT.atoms) x)
      (TT.print_ty ~penv ty)

  let print ~penv ctx ppf =
    Format.pp_open_vbox ppf 0 ;
    AtomMap.iter (print_entry ~penv ppf) ctx ;
    Format.pp_close_box ppf ()

  let as_set ctx =
    AtomMap.fold (fun x _ acc -> AtomSet.add x acc) ctx AtomSet.empty

  let lookup x (ctx : t) =
    try Some (AtomMap.find x ctx)
    with Not_found -> None

  let recursive_assumptions ctx aset =
    let rec fold visited = function
      | [] -> visited
      | x::rem ->
        if AtomSet.mem x visited
        then fold visited rem
        else
          let visited = AtomSet.add x visited in
          let {ty;_} = AtomMap.find x ctx in
          let aset = TT.assumptions_ty ty in
          let rem = List.rev_append (AtomSet.elements aset) rem in
          fold visited rem
    in
    fold AtomSet.empty (AtomSet.elements aset)

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

  let lookup_atom x ctx =
    match lookup x ctx with
      | None -> None
      | Some {ty;_} ->
        let ctx = restrict ctx (AtomSet.singleton x) in
        Some (JAtom (ctx, x, ty))

  let add_fresh (Ty (ctx, ty)) x =
    let y = Name.fresh x in
    let ctx = AtomMap.mapi
      (fun z node -> {node with needed_by = AtomSet.add y node.needed_by})
      ctx
    in
    let ctx = AtomMap.add y {ty;needed_by = AtomSet.empty;} ctx in
    JAtom (ctx, y, ty)

  let add_weak (WeakTy (ctx, ty)) x =
    let y = Name.fresh x in
    let aset = TT.assumptions_ty ty in
    let needs = recursive_assumptions ctx aset in
    let ctx = AtomMap.mapi (fun z node ->
                            if AtomSet.mem z needs
                            then {node with needed_by = AtomSet.add y node.needed_by}
                            else node)
                           ctx
    in
    let ctx = AtomMap.add y {ty;needed_by = AtomSet.empty;} ctx in
    WeakAtom (ctx, y, ty)

  let abstract ~loc (ctx : t) x ty =
    match lookup x ctx with
    | None ->
       ctx
    | Some node ->
      if TT.alpha_equal_ty node.ty ty
      then
        if AtomSet.is_empty node.needed_by
        then
          let ctx = AtomMap.remove x ctx in
          let ctx = AtomMap.map (fun node -> {node with needed_by = AtomSet.remove x node.needed_by}) ctx in
          ctx
        else
          let needed_by_l = AtomSet.elements node.needed_by in
          error ~loc (AbstractDependency (ctx, x, needed_by_l))
      else
        error ~loc (AbstractInvalidType (x, ty, node.ty))

  let join ~loc ctx1 ctx2 =
    AtomMap.fold (fun x node res ->
        match lookup x res with
          | Some node' ->
            if TT.alpha_equal_ty node.ty node'.ty
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

  (* substitute x by e in ctx *)
  let substitute ~loc ctx x (Term (ctxe, e, t)) =
    let ctx = join ~loc ctx ctxe in
    match lookup x ctx with
      | None -> ctx
      | Some xnode ->
        if not (TT.alpha_equal_ty xnode.ty t)
        then
          error ~loc (SubstitutionInvalidType (x, xnode.ty, t))
        else
          let deps = recursive_assumptions ctx (TT.assumptions_term e) in
          let ctx = AtomSet.fold (fun y ctx ->
              let ynode = AtomMap.find y ctx in
              if AtomSet.mem y deps
              then
                error ~loc (SubstitutionDependency (x, e, y))
              else
                let ty = TT.substitute_ty [x] [e] ynode.ty in
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
        (AtomSet.add x handled, (JAtom (restrict ctx (AtomSet.singleton x), x, ty)) :: xts)
    in
    let _, xts = AtomMap.fold (fun x _ -> process x) ctx (AtomSet.empty, []) in
    xts

end

module Signature = struct
  module ConstantMap = Name.IdentMap

  type t = {
    constants : TT.ty ConstantMap.t;
  }

  let empty = {
    constants = ConstantMap.empty;
  }

  let constant_type c env =
    ConstantMap.find c env.constants

  let add_constant c t env =
    {constants = ConstantMap.add c t env.constants}

end

(** Judgements *)

let strengthen (WeakTerm (ctx, e, t)) =
  let hyps = AtomSet.union (TT.assumptions_term e) (TT.assumptions_ty t) in
  let ctx = Ctx.restrict ctx hyps in
  Term (ctx,e,t)

let strengthen_ty (WeakTy (ctx, t)) =
  let hyps = TT.assumptions_ty t in
  let ctx = Ctx.restrict ctx hyps in
  Ty (ctx, t)

let strengthen_atom (WeakAtom (ctx, x, t)) =
  let hyps = AtomSet.singleton x in
  let ctx = Ctx.restrict ctx hyps in
  JAtom (ctx, x, t)

let typeof (Term (ctx, _, t)) =
  strengthen_ty (WeakTy (ctx, t))

let atom_ty (JAtom (ctx,x,t)) =
  strengthen_ty (WeakTy (ctx, t))

let atom_term ~loc (JAtom (ctx,x,t)) =
  Term (ctx, TT.mk_atom ~loc x, t)

let ty_ty = Ty (Ctx.empty, TT.typ)

let is_closed_ty ~loc (Ty (ctx, t)) =
  if Ctx.is_empty ctx
  then t
  else error ~loc ConstantDependency

let occurs (JAtom (_, x, _)) (Term (ctx, _, _)) =
  Ctx.lookup_atom x ctx

let contextof (Term (ctx, _, _)) =
  ctx

let print_term ~penv ?max_level (Term (ctx, e, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hv>@[<hov>%t@]@;<1 -2>: @[<hov>%t@]@]"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (TT.print_term ~penv ~max_level:Level.highest e)
              (TT.print_ty ~penv ~max_level:Level.highest t)

let print_ty ~penv ?max_level (Ty (ctx, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hov>%t@] @ type"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (TT.print_ty ~penv ~max_level:Level.highest t)

let print_eq_term ~penv ?max_level (EqTerm (ctx, e1, e2, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hv>@[<hov>%t@]@ %s@ @[<hov>%t@]@ :@ @[<hov>%t@]@]"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (TT.print_term ~penv e1)
              (Print.char_equal ())
              (TT.print_term ~penv e2)
              (TT.print_ty ~penv t)

let print_eq_ty ~penv ?max_level (EqTy (ctx, t1, t2)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hv>@[<hov>%t@]@ %s@ @[<hov>%t@]@]"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (TT.print_ty ~penv t1)
              (Print.char_equal ())
              (TT.print_ty ~penv t2)

let print_error ~penv err ppf = match err with
  | ConstantDependency ->
     Format.fprintf ppf "constants may not depend on assumptions"

  | InvalidApplication -> Format.fprintf ppf "Invalid application."

  | NotAType -> Format.fprintf ppf "Not a type."

  | AbstractDependency (ctx, x, needed_by_l) ->
     Format.fprintf ppf "@[<hov>cannot abstract@ %t@ because@ %t@ depend%s on it, in context@,   @[<hov>%t@]@]"
          (Name.print_atom ~printer:penv.TT.atoms x)
          (Print.sequence (Name.print_atom ~printer:penv.TT.atoms ~parentheses:true) "," needed_by_l)
           (match needed_by_l with [_] -> "s" | _ -> "")
          (Ctx.print ~penv ctx)

  | AbstractInvalidType (x, t1, t2) ->
     Format.fprintf ppf "cannot abstract@ %t@ with type@ %t@ because it must have type@ %t"
        (Name.print_atom ~printer:penv.TT.atoms x)
        (TT.print_ty ~penv t1)
        (TT.print_ty ~penv t2)

  | InvalidJoin (ctx1, ctx2, x) ->
     Format.fprintf ppf "cannot join contexts@ %t and@ %t at %t"
                    (Ctx.print ~penv ctx1)
                    (Ctx.print ~penv ctx2)
                    (Name.print_atom ~printer:penv.TT.atoms x ~parentheses:true)

  | SubstitutionDependency (x, e, y) ->
     Format.fprintf ppf "cannot substitute@ %t@ with@ %t,@ dependency cycle at@ %t"
                (Name.print_atom ~printer:penv.TT.atoms x)
                (TT.print_term ~penv e)
                (Name.print_atom ~printer:penv.TT.atoms y)

  | SubstitutionInvalidType (x, x_ty, t) ->
     Format.fprintf ppf "cannot substitute term of type %t for %t of type %t"
                    (TT.print_ty ~penv t)
                    (Name.print_atom ~printer:penv.TT.atoms x)
                    (TT.print_ty ~penv x_ty)

  | InvalidConvert (t1, t2) ->
    Format.fprintf ppf "Trying to convert something at@ %t@ using an equality on@ %t@."
      (TT.print_ty ~penv t1) (TT.print_ty ~penv t2)

  | AlphaEqualTypeMismatch (t1, t2) ->
    Format.fprintf ppf "The types@ %t@ and@ %t@ should be alpha equal."
      (TT.print_ty ~penv t1) (TT.print_ty ~penv t2)

  | AlphaEqualTermMismatch (e1, e2) ->
    Format.fprintf ppf "The terms@ %t@ and@ %t@ should be alpha equal."
      (TT.print_term ~penv e1) (TT.print_term ~penv e2)

  | RuleInputMismatch (rule, t1, desc1, t2, desc2) ->
    Format.fprintf ppf "@[<v>In the %s rule, the following types should be identical\
:@,   @[<hov>%t@]@ (%s) and@,   @[<hov>%t@]@ (%s)@]@."
      rule (TT.print_ty ~penv t1) desc1 (TT.print_ty ~penv t2) desc2

(** Destructors *)
type 'a abstraction = atom * 'a

type shape =
  | Atom of atom
  | Constant of Name.constant
  | Abstract of term abstraction
  | Apply of term * term

and shape_ty =
  | Type
  | Prod of ty abstraction
  | El of term

let shape (Term (ctx,e,t)) =
  match e.Location.thing.TT.thing with
    | TT.Atom x ->
      begin match Ctx.lookup_atom x ctx with
        | Some j -> Atom j
        | None -> assert false
      end

    | TT.Constant c -> Constant c

    | TT.Abstract ((x,a),(e,b)) ->
      let ja = WeakTy (ctx, a) in
      let WeakAtom (ctx, y, _) as jy = Ctx.add_weak ja x in
      let b = TT.unabstract_ty [y] b
      and e = TT.unabstract [y] e in
      let je = WeakTerm (ctx, e, b) in
      Abstract (strengthen_atom jy, strengthen je)


    | TT.Apply (e1,((x,a),b),e2) ->
      let je2 = WeakTerm (ctx, e2, a) in
      let prod = TT.mk_prod ~loc:e.Location.loc x a b in
      let je1 = WeakTerm (ctx, e1, prod) in
      Apply (strengthen je1, strengthen je2)

    | TT.Bound _ -> assert false

let shape_ty (Ty (ctx, ty)) =
  match ty.Location.thing.TT.thing with

  | TT.Type -> Type

  | TT.Prod ((x,a),b) ->
     let ja = WeakTy (ctx, a) in
     let WeakAtom (ctx, y, _) as jy = Ctx.add_weak ja x in
     let b = TT.unabstract_ty [y] b in
     let jb = WeakTy (ctx, b) in
     Prod (strengthen_atom jy, strengthen_ty jb)

  | TT.El e -> El (Term (ctx, e, TT.mk_type ~loc:e.Location.loc))

let shape_eq_ty (EqTy (ctx, ty1, ty2)) =
  let j1 = strengthen_ty (WeakTy (ctx, ty1))
  and j2 = strengthen_ty (WeakTy (ctx, ty2))
  in j1, j2

let shape_eq_term (EqTerm (ctx, e1, e2, ty)) =
  let j1 = strengthen (WeakTerm (ctx, e1, ty))
  and j2 = strengthen (WeakTerm (ctx, e2, ty))
  and jt = strengthen_ty (WeakTy (ctx, ty))
  in (j1, j2, jt)

let shape_prod j =
  match shape_ty j with
  | Prod (a, b) -> Some (a, b)
  | (Type | El _) -> None

(** Construct judgements *)
let form ~loc env = function
  | Atom x -> atom_term ~loc x

  | Constant c ->
    let t = Signature.constant_type c env in
    Term (Ctx.empty, TT.mk_constant ~loc c,t)

  | Abstract ((JAtom (ctxa,x,a)),(Term (ctxe,e,b))) ->
    let ctx = Ctx.join ~loc ctxe ctxa in
    let ctx = Ctx.abstract ~loc ctx x a in
    let b = TT.abstract_ty [x] b
    and e = TT.abstract [x] e in
    let x = Name.ident_of_atom x in
    Term (ctx, TT.mk_abstract ~loc x a e b, TT.mk_prod ~loc x a b)

  | Apply (Term (ctx1,e1,t1), Term (ctx2,e2,t2)) ->
    let ctx = Ctx.join ~loc ctx2 ctx1 in
    begin match t1.Location.thing.TT.thing with
      | TT.Prod ((x,a),b) ->
        if TT.alpha_equal_ty a t2
        then
          let out = TT.instantiate_ty [e2] b in
          Term (ctx, TT.mk_apply ~loc e1 x a b e2, out)
        else
          error ~loc InvalidApplication
      | _ -> error ~loc InvalidApplication
    end

let form_ty ~loc env = function
  | Type ->
    Ty (Ctx.empty, TT.mk_type ~loc)

  | Prod ((JAtom (ctxa,x,a)),(Ty (ctxb,b))) ->
    let ctx = Ctx.join ~loc ctxb ctxa in
    let ctx = Ctx.abstract ~loc ctx x a in
    let b = TT.abstract_ty [x] b in
    Ty (ctx, TT.mk_prod ~loc (Name.ident_of_atom x) a b)

  | El (Term (ctx, e, t)) ->
     if TT.alpha_equal_ty t TT.typ
     then
       Ty (ctx, TT.mk_el ~loc e)
     else
       error ~loc NotAType

(** Substitution *)
let substitute_ty ~loc (Ty (ctxt, t)) (JAtom (_, a, _)) (Term (_, s, _) as js) =
  let ctxt = Ctx.substitute ~loc ctxt a js in
  let t = TT.substitute_ty [a] [s] t in
  strengthen_ty (WeakTy (ctxt, t))

let substitute ~loc (Term (ctxe, e, t)) (JAtom (_, a, _)) (Term (_, s, _) as js) =
  let ctxe = Ctx.substitute ~loc ctxe a js in
  let t = TT.substitute_ty [a] [s] t
  and e = TT.substitute [a] [s] e in
  strengthen (WeakTerm (ctxe, e, t))

(** Conversion *)

type side = LEFT | RIGHT

let eq_term_side side (EqTerm (ctx, lhs, rhs, ty)) =
  let term = match side with LEFT -> lhs | RIGHT -> rhs in
  strengthen (WeakTerm (ctx, term, ty))

let eq_term_typeof (EqTerm (ctx, _, _, ty)) =
  strengthen_ty (WeakTy (ctx, ty))

let eq_ty_side side (EqTy (ctx, lhs, rhs)) : ty =
  let ty = match side with LEFT -> lhs | RIGHT -> rhs in
  strengthen_ty (WeakTy (ctx, ty))

let convert ~loc (Term (ctx1, e, t)) (EqTy (ctx2, t1, t2)) =
  if not (TT.alpha_equal_ty t t1)
  then error ~loc (InvalidConvert (t, t1))
  else
    let ctx = Ctx.join ~loc ctx1 ctx2 in
    let e = TT.mention_atoms (Ctx.as_set ctx2) e in
    Term (ctx, e, t2)

let convert_eq ~loc (EqTerm (ctx1, e1, e2, ty)) (EqTy (ctx2, t1, t2)) =
  if not (TT.alpha_equal_ty ty t1)
  then error ~loc (InvalidConvert (ty, t1))
  else
    let hyps2 = Ctx.as_set ctx2 in
    let e1 = TT.mention_atoms hyps2 e1
    and e2 = TT.mention_atoms hyps2 e2
    and ctx = Ctx.join ~loc ctx1 ctx2 in
    EqTerm (ctx, e1, e2, t2)

(** Constructors *)

let reflexivity (Term (ctx, e, t)) =
  EqTerm (ctx, e, e, t)

let reflexivity_ty (Ty (ctx, t)) =
  EqTy (ctx, t, t)

let mk_alpha_equal_ty ~loc (Ty (ctx1, t1)) (Ty (ctx2, t2)) =
  match TT.alpha_equal_ty t1 t2 with
  | false -> None
  | true ->
     let ctx = Ctx.join ~loc ctx1 ctx2 in
     Some (EqTy (ctx, t1, t2))

let mk_alpha_equal ~loc (Term (ctx1, e1, ty1)) (Term (ctx2, e2, ty2)) =
  match TT.alpha_equal_ty ty1 ty2 with
  | false -> error ~loc (AlphaEqualTypeMismatch (ty1, ty2))
  | true ->
     begin match TT.alpha_equal e1 e2 with
     | false -> None
     | true ->
        let ctx = Ctx.join ~loc ctx1 ctx2 in
        let e2 = TT.mention_atoms (TT.assumptions_term e1) e2 in
        Some (EqTerm (ctx, e1, e2, ty1))
     end

let alpha_equal (Term (_, e1, _)) (Term (_, e2, _)) =
  TT.alpha_equal e1 e2

let alpha_equal_ty (Ty (_, t1)) (Ty (_, t2)) =
  TT.alpha_equal_ty t1 t2

let alpha_equal_eq_ty ~loc (Ty (ctx1, t1)) (Ty (ctx2, t2)) =
  if not (TT.alpha_equal_ty t1 t2)
  then
    None
  else
    let ctx = Ctx.join ~loc ctx1 ctx2 in
    Some (EqTy (ctx, t1, t2))

let symmetry (EqTerm (ctx, e1, e2, t)) = EqTerm (ctx, e2, e1, t)

let symmetry_ty (EqTy (ctx, t1, t2)) = EqTy (ctx, t2, t1)

let transitivity_term ~loc (EqTerm (ctx, e1, e2, t)) (EqTerm (ctx', e1', e2', t')) =
  match TT.alpha_equal_ty t t' with
  | false -> error ~loc (AlphaEqualTypeMismatch (t, t'))
  | true ->
     begin match TT.alpha_equal e2 e1' with
     | false -> error ~loc (AlphaEqualTermMismatch (e2, e1'))
     | true ->
        let ctx = Ctx.join ~loc ctx ctx' in
        EqTerm (ctx, e1, e2', t)
     end

let transitivity_ty ~loc (EqTy (ctx1, t1, t2)) (EqTy (ctx2, u1, u2)) =
  begin match TT.alpha_equal_ty t2 u1 with
     | false -> error ~loc (AlphaEqualTypeMismatch (t2, u1))
     | true ->
        let ctx = Ctx.join ~loc ctx1 ctx2 in
        EqTy (ctx, t1, u2)
     end

(** Beta step, in the future this will be expressible. *)
let beta ~loc (EqTy (ctxa, a1, a2))
              (JAtom (_, x, _)) (JAtom (_, y, _))
              (EqTy (ctxb, b1, b2))
              (Term (ctx1, e1, t1))
              (Term (ctx2, e2, t2)) =
  if not (TT.alpha_equal_ty b1 t1)
  then error ~loc (RuleInputMismatch ("beta",
          b1, "the given type family ('B')",
          t1, "the type of the expression being substituted into ('e1')"))
  else if not (TT.alpha_equal_ty a2 t2)
  then error ~loc (RuleInputMismatch ("beta",
          a2, "the given parameter type ('A')",
          t2, "the type of the expression to be substituted ('e2')"))
  else
    let ctxa = Ctx.join ~loc ctxa ctx2
    and ctxb = Ctx.abstract ~loc (Ctx.join ~loc ctxb ctx1) x a1 in

    let hypsa = Ctx.as_set ctxa
    and hypsb = Ctx.as_set ctxb in

    let b1 = TT.abstract_ty [x] b1
    and e1 = TT.abstract [x] e1
    and b2 = TT.abstract_ty [y] (TT.substitute_ty [x] [TT.mention_atoms hypsa (TT.mk_atom ~loc y)] b2) in
    let ctx = Ctx.join ~loc ctxa ctxb
    and lam = TT.mk_abstract ~loc (Name.ident_of_atom x) a1 e1 b1
    and e_s = TT.mention_atoms hypsb (TT.instantiate [TT.mention_atoms hypsa e2] e1) in
    let app = TT.mk_apply ~loc lam (Name.ident_of_atom y) a2 b2 e2
    and ty = TT.instantiate_ty [e2] b2 in
    EqTerm (ctx, app, e_s, ty)


(** Congruence *)

let congr_prod ~loc (EqTy (ctxa, ta1, ta2)) (JAtom (_, x, _)) (JAtom (_, y, _)) (EqTy (ctxb, b1, b2)) =
  let ctxb = Ctx.abstract ~loc ctxb x ta1 in

  let hypsa = Ctx.as_set ctxa in

  let b1 = TT.abstract_ty [x] b1
  and b2 = TT.abstract_ty [y] (TT.substitute_ty [x] [TT.mention_atoms hypsa (TT.mk_atom ~loc y)] b2) in
  let ctx = Ctx.join ~loc ctxa ctxb in
  let lhs = TT.mk_prod ~loc (Name.ident_of_atom x) ta1 b1
  and rhs = TT.mk_prod ~loc (Name.ident_of_atom y) ta2 b2 in
  EqTy (ctx, lhs, rhs)

let congr_abstract ~loc (EqTy (ctxa, ta1, ta2))
                 (JAtom (_, x, _)) (JAtom (_, y, _))
                 (EqTy (ctxb, b1, b2))
                 (EqTerm (ctxe, e1, e2, ty_e)) =
  if not (TT.alpha_equal_ty b1 ty_e)
  then error ~loc (RuleInputMismatch ("congr-abstract",
            b1, "The left-hand-side in the equality between body types",
            ty_e, "The type at which the body terms are compared"))
  else
    let ctx = Ctx.join ~loc ctxa (Ctx.abstract ~loc (Ctx.join ~loc ctxb ctxe) x ta1) in

    let hypsa = Ctx.as_set ctxa
    and hypsb = AtomSet.remove x (Ctx.as_set ctxb) in
    let hypsab = AtomSet.union hypsa hypsb in

    let y_mentions = TT.mention_atoms hypsa (TT.mk_atom ~loc y) in
    let e1 = TT.abstract [x] e1
    and e2 = TT.abstract [y] (TT.substitute [x] [y_mentions] e2)
    and b1 = TT.abstract_ty [x] b1
    and b2 = TT.abstract_ty [x] (TT.substitute_ty [x] [y_mentions] b2) in
    let lhs = TT.mk_abstract ~loc (Name.ident_of_atom x) ta1 e1 b1
    and rhs = TT.mention_atoms hypsab (TT.mk_abstract ~loc (Name.ident_of_atom y) ta2 e2 b2)
    and ty = TT.mk_prod ~loc (Name.ident_of_atom x) ta1 b1 in
    EqTerm (ctx, lhs, rhs, ty)

let congr_apply ~loc (EqTy (ctxa, ta1, ta2))
                (JAtom (_, x, _)) (JAtom (_, y, _))
                (EqTy (ctxb, b1, b2))
                (EqTerm (ctxh, h1, h2, ty_h))
                (EqTerm (ctxe, e1, e2, ty_e)) =
  let b1 = TT.abstract_ty [x] b1 in
  let prod1 = TT.mk_prod ~loc (Name.ident_of_atom x) ta1 b1 in
  if not (TT.alpha_equal_ty prod1 ty_h)
  then error ~loc (RuleInputMismatch ("congr-apply", prod1,
       "the Pi inferred from the left-hand-sides of the type equalities",
       ty_h,
       "the type at which the functions are equal"))
  else if not (TT.alpha_equal_ty ta1 ty_e)
  then error ~loc (RuleInputMismatch ("congr-apply", ta1,
       "the parameter type on the left-hand-side of the type equality",
       ty_e,
       "the type at which the arguments are equal"))
  else
    let ctxb = Ctx.abstract ~loc ctxb x ta1 in

    let hypsa = Ctx.as_set ctxa
    and hypsb = Ctx.as_set ctxb
    and hypse = Ctx.as_set ctxe in
    let hypsab = AtomSet.union hypsa hypsb in
    let hypsabe = AtomSet.union hypsab hypse in

    let y_mentions = TT.mention_atoms hypsa (TT.mk_atom ~loc y) in
    let b2 = TT.abstract_ty [y] (TT.substitute_ty [x] [y_mentions] b2) in
    let ctx = Ctx.join ~loc ctxa (Ctx.join ~loc ctxb (Ctx.join ~loc ctxh ctxe)) in
    let lhs = TT.mk_apply ~loc h1 (Name.ident_of_atom x) ta1 b1 e1
    and rhs = TT.mk_apply ~loc (TT.mention_atoms hypsab h2) (Name.ident_of_atom y) ta2 (TT.mention_atoms_ty hypsa b2) (TT.mention_atoms hypsa e2)
    and ty = TT.instantiate_ty [e1] b1 in
    let rhs = TT.mention_atoms hypsabe rhs in
    EqTerm (ctx, lhs, rhs, ty)

(** Derivables *)

let natural_ty ~loc env ctx e =
  match e.Location.thing.TT.thing with
    | TT.Atom x ->
      begin match Ctx.lookup_atom x ctx with
        | Some (JAtom (_, _, t)) -> t
        | None -> assert false
      end

    | TT.Constant c ->
      Signature.constant_type c env

    | TT.Abstract ((x,a),(_,b)) ->
      TT.mk_prod ~loc x a b

    | TT.Apply (_,(_,b),e2) ->
      TT.instantiate_ty [e2] b

    | TT.Bound _ -> assert false

let natural_eq ~loc env (Term (ctx, e, derived)) =
  let natural = natural_ty ~loc env ctx e in
  EqTy (ctx, natural, derived)

module Json =
struct

  let context ctx =
    let dict =
      AtomMap.fold
        (fun x {ty; needed_by} dict ->
         (Name.Json.atom x,
          Json.tuple [TT.Json.ty ty; Name.Json.atomset needed_by]) :: dict)
        ctx
        []
    in
    Json.Dict dict

  let term (Term (ctx, e, ty)) =
    Json.record [("context", context ctx);
                 ("term", TT.Json.term e);
                 ("ty", TT.Json.ty ty)]

  let ty (Ty (ctx, ty)) =
    Json.record [("context", context ctx);
                 ("ty", TT.Json.ty ty)]

  let eq_term (EqTerm (ctx, e1, e2, t)) =
    Json.record [("context", context ctx);
                 ("lhs", TT.Json.term e1);
                 ("rhs", TT.Json.term e2);
                 ("ty", TT.Json.ty t)]

  let eq_ty (EqTy (ctx, t1, t2)) =
    Json.record [("context", context ctx);
                 ("lhs", TT.Json.ty t1);
                 ("rhs", TT.Json.ty t2)]

end
