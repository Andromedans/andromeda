module AtomSet = Name.AtomSet
module AtomMap = Name.AtomMap

(** Start with the types. *)

(* A Ctx is a map which assigns to an atom its type and the dependencies and dependants respectively.
   We can think of it as a directed graph whose vertices are the atoms, labelled by
   the type, and the sets of atoms are the two directions of edges. *)

type 'a abstraction =
  | Abstract of (Name.ident * TT.ty) * 'a abstraction
  | NotAbstract of 'a

type ctx_entry =
  { ty : TT.ty; (* type of x *)
    needed_by : AtomSet.t } (* atoms which depend on x *)

type ctx = ctx_entry AtomMap.t

(** Every judgement enforces that its context is minimal (strengthened). *)

type is_atom = IsAtom of ctx * Name.atom * TT.ty

type is_term = IsTerm of ctx * (TT.term * TT.ty) abstraction

type is_type = IsType of ctx * TT.ty abstraction

type eq_term = EqTerm of ctx * (TT.term * TT.term * TT.ty) abstraction

type eq_type = EqType of ctx * (TT.ty * TT.ty) abstraction

(** Shapes (defined below) are used to construct and invert judgements. The
   [form_XYZ] functions below take a shape and construct a judgement from it,
   whereas the [invert_XYZ] functions do the opposite. We can think of shapes as
   "stumps", i.e., the lowest level of a derivation tree. *)

(** Premises of a constructor. *)
type premise =
  | PremiseIsType of is_type
  | PremiseIsTerm of is_term
  | PremiseEqType of eq_type
  | PremiseEqTerm of eq_term

type shape_is_term =
  | TermAtom of is_atom
  | TermConstructor of Name.constructor * premise list
  | TermAbstract of is_atom * is_term
  (* obsolete *)
  | Constant of Name.constant

and shape_is_type =
  | TypeConstructor of Name.constructor * premise list
  | TypeAbstract of is_atom * is_type
  (* obsolete *)
  | Type
  | El of is_term

(** Auxiliary datatypes used for judgements whose context are not necessarily
   minimal. *)

type weak_is_type = WeakIsType of ctx * TT.ty

type weak_is_term = WeakIsTerm of ctx * TT.term * TT.ty

type weak_is_atom = WeakIsAtom of ctx * Name.atom * TT.ty

(** Error messages emitted by this module. *)

type error =
  | ConstantDependency
  | AbstractDependency of ctx * Name.atom * Name.atom list
  | AbstractInvalidType of Name.atom * TT.ty * TT.ty
  | InvalidJoin of ctx * ctx * Name.atom
  | SubstitutionDependency of Name.atom * TT.term * Name.atom
  | SubstitutionInvalidType of Name.atom * TT.ty * TT.ty
  | NotAType
  | AlphaEqualTypeMismatch of TT.ty * TT.ty
  | AlphaEqualTermMismatch of TT.term * TT.term
  | InvalidConvert of TT.ty * TT.ty
  | RuleInputMismatch of string * TT.ty * string * TT.ty * string
  | NotAbstractExpected

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

let not_abstracted ~loc = function
  | NotAbstract x -> x
  | Abstract _ -> error ~loc NotAbstractExpected

module Ctx = struct
  type t = ctx

  let empty = AtomMap.empty

  let is_empty = AtomMap.is_empty

  let print_entry ~penv ppf x {ty; needed_by;} =
    Format.fprintf ppf "%t : @[<hov>%t@]@ "
      (Name.print_atom ~printer:(penv.TT.atoms) x)
      (TT.print_type ~penv ty)

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
        Some (IsAtom (ctx, x, ty))

  let add_fresh ~loc (IsType (ctx, ty)) x =
    let ty = not_abstracted ~loc ty in
    let y = Name.fresh x in
    let ctx = AtomMap.mapi
      (fun z node -> {node with needed_by = AtomSet.add y node.needed_by})
      ctx
    in
    let ctx = AtomMap.add y {ty; needed_by = AtomSet.empty} ctx in
    IsAtom (ctx, y, ty)

  let add_weak (WeakIsType (ctx, ty)) x =
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
    WeakIsAtom (ctx, y, ty)

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
  let substitute ~loc ctx x (IsTerm (ctxe, e, t)) =
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
                let ty = TT.substitute_type [x] [e] ynode.ty in
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
        (AtomSet.add x handled, (IsAtom (restrict ctx (AtomSet.singleton x), x, ty)) :: xts)
    in
    let _, xts = AtomMap.fold (fun x _ -> process x) ctx (AtomSet.empty, []) in
    xts

end

module Rule = struct

  module Schema = struct

    type meta = int (* meta-variables appearing in rules *)

    type term =
      | TermMeta of meta (* a previously matched meta-variable *)
      | TermConstructor of Name.constructor * premise list

    and ty =
      | TypeMeta of meta (* a previously matched meta-variable *)
      | TypeConstructor of Name.constructor * premise list

    type 'a premise_abstraction =
      | PremiseNotAbstract of 'a
      | PremiseAbstract of (Name.ident * ty) * 'a premise_abstraction

    type premise =
      | PremiseIsType of unit premise_abstraction
      | PremiseIsTerm of ty premise_abstraction
      | PremiseEqType of (ty * ty) premise_abstraction
      | PremiseEqTerm of (term * term * ty) premise_abstraction

    type 'a rule_abstraction =
      | RuleNotAbstract of 'a
      | RuleAbstract of (Name.ident * premise) * 'a rule_abstraction

    type is_type = unit rule_abstraction

    type is_term = ty rule_abstraction

    type eq_term = (ty * ty) rule_abstraction

    type eq_type = (term * term * ty) rule_abstraction

  end


  let rec match_type metas t_schema t =
    match t_schema, t.Location.thing.TT.thing with

    | Schema.TypeMeta k, t' ->
       failwith "not done" ;
       t

    | Schema.TypeConstructor (c, premises), TT.TypeConstructor (c', args) ->
       failwith "not done"

    | _, _ -> failwith "not done"

  let rec match_premise_abstraction metas match_jdg schema abstr =
    match schema, abstr with

    | Schema.PremiseNotAbstract jdg_schema, NotAbstract jdg ->
       match_jdg metas jdg_schema jdg

    | Schema.PremiseAbstract ((_, t_schema), schema), Abstract ((x, t), abstr) ->
       check_type metas t_schema t ;
       let abstr = match_premise_abstraction metas match_jdg schema abstr in
       TT.mk_abstract x abstr

    | _, _ ->
       failwith "premise match fail"

  let rec match_is_type metas ty_schema (IsType (ctx, abstr)) =



  let match_premise metas premise_schema premise =
    match premise_schema, premise with

    | Schema.PremiseIsType type_schema, PremiseIsType t ->
       let t = match_is_type metas type_schema t in
       TT.mk_arg_is_type t

    | Schema.PremiseIsTerm term_schema, PremiseIsTerm e ->
       let e = match_is_term metas term_schema e in
       TT.mk_arg_is_term e

    | Schema.PremiseEqType eqty_schema, PremiseEqType eqty ->
       let eqty = match_eq_type metas eqty_schema eqty in
       TT.mk_arg_eq_type eqty

    | Schema.PremiseEqTerm eqterm_schmea, PremiseEqTerm eqterm ->
       let eqterm = match_eq_term metas eqterm_schema eqterm in
       TT.mk_arg_eq_term eqterm

    | _, _ ->
       failwith "wrong premise form"

  let rec form_is_type' metas rule_schema premises =
    match rule_schema, premises with

    | Schema.RuleNotAbstract (), [] -> List.rev metas

    | Schema.RuleAbstract ((_, premise_schema), rule_schema), premise :: premises ->
       let m = match_premise metas premise_schema premise in
       form_is_type' (m :: metas) rule_schema premises

    | Schema.RuleNotAbstract (), _::_ ->
       failwith "this type constructor is applied to too many arguments"

    | Schema.RuleAbstract _, [] ->
       failwith "this type constructor is applied to too few arguments"



  let form_is_type rule premises = form_is_type' [] rule premises

  let form_is_term rule premises = failwith "Rule.form_is_term is not implemented"

  let form_eq_type rule premises = failwith "Rule.form_eq_type is not implemented"

  let form_eq_term rule premises = failwith "Rule.form_eq_term is not implemented"

  let invert_is_term rule args = failwith "Rule.invert_is_term is not implemented"

  let invert_is_type rule args = failwith "Rule.invert_is_type is not implemented"

end


module Signature = struct
  module ConstantMap = Name.IdentMap

  type t =
    { constants : TT.ty ConstantMap.t
    }

  let empty = {
    constants = ConstantMap.empty;
  }

  let constant_type c sgn =
    ConstantMap.find c sgn.constants

  let add_constant c t sgn =
    {constants = ConstantMap.add c t sgn.constants}

end

(** Judgements *)

let strengthen (WeakIsTerm (ctx, e, t)) =
  let hyps = AtomSet.union (TT.assumptions_term e) (TT.assumptions_ty t) in
  let ctx = Ctx.restrict ctx hyps in
  IsTerm (ctx,e,t)

let strengthen_ty (WeakIsType (ctx, t)) =
  let hyps = TT.assumptions_ty t in
  let ctx = Ctx.restrict ctx hyps in
  IsType (ctx, t)

let strengthen_atom (WeakIsAtom (ctx, x, t)) =
  let hyps = AtomSet.singleton x in
  let ctx = Ctx.restrict ctx hyps in
  IsAtom (ctx, x, t)

let typeof (IsTerm (ctx, _, t)) =
  strengthen_ty (WeakIsType (ctx, t))

let atom_is_type (IsAtom (ctx,x,t)) =
  strengthen_ty (WeakIsType (ctx, t))

let atom_is_term ~loc (IsAtom (ctx,x,t)) =
  IsTerm (ctx, TT.mk_atom ~loc x, t)

let ty_ty = IsType (Ctx.empty, TT.typ)

let is_closed_ty ~loc (IsType (ctx, t)) =
  if Ctx.is_empty ctx
  then t
  else error ~loc ConstantDependency

let occurs (IsAtom (_, x, _)) (IsTerm (ctx, _, _)) =
  Ctx.lookup_atom x ctx

let contextof (IsTerm (ctx, _, _)) =
  ctx

let print_is_term ~penv ?max_level (IsTerm (ctx, e, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hv>@[<hov>%t@]@;<1 -2>: @[<hov>%t@]@]"
              (Ctx.print ~penv ctx)
              (Print.char_vdash ())
              (TT.print_term ~penv ~max_level:Level.highest e)
              (TT.print_ty ~penv ~max_level:Level.highest t)

let print_is_type ~penv ?max_level (IsType (ctx, t)) ppf =
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

let print_eq_type ~penv ?max_level (EqType (ctx, t1, t2)) ppf =
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

let invert_is_term (IsTerm (ctx,e,t)) =
  match e.Location.thing.TT.thing with
    | TT.Atom x ->
      begin match Ctx.lookup_atom x ctx with
        | Some j -> Atom j
        | None -> assert false
      end

    | TT.Constant c -> Constant c

    | TT.TermConstructor (c, args) ->
       assert false (* XXX to do *)

    | TT.TermAbstract ((x,a),(e,b)) ->
      let ja = WeakIsType (ctx, a) in
      let WeakIsAtom (ctx, y, _) as jy = Ctx.add_weak ja x in
      let b = TT.unabstract_ty [y] b
      and e = TT.unabstract [y] e in
      let je = WeakIsTerm (ctx, e, b) in
      Abstract (strengthen_atom jy, strengthen je)

    | TT.Bound _ -> assert false

let invert_is_type (IsType (ctx, ty)) =
  match ty.Location.thing.TT.thing with

  | TT.Type -> Type

  | TT.TypeConstructor (c, args) ->
     assert false (* XXX to do *)

  | TT.TypeAbstract ((x,a),b) ->
     let ja = WeakIsType (ctx, a) in
     let WeakIsAtom (ctx, y, _) as jy = Ctx.add_weak ja x in
     let b = TT.unabstract_ty [y] b in
     let jb = WeakIsType (ctx, b) in
     AbstractTy (strengthen_atom jy, strengthen_ty jb)

  | TT.El e -> El (IsTerm (ctx, e, TT.mk_type ~loc:e.Location.loc))

let invert_eq_type (EqType (ctx, ty1, ty2)) =
  let j1 = strengthen_ty (WeakIsType (ctx, ty1))
  and j2 = strengthen_ty (WeakIsType (ctx, ty2))
  in j1, j2

let invert_eq_term (EqTerm (ctx, e1, e2, ty)) =
  let j1 = strengthen (WeakIsTerm (ctx, e1, ty))
  and j2 = strengthen (WeakIsTerm (ctx, e2, ty))
  and jt = strengthen_ty (WeakIsType (ctx, ty))
  in (j1, j2, jt)

let invert_abstract_ty j =
  match invert_is_type j with
  | AbstractTy (a, b) -> Some (a, b)
  | (TyConstructor _ | Type | El _) -> None

(** Construct judgements *)
let form_is_term ~loc sgn = function
  | Atom x -> atom_is_term ~loc x

  | Constant c ->
    let t = Signature.constant_type c sgn in
    IsTerm (Ctx.empty, TT.mk_constant ~loc c,t)

 | TermConstructor (c, args) ->
    assert false (* XXX to do *)

  | Abstract ((IsAtom (ctxa,x,a)),(IsTerm (ctxe,e,b))) ->
    let ctx = Ctx.join ~loc ctxe ctxa in
    let ctx = Ctx.abstract ~loc ctx x a in
    let b = TT.abstract_ty [x] b
    and e = TT.abstract [x] e in
    let x = Name.ident_of_atom x in
    IsTerm (ctx, TT.mk_abstract ~loc x a e b, TT.mk_abstract_ty ~loc x a b)

let form_is_type ~loc sgn = function
  | Type ->
    IsType (Ctx.empty, TT.mk_type ~loc)

  | TyConstructor (c, args) ->
     assert false (* XXX to do *)

  | AbstractTy ((IsAtom (ctxa,x,a)),(IsType (ctxb,b))) ->
    let ctx = Ctx.join ~loc ctxb ctxa in
    let ctx = Ctx.abstract ~loc ctx x a in
    let b = TT.abstract_ty [x] b in
    IsType (ctx, TT.mk_abstract_ty ~loc (Name.ident_of_atom x) a b)

  | El (IsTerm (ctx, e, t)) ->
     if TT.alpha_equal_ty t TT.typ
     then
       IsType (ctx, TT.mk_el ~loc e)
     else
       error ~loc NotAType

(** Substitution *)
let substitute_ty ~loc (IsType (ctxt, t)) (IsAtom (_, a, _)) (IsTerm (_, s, _) as js) =
  let ctxt = Ctx.substitute ~loc ctxt a js in
  let t = TT.substitute_ty [a] [s] t in
  strengthen_ty (WeakIsType (ctxt, t))

let substitute ~loc (IsTerm (ctxe, e, t)) (IsAtom (_, a, _)) (IsTerm (_, s, _) as js) =
  let ctxe = Ctx.substitute ~loc ctxe a js in
  let t = TT.substitute_ty [a] [s] t
  and e = TT.substitute [a] [s] e in
  strengthen (WeakIsTerm (ctxe, e, t))

(** Conversion *)

type side = LEFT | RIGHT

let eq_term_side side (EqTerm (ctx, lhs, rhs, ty)) =
  let term = match side with LEFT -> lhs | RIGHT -> rhs in
  strengthen (WeakIsTerm (ctx, term, ty))

let eq_term_typeof (EqTerm (ctx, _, _, ty)) =
  strengthen_ty (WeakIsType (ctx, ty))

let eq_type_side side (EqType (ctx, lhs, rhs)) =
  let ty = match side with LEFT -> lhs | RIGHT -> rhs in
  strengthen_ty (WeakIsType (ctx, ty))

let convert ~loc (IsTerm (ctx1, e, t)) (EqType (ctx2, t1, t2)) =
  if not (TT.alpha_equal_ty t t1)
  then error ~loc (InvalidConvert (t, t1))
  else
    let ctx = Ctx.join ~loc ctx1 ctx2 in
    let e = TT.mention_atoms (Ctx.as_set ctx2) e in
    IsTerm (ctx, e, t2)

let convert_eq ~loc (EqTerm (ctx1, e1, e2, ty)) (EqType (ctx2, t1, t2)) =
  if not (TT.alpha_equal_ty ty t1)
  then error ~loc (InvalidConvert (ty, t1))
  else
    let hyps2 = Ctx.as_set ctx2 in
    let e1 = TT.mention_atoms hyps2 e1
    and e2 = TT.mention_atoms hyps2 e2
    and ctx = Ctx.join ~loc ctx1 ctx2 in
    EqTerm (ctx, e1, e2, t2)

(** Constructors *)

let reflexivity (IsTerm (ctx, e, t)) =
  EqTerm (ctx, e, e, t)

let reflexivity_ty (IsType (ctx, t)) =
  EqType (ctx, t, t)

let mk_alpha_equal_ty ~loc (IsType (ctx1, t1)) (IsType (ctx2, t2)) =
  match TT.alpha_equal_ty t1 t2 with
  | false -> None
  | true ->
     let ctx = Ctx.join ~loc ctx1 ctx2 in
     Some (EqType (ctx, t1, t2))

let mk_alpha_equal ~loc (IsTerm (ctx1, e1, ty1)) (IsTerm (ctx2, e2, ty2)) =
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

let alpha_equal_is_term (IsTerm (_, e1, _)) (IsTerm (_, e2, _)) =
  TT.alpha_equal e1 e2

let alpha_equal_is_type (IsType (_, t1)) (IsType (_, t2)) =
  TT.alpha_equal_ty t1 t2

let alpha_equal_eq_type ~loc (IsType (ctx1, t1)) (IsType (ctx2, t2)) =
  if not (TT.alpha_equal_ty t1 t2)
  then
    None
  else
    let ctx = Ctx.join ~loc ctx1 ctx2 in
    Some (EqType (ctx, t1, t2))

let symmetry_term (EqTerm (ctx, e1, e2, t)) = EqTerm (ctx, e2, e1, t)

let symmetry_type (EqType (ctx, t1, t2)) = EqType (ctx, t2, t1)

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

let transitivity_type ~loc (EqType (ctx1, t1, t2)) (EqType (ctx2, u1, u2)) =
  begin match TT.alpha_equal_ty t2 u1 with
     | false -> error ~loc (AlphaEqualTypeMismatch (t2, u1))
     | true ->
        let ctx = Ctx.join ~loc ctx1 ctx2 in
        EqType (ctx, t1, u2)
     end

(** Congruence *)

let congr_abstract_type ~loc (EqType (ctxa, ta1, ta2)) (IsAtom (_, x, _)) (IsAtom (_, y, _)) (EqType (ctxb, b1, b2)) =
  let ctxb = Ctx.abstract ~loc ctxb x ta1 in

  let hypsa = Ctx.as_set ctxa in

  let b1 = TT.abstract_ty [x] b1
  and b2 = TT.abstract_ty [y] (TT.substitute_ty [x] [TT.mention_atoms hypsa (TT.mk_atom ~loc y)] b2) in
  let ctx = Ctx.join ~loc ctxa ctxb in
  let lhs = TT.mk_abstract_ty ~loc (Name.ident_of_atom x) ta1 b1
  and rhs = TT.mk_abstract_ty ~loc (Name.ident_of_atom y) ta2 b2 in
  EqType (ctx, lhs, rhs)

let congr_abstract_term ~loc (EqType (ctxa, ta1, ta2))
                 (IsAtom (_, x, _)) (IsAtom (_, y, _))
                 (EqType (ctxb, b1, b2))
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
    and ty = TT.mk_abstract_ty ~loc (Name.ident_of_atom x) ta1 b1 in
    EqTerm (ctx, lhs, rhs, ty)

(** Derivables *)

let natural_type ~loc sgn ctx e =
  match e.Location.thing.TT.thing with
    | TT.Atom x ->
      begin match Ctx.lookup_atom x ctx with
        | Some (IsAtom (_, _, t)) -> t
        | None -> assert false
      end

    | TT.Constant c ->
      Signature.constant_type c sgn

    | TT.TermConstructor (c, args) ->
       assert false (* XXX to do *)

    | TT.TermAbstract ((x,a),(_,b)) ->
      TT.mk_abstract_ty ~loc x a b

    | TT.Bound _ -> assert false

let natural_eq_type ~loc sgn (IsTerm (ctx, e, derived)) =
  let natural = natural_type ~loc sgn ctx e in
  EqType (ctx, natural, derived)

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

  let is_term (IsTerm (ctx, e, ty)) =
    Json.record [("context", context ctx);
                 ("term", TT.Json.term e);
                 ("type", TT.Json.ty ty)]

  let is_type (IsType (ctx, ty)) =
    Json.record [("context", context ctx);
                 ("type", TT.Json.ty ty)]

  let eq_term (EqTerm (ctx, e1, e2, t)) =
    Json.record [("context", context ctx);
                 ("lhs", TT.Json.term e1);
                 ("rhs", TT.Json.term e2);
                 ("type", TT.Json.ty t)]

  let eq_type (EqType (ctx, t1, t2)) =
    Json.record [("context", context ctx);
                 ("lhs", TT.Json.ty t1);
                 ("rhs", TT.Json.ty t2)]

end
