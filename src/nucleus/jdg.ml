type 'a abstraction = 'a TT.abstraction

(** Every judgement enforces that its context is minimal (strengthened). *)

type is_term = TT.term

type is_type = TT.ty

type eq_type = TT.eq_type

type eq_term = TT.eq_term


(** Stumps (defined below) are used to construct and invert judgements. The
   [form_XYZ] functions below take a stump and construct a judgement from it,
   whereas the [invert_XYZ] functions do the opposite. We can think of stumps as
   "stumps", i.e., the lowest level of a derivation tree. *)

(** Premises of a constructor. *)
type premise =
  | PremiseIsType of is_type abstraction
  | PremiseIsTerm of is_term abstraction
  | PremiseEqType of eq_type abstraction
  | PremiseEqTerm of eq_term abstraction

type stump_is_type =
  | TypeConstructor of Name.constructor * premise list

type stump_is_term =
  | TermAtom of is_type TT.atom
  | TermConstructor of Name.constructor * premise list
  | TermConvert of is_term * eq_type

type stump_eq_type =
  | EqType of TT.assumption * is_type * is_type

type stump_eq_term =
  | EqTerm of TT.assumption * is_term * is_term * is_type

(** Error messages emitted by this module. *)

type error =
  | ConstantDependency
  | AbstractDependency of Name.atom * Name.atom list
  | AbstractInvalidType of Name.atom * TT.ty * TT.ty
  | SubstitutionDependency of Name.atom * TT.term * Name.atom
  | SubstitutionInvalidType of Name.atom * TT.ty * TT.ty
  | NotAType
  | AlphaEqualTypeMismatch of TT.ty * TT.ty
  | AlphaEqualTermMismatch of TT.term * TT.term
  | InvalidConvert of TT.ty * TT.ty
  | RuleInputMismatch of string * TT.ty * string * TT.ty * string
  | SubstitutionAbstractedTerm of Name.atom * is_term
  | NotAbstractExpected

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

module Rule = struct

  module Schema = struct

    type meta = int (* meta-variables appearing in rules *)
    type bound = int

    type 'a abstraction =
      | NotAbstract of 'a
      | Abstract of Name.ident * 'a abstraction

    type term =
      | TermMeta of meta (* a previously matched meta-variable *)
      | TermBound of bound
      | TermInstantiate of term * argument list
      | TermConstructor of Name.constructor * argument list

    and ty =
      | TypeMeta of meta (* a previously matched meta-variable *)
      | TypeInstantiate of ty * argument list
      | TypeConstructor of Name.constructor * argument list

    and argument =
      | ArgIsType of ty abstraction
      | ArgIsTerm of term abstraction
      | ArgEqType of unit abstraction
      | ArgEqTerm of unit abstraction

    type 'a premise_abstraction =
      | PremiseNotAbstract of 'a
      | PremiseAbstract of (Name.ident * ty) * 'a premise_abstraction

    and premise =
      | PremiseIsType of Name.ident premise_abstraction
      | PremiseIsTerm of (Name.ident * ty) premise_abstraction
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

  let rec check_type
    : TT.argument list -> Schema.ty -> TT.ty -> unit
    = fun metas t_schema t ->
    match t_schema, t with

      | Schema.TypeMeta m, t ->
         (* lookup m and compare with t, they should be equal *)
         assert false

      | Schema.TypeConstructor (c, premises), TT.TypeConstructor (c', args) ->
         begin
           match Name.eq_ident c c' with
           | false -> failwith "match failure, we wish we had a location"
           | true -> check_premises metas premises args
         end

      | _, _ -> failwith "put an error message here"

  and check_term metas e_schema e =
    match e_schema, e with

    | Schema.TermMeta m, e ->
       assert false

    | Schema.TermConstructor (c, premises), TT.TermConstructor (c', args) ->
         begin
           match Name.eq_ident c c' with
           | false -> failwith "match failure, we wish we had a location"
           | true -> check_premises metas premises args
         end

    | _, _ -> failwith "put an error message here" (* Consider other values, such as TT.Atom! *)

  and check_premises metas premises args =
    match premises, args with
    | [], [] -> ()
    | premise :: premises, arg :: args -> check_premise metas premise arg
    | [], _::_ -> failwith "too many arguments are applied to this constructor"
    | _::_, [] -> failwith "too few arguments are applied to this constructor"

  and check_premise
    : TT.argument list -> Schema.argument -> TT.argument -> unit
    = fun metas premise arg ->
    match premise, arg with
    | Schema.ArgIsType t_schema, TT.ArgIsType t -> check_abstraction check_type metas t_schema t
    | Schema.ArgIsTerm e_schema, TT.ArgIsTerm e -> check_abstraction check_term metas e_schema e
    | Schema.ArgEqType eq_schema, TT.ArgEqType eq -> check_abstraction check_eq_type metas eq_schema eq
    | Schema.ArgEqTerm eq_schema, TT.ArgEqTerm eq -> check_abstraction check_eq_term metas eq_schema eq
    | _, _ -> failwith "place an error message here"

  and check_eq_type _metas () _ = ()

  and check_eq_term _metas () _ = ()

  and check_abstraction :
    'a 'b . (TT.argument list -> 'a -> 'b -> unit) -> TT.argument list ->
            'a Schema.abstraction -> 'b TT.abstraction -> unit =
    fun check_u metas abstr_schema abstr ->
    let rec fold metas abstr_schema abstr =
      match abstr_schema, abstr with
      | Schema.NotAbstract u_schema, TT.NotAbstract u -> check_u metas u_schema u
      | Schema.Abstract (_, abstr_schema), TT.Abstract (_, abstr) -> fold metas abstr_schema abstr
      | _, _ -> failwith "place an error message here"
    in
    fold metas abstr_schema abstr

  let rec match_premise_abstraction
    : (TT.argument list -> 'schema_jdg_form -> 'premise_jdg_form -> TT.argument)
        -> TT.argument list
        -> 'schema_jdg_form Schema.premise_abstraction
        -> 'premise_jdg_form abstraction
        -> TT.argument
      = fun match_jdg metas schema abstr ->
      match schema, abstr with

      | Schema.PremiseNotAbstract jdg_schema, NotAbstract jdg ->
         let jdg = match_jdg metas jdg_schema jdg in
         jdg

      | Schema.PremiseAbstract ((_, t_schema), schema), Abstract ((x, t), abstr) ->
         check_type metas t_schema t ;
         let abstr = match_premise_abstraction match_jdg metas schema abstr in
         (* [abstr] is a TT.argument, we need to abstract it by [x] *)
         TT.mk_abstract_argument x abstr

      | _, _ ->
         failwith "premise match fail"

  let match_is_type
    : TT.argument list -> Name.ident -> TT.ty -> TT.argument
    = fun metas _x t ->
    TT.mk_arg_is_type t

  let match_is_term metas t_schema (e, t) =
    check_type metas t_schema t ;
    TT.mk_arg_eq_term e

  let match_eq_type metas (t1_schema, t2_schema) (t1, t2) =
    check_type metas t1_schema t1 ;
    check_type metas t2_schema t2 ;
    TT.mk_arg_eq_type ()

  let match_eq_term metas (e1_schema, e2_schema, t_schema) (e1, e2, t) =
    check_type metas t_schema t ;
    check_term metas e1_schema e1 ;
    check_term metas e2_schema e2 ;
    TT.mk_arg_eq_term ()

  let rec match_eq_type = failwith "todo"

  let rec match_is_term = failwith "todo"

  let match_premise ~loc metas_ctx metas premise_schema premise =
    let ctx, m =
      match premise_schema, premise with

      | Schema.PremiseIsType t_schema, PremiseIsType (IsType (ctx, abstr)) ->
         ctx, match_premise_abstraction match_is_type metas t_schema abstr

      | Schema.PremiseIsTerm e_schema, PremiseIsTerm (IsTerm (ctx, abstr)) ->
         ctx, match_premise_abstraction match_is_term metas e_schema abstr

      | Schema.PremiseEqType eqty_schema, PremiseEqType (EqType (ctx, eqty)) ->
         ctx, match_premise_abstraction match_eq_type metas eqty_schema eqty

      | Schema.PremiseEqTerm eqterm_schema, PremiseEqTerm (EqTerm (ctx, eqterm)) ->
         ctx, match_premise_abstraction match_eq_term metas eqterm_schema eqterm

      | _, _ ->
         failwith "wrong premise form"
    in
    let ctx = Ctx.join ~loc metas_ctx ctx in
    ctx, m

  (* Form a type according to [rule_schema]. Previously provided premises may
     be referred to by de Bruijn indices pointing into [metas]. *)
  let rec form_is_type' ~loc ctx metas rule_schema premises =
    match rule_schema, premises with

    | Schema.RuleNotAbstract (), [] -> ctx, List.rev metas

    | Schema.RuleAbstract ((_, premise_schema), rule_schema), premise :: premises ->
       let ctx, m = match_premise ~loc ctx metas premise_schema premise in
       form_is_type' ~loc ctx (m :: metas) rule_schema premises

    | Schema.RuleNotAbstract (), _::_ ->
       failwith "this type constructor is applied to too many arguments"

    | Schema.RuleAbstract _, [] ->
       failwith "this type constructor is applied to too few arguments"


  (* Given a type rule and a list of premises, match the rule against the given
   premises, make sure they fit the rule, and form the type. *)
  let form_is_type ~loc c (rule : Schema.is_type) premises =
    let ctx, args = form_is_type' ~loc Ctx.empty [] rule premises in
    TT.mk_type_constructor c args

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

let natural_type sgn = function
  | TT.TermAtom (_, t) -> t

  | TT.TermBound k ->
     lookup_bound k ctx (* XXX shifting, do we need this case? *)

  | TT.TermConstructor (c, args) ->
     let sch = Signature.lookup_term_constructor c sgn in
     instantiate_schema sch args

  | TT.TermConvert (_, _, t) -> t

let atom_is_type (x,t) = TT.mk_not_abstract t

let atom_is_term (x,t) = TT.mk_not_abstract (TT.mk_atom x t)

(** Printing *)

(** [print_abstraction occurs_v print_v ?max_level ~penv abstr ppf] prints an abstraction using formatter [ppf]. *)
let print_abstraction occurs_v print_v ~penv ?max_level abstr ppf =
  TT.print_abstraction
    TT.occurs_type
    print_binder
    occurs_v
    print_v
    ?max_level
    ~penv
    abstr
    ppf

let print_is_type ~penv ?max_level abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>%t@]"
              (Print.char_vdash ())
              (print_abstraction
                 TT.occurs_type
                 (fun ?max_level ~penv t ppf ->
                   Print.print ppf "@[<hv>@[<hov>%t@]@;<1 -2>: type@]"
                     (TT.print_type ~max_level:Level.highest ~penv t)
                 )
                 ~max_level:Level.highest
                 ~penv
                 abstr)

let print_eq_term ~penv ?max_level abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>%t@]"
              (Print.char_vdash ())
              (print_abstraction
                 (fun k (e1, e2, t) -> TT.occurs_term k e1 || TT.occurs_term k e2 || TT.occurs_type k t)
                 (fun ?max_level ~penv (e1, e2, t) ppf ->
                   Print.print ppf "@[<hv>@[<hov>%t@]@ %s@ @[<hov>%t@]@ :@ @[<hov>%t@]@]"
                     (TT.print_term ~penv e1)
                     (Print.char_equal ())
                     (TT.print_term ~penv e2)
                     (TT.print_type ~penv t)
                 )
                 ~penv
                 ~max_level:Level.highest
                 abstr)

let print_eq_type ~penv ?max_level abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>%t@]"
              (Print.char_vdash ())
              (print_abstraction
                 (fun k (t1, t2) -> TT.occurs_type k t1 || TT.occurs_type k t2)
                 (fun ?max_level ~penv (t1, t2) ppf ->
                   Print.print ppf "@[<hv>@[<hov>%t@]@ %s@ @[<hov>%t@]@]"
                     (TT.print_type ~penv t1)
                     (Print.char_equal ())
                     (TT.print_type ~penv t2)
                 )
                 ~penv
                 ~max_level:Level.highest
                 abstr)

let print_error ~penv err ppf =
  match err with

  | ConstantDependency ->
     Format.fprintf ppf "constants may not depend on assumptions"

  | NotAType -> Format.fprintf ppf "Not a type."

  | AbstractInvalidType (x, t1, t2) ->
     Format.fprintf ppf "cannot abstract@ %t@ with type@ %t@ because it must have type@ %t"
        (Name.print_atom ~printer:penv.TT.atoms x)
        (TT.print_type ~penv t1)
        (TT.print_type ~penv t2)

  | SubstitutionDependency (x, e, y) ->
     Format.fprintf ppf "cannot substitute@ %t@ with@ %t,@ dependency cycle at@ %t"
                (Name.print_atom ~printer:penv.TT.atoms x)
                (TT.print_term ~penv e)
                (Name.print_atom ~printer:penv.TT.atoms y)

  | SubstitutionInvalidType (x, x_ty, t) ->
     Format.fprintf ppf "cannot substitute term of type %t for %t of type %t"
                    (TT.print_type ~penv t)
                    (Name.print_atom ~printer:penv.TT.atoms x)
                    (TT.print_type ~penv x_ty)

  | InvalidConvert (t1, t2) ->
    Format.fprintf ppf "Trying to convert something at@ %t@ using an equality on@ %t@."
      (TT.print_type ~penv t1) (TT.print_type ~penv t2)

  | AlphaEqualTypeMismatch (t1, t2) ->
    Format.fprintf ppf "The types@ %t@ and@ %t@ should be alpha equal."
      (TT.print_type ~penv t1) (TT.print_type ~penv t2)

  | AlphaEqualTermMismatch (e1, e2) ->
    Format.fprintf ppf "The terms@ %t@ and@ %t@ should be alpha equal."
      (TT.print_term ~penv e1) (TT.print_term ~penv e2)

  | RuleInputMismatch (rule, t1, desc1, t2, desc2) ->
    Format.fprintf ppf "@[<v>In the %s rule, the following types should be identical\
:@,   @[<hov>%t@]@ (%s) and@,   @[<hov>%t@]@ (%s)@]@."
      rule (TT.print_type ~penv t1) desc1 (TT.print_type ~penv t2) desc2

(** Destructors *)

let invert_arg = function
  | TT.ArgIsTerm abstr -> PremiseIsTerm abstr
  | TT.ArgIsType abstr -> PremiseIsType abstr
  | TT.ArgEqType abstr -> PremiseEqType abstr
  | TT.ArgEqTerm abstr -> PremiseEqTerm abstr

let invert_args args = List.map invert_arg args

let invert_is_term sgn = function

  | TT.TermAtom a -> TermAtom a

  | TT.TermBound _ -> assert false

  | TT.TermConstructor (c, args) ->
     let premises = invert_args args in
     TermConstructor (c, premises)

  | TT.TermConvert (e, asmp, t) ->
        let t' = natural_type e in
        let e = TT.mk_not_abstract e in
        let eq = TT.mk_not_abstract (TT.mk_eq_type asmp t' t) in
        TermConvert (e, eq)

let invert_is_type = function
  | TT.TypeConstructor (c, args) ->
     let premises = invert_args args in
     TypeConstructor (c, premises)

let invert_eq_type eq = eq

let invert_eq_term eq = eq

let invert_abstraction inst_v invert_v = function
  | TT.Abstract (x, t, abstr) ->
     let a = TT.mk_atom x t in
     let abstr = TT.instantiate_abstraction inst_v a abstr in
     (Some a, abstr)
  | TT.NotAbstract v -> (None, invert_v v)

(** Construct judgements *)
let form_is_term sgn = function
  | TermAtom (x, t) -> TT.mk_not_abstract (TT.mk_atom x t)

 | TermConstructor (c, args) ->
    let sch = Signature.lookup_term_constructor c sgn in
    let args = form_args sch args in
    TT.mk_not_abstract (TT.mk_term_constructor c args)

  | TermAbstract ((x, t), e) ->
     let x = Name.ident_of_atom x in
     TT.mk_abstract x t e


let form_is_type ~loc sgn = function
  | TypeConstructor (c, args) ->
     Rule.form_is_type ~loc c args

  | AbstractTy ((IsAtom (ctxa,x,a)),(IsType (ctxb,b))) ->
    let ctx = Ctx.join ~loc ctxb ctxa in
    let ctx = Ctx.abstract ~loc ctx x a in
    let b = TT.abstract_ty x b in
    IsType (ctx, TT.mk_abstract_ty ~loc (Name.ident_of_atom x) a b)

(** Substitution *)
let substitute_ty ~loc (IsType (ctxt, t)) (IsAtom (_, a, _)) (IsTerm (_, s, _) as js) =
  let ctxt = Ctx.substitute ~loc ctxt a js in
  let t = TT.substitute_ty a s t in
  strengthen_ty (WeakIsType (ctxt, t))

let substitute ~loc (IsTerm (ctxe, e, t)) (IsAtom (_, a, _)) (IsTerm (_, s, _) as js) =
  let ctxe = Ctx.substitute ~loc ctxe a js in
  let t = TT.substitute_ty a s t
  and e = TT.substitute a s e in
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

  let b1 = TT.abstract_ty x b1
  and b2 = TT.abstract_ty y (TT.substitute_ty x (TT.mention_atoms hypsa (TT.mk_atom ~loc y)) b2) in
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
    let e1 = TT.abstract x e1
    and e2 = TT.abstract y (TT.substitute x y_mentions e2)
    and b1 = TT.abstract_ty x b1
    and b2 = TT.abstract_ty x (TT.substitute_ty x y_mentions b2) in
    let lhs = TT.mk_abstract ~loc (Name.ident_of_atom x) ta1 e1 b1
    and rhs = TT.mention_atoms hypsab (TT.mk_abstract ~loc (Name.ident_of_atom y) ta2 e2 b2)
    and ty = TT.mk_abstract_ty ~loc (Name.ident_of_atom x) ta1 b1 in
    EqTerm (ctx, lhs, rhs, ty)

module Json =
struct

  let rec abstraction json_u = function
    | NotAbstract u -> Json.tag "NotAbstract" [json_u u]
    | Abstract ((x, t), abstr) ->
       Json.tag "Abstract" [Name.Json.ident x; TT.Json.ty t; abstraction json_u abstr]

  let is_term (IsTerm abstr) =
    abstraction
      (fun (e, ty) -> Json.tag "IsTerm" [TT.Json.term e; TT.Json.ty ty])
      abstr

  let is_type (IsType abstr) =
    abstraction
      (fun ty -> Json.tag "IsType" [TT.Json.ty ty])
      abstr

  let eq_term (EqTerm abstr) =
    abstraction
      (fun (e1, e2, t) -> Json.tag "EqTerm" [TT.Json.term e1; TT.Json.term e2; TT.Json.ty t])
      abstr

  let eq_type (EqType abstr) =
    abstraction
      (fun (t1, t2) -> Json.tag "EqType" [TT.Json.ty t1; TT.Json.ty t2])
      abstr

end
