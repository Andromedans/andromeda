type 'a abstraction = 'a TT.abstraction

(** Every judgement enforces that its context is minimal (strengthened). *)

type is_term = TT.term

type is_type = TT.ty

type is_atom = is_type TT.atom

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

(** Premise of a congruence rule. *)
type congr_premise =
  | CongrEqType of eq_type abstraction
  | CongrEqTerm of eq_term abstraction
  | CongrEqEqType of eq_type abstraction * eq_type abstraction
  | CongEqEqTerm of eq_term abstraction * eq_term abstraction

type stump_is_type =
  | TypeConstructor of Name.constructor * premise list

type stump_is_term =
  | TermAtom of is_atom
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
      | TermMeta of meta * argument list (* a previously matched meta-variable, instantiated *)
      | TermBound of bound
      | TermConstructor of Name.constructor * argument list

    and ty =
      | TypeMeta of meta * argument list (* a previously matched meta-variable, instantiated *)
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

(** [typeof sgn e] gives the judgment that the type [t] of [e] is derivable.
    Note that [t] itself gives no evidence that [e] actually has type [t].
    However, the assumptions of [e] are sufficient to show that [e] has
    type [t].  *)
let typeof sgn = function
  | TT.TermAtom {atom_type=t; _} -> t

  | TT.TermBound k ->
     lookup_bound k ctx (* XXX shifting, do we need this case? *)

  | TT.TermConstructor (c, args) ->
     let sch = Signature.lookup_term_constructor c sgn in
     instantiate_schema sch args

  | TT.TermConvert (e, _, t) -> t

(** [natural_type sgn e] gives the judgment that the natural type [t] of [e] is derivable.
    We maintain the invariant that no further assumptions are needed (apart from those
    already present in [e]) to derive that [e] actually has type [t]. *)
let natural_type sgn = function
  | TT.TermAtom {atom_type=t; _} -> t

  | TT.TermBound k ->
     lookup_bound k ctx (* XXX shifting, do we need this case? *)

  | TT.TermConstructor (c, args) ->
     let sch = Signature.lookup_term_constructor c sgn in
     instantiate_schema sch args

  | TT.TermConvert (e, _, _) -> typeof sgn e


let atom_is_type {TT.atom_type=t;_} = t

let atom_is_term = TT.mk_atom

(** Printing *)

let print_is_type ~penv ?max_level abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>%t@]"
              (Print.char_vdash ())
              (TT.print_abstraction
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
              (TT.print_abstraction
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
              (TT.print_abstraction
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
        let t' = natural_type sgn e in
        let eq = TT.mk_eq_type asmp t' t in
        TermConvert (e, eq)

let invert_is_type = function
  | TT.TypeConstructor (c, args) ->
     let premises = invert_args args in
     TypeConstructor (c, premises)

let invert_eq_type eq = eq

let invert_eq_term eq = eq

let invert_abstraction inst_v invert_v = function
  | TT.Abstract (x, t, abstr) ->
     let a = TT.mk_atom (TT.fresh_atom x t) in
     let abstr = TT.instantiate_abstraction inst_v a abstr in
     (Some a, abstr)
  | TT.NotAbstract v -> (None, invert_v v)

(** Construct judgements *)
let form_is_term ~loc sgn = function
  | TermAtom a -> TT.mk_atom a

 | TermConstructor (c, args) ->
    let sch = Signature.lookup_term_constructor c sgn in
    let args = form_args sch args in
    TT.mk_term_constructor c args

 | TermConvert (e, TT.EqType (asmp, t1, t2)) ->
    begin match e with
    | TT.TermConvert (e, asmp0, t0) ->
       if TT.alpha_equal_type t0 t1 then
         (* here we rely on transitivity of equality *)
         let asmp = Assumption.union asmp0 (Assumption.union asmp (TT.assumptions_type t1))
         (* we could have used the assumptions of [t0] instead, because [t0] and [t1] are
            alpha equal, and so either can derive the type. Possible optimizations:
              (i) pick the smaller of the assumptions of [t0] or of [t1],
             (ii) pick the asumptions that are included in [t2]
            (iii) remove assumptions already present in [t2] from the assumption set
          *)
         in
         (* [e] itself is not a [TermConvert] by the maintained invariant. *)
         TT.mk_term_convert e asmp t2
       else
         error ~loc (InvalidConvert (t0, t1))

    | (TT.TermAtom _ | TT.TermBound _ | TT.TermConstructor _) as e ->
       let t0 = natural_type sgn e in
       if TT.alpha_equal_type t0 t1 then
         (* We need not include assumptions of [t1] because [t0] is alpha-equal
            to [t1] so we can use [t0] in place of [t1] if so desired. *)
         (* [e] is not a [TermConvert] by the above pattern-check *)
         TT.mk_term_convert e asmp t2
       else
         error ~loc (InvalidConvert (t0, t1))

    end

let form_is_type ~loc sgn = function
  | TypeConstructor (c, args) ->
     Rule.form_is_type ~loc sgn c args

(** Substitution *)
let substitute_ty ~loc a e0 t =
  TT.substitute_type a e0 t

let substitute_term ~loc a e0 e =
  TT.substitute_term a e0 e

(** Conversion *)

let convert_eq_term ~loc (TT.EqTerm (asmp1, e1, e2, t0)) (TT.EqType (asmp2, t1, t2)) =
  if TT.alpha_equal_type t0 t1 then
    (* We could have used the assumptions of [t0] instead of [t1], see comments in [form_is_term]
       about possible optimizations. *)
    let asmp = Assumption.union asmp1 (Assumption.union asmp2 (TT.assumptions_type t1)) in
    TT.mk_eq_term asmp e1 e2 t2
  else
    error ~loc (InvalidConvert (t0, t1))

(** Constructors *)

let reflexivity sgn e =
  let t = typeof sgn e in
  EqTerm (Assumption.empty, e, e, t)

let reflexivity_type sgn t =
  EqType (Assumption.empty, t, t)

let mk_alpha_eq_type t1 t2 =
  match TT.alpha_equal_type t1 t2 with
  | false -> None
  | true -> Some (EqType (Assumption.empty, t1, t2))

let mk_alpha_equal_term ~loc sgn e1 e2 =
  let t1 = typeof sgn e1
  and t2 = typeof sgn e2
  in
  match TT.alpha_equal_type t1 t2 with
  | false -> error ~loc (AlphaEqualTypeMismatch (t1, t2))
  | true ->
     begin match TT.alpha_equal e1 e2 with
     | false -> None
     | true ->
        (* We may keep the assumptions empty here. One might worry
           that the assumptions needed for [e2 : t2] have to be included,
           but this does not seem to be the case: we have [e2 : t2] and
           [t1 == t2] (without assumptions as they are alpha-equal!),
           hence by conversion [e2 : t1], and whatever assumptions are
           required for [e2 : t2], they're already present in [e2]. *)
        Some (EqTerm (Assumption.empty, e1, e2, t1))
     end

let alpha_equal_is_term = TT.alpha_equal

let alpha_equal_is_type = TT.alpha_equal_type

let symmetry_term (EqTerm (asmp, e1, e2, t)) = EqTerm (asmp, e2, e1, t)

let symmetry_type (EqType (asmp, t1, t2)) = EqType (asmp, t2, t1)

let transitivity_term ~loc (EqTerm (asmp, e1, e2, t)) (EqTerm (asmp', e1', e2', t')) =
  match TT.alpha_equal_type t t' with
  | false -> error ~loc (AlphaEqualTypeMismatch (t, t'))
  | true ->
     begin match TT.alpha_equal e2 e1' with
     | false -> error ~loc (AlphaEqualTermMismatch (e2, e1'))
     | true ->
        (* XXX could use assumptions of [e1'] instead, or whichever is better. *)
        let asmp = Assumption.union asmp (Assumption.union asmp' (TT.assumptions_term e2))
        in EqTerm (asmp, e1, e2', t)
     end

let transitivity_type ~loc (EqType (asmp1, t1, t2)) (EqType (asmp2, u1, u2)) =
  begin match TT.alpha_equal_type t2 u1 with
     | false -> error ~loc (AlphaEqualTypeMismatch (t2, u1))
     | true ->
        (* XXX could use assumptions of [u1] instead, or whichever is better. *)
        let asmp = Assumption.union asmp1 (Assumption.union asmp2 (TT.assumptions_type t2))
        in EqType (asmp, t1, u2)
     end

(** Congruence *)

(** Given a list of (possibly abstracted) equations between arguments, create an equation
   between [c] applied to the arguments of the left-hand sides and the right-hand sides,
   respectively. *)
let congruence_term_constructor sgn c eqs =
  let (asmp, lhs, rhs) =
    List.fold_left
      (fun (asmp, lhs, rhs) (EqTerm (asmp', e1, e2, t)) ->
        let asmp = Assumption.union asmp asmp'
        and e1 =

        (Assumption.union asmp asmp', e1 :: lhs, t2:: rhs))
      (Assumption.empty, [], [])
      eqs
  in
  let t1 = form_type_constructor c lhs
  and t2 = form_type_constructor c rhs
  in EqType (asmp, t1, t2)


(** Given a list of (possibly abstracted) equations between arguments, create an equation
   between [c] applied to the arguments of the left-hand sides and the right-hand sides,
   respectively. *)
let congruence_type_constructor sgn c eqs =
  let (asmp, lhs, rhs) =
    List.fold_left
      (fun (asmp, lhs, rhs) (EqType (asmp', t1, t2)) ->
        (Assumption.union asmp asmp', t1 :: lhs, t2:: rhs))
      (Assumption.empty, [], [])
      eqs
  in
  let t1 = form_type_constructor sgn c lhs
  and t2 = form_type_constructor sgn c rhs
  in EqType (asmp, t1, t2)



  failwith "congruence_type_constructor"

module Json =
struct

  let rec abstraction json_u = function
    | TT.NotAbstract u -> Json.tag "NotAbstract" [json_u u]
    | TT.Abstract (x, t, abstr) ->
       Json.tag "Abstract" [Name.Json.ident x; TT.Json.ty t; abstraction json_u abstr]

  let is_term e = Json.tag "IsTerm" [TT.Json.term e]

  let is_type t = Json.tag "IsType" [TT.Json.ty t]

  let eq_term (EqTerm (asmp, e1, e2, t)) =
    Json.tag "EqTerm" [Assumption.Json.assumptions asmp; TT.Json.term e1; TT.Json.term e2; TT.Json.ty t]

  let eq_type (EqType (asmp, t1, t2)) =
    Json.tag "EqType" [Assumption.Json.assumptions asmp; TT.Json.ty t1; TT.Json.ty t2]

end
