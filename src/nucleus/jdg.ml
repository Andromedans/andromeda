include Jdg_typedefs


let error = TT_error.raise

module Signature = Signature

(** Creation of rules of inference from judgements. *)

(** Manipulation of rules of inference. *)

(** [fully_apply_abstraction inst_u abstr args] fully applies an abstraction to the given arguments. *)
let fully_instantiate_abstraction inst_u abstr args =
  let rec fold es abstr args =
    match abstr, args with
    | NotAbstract u, [] -> inst_u es u
    | Abstract (_, _, abstr), e :: args -> fold (e :: es) abstr args
    | Abstract _, [] -> TT_error.raise TooFewArguments
    | NotAbstract _, _::_ -> TT_error.raise TooManyArguments
  in
  fold [] abstr args


(* Sometimes we work with meta-variables in their _de Bruijn index_ order, i.e.,
   as a list whose first element is de Bruijn index 0, and sometimes we work in
   the _constructor_ order, i.e., in the order of premises to a rule. These
   are reverse from each other. We have found it to be quite error-prone to
   keep track of which order any given list might be, so we use some abstract
   types to reduce the possibility of further bugs.
*)
module Indices :
  sig
    type t
    val nth : t -> int -> argument
    val of_list : argument list -> t
    val to_list : t -> argument list
    val cons : argument -> t -> t
  end
  =
  struct
    type t = argument list
    let nth = List.nth
    let of_list = List.rev
    let to_list = List.rev
    let cons = List.cons
  end

let lookup_term_meta k metas =
  match Indices.nth metas k with
  | ArgumentIsTerm e_abstr -> e_abstr
  | ArgumentIsType _ | ArgumentEqType _ | ArgumentEqTerm _ -> TT_error.raise TermExpected

let lookup_type_meta k metas =
  match Indices.nth metas k with
  | ArgumentIsType t_abstr -> t_abstr
  | ArgumentIsTerm _ | ArgumentEqType _ | ArgumentEqTerm _ -> TT_error.raise TypeExpected

let rec meta_instantiate_is_type ~lvl metas = function
  | Rule.TypeConstructor (c, args) ->
     let args = meta_instantiate_args ~lvl metas args
     in TT_mk.type_constructor c args

  | Rule.TypeMeta (k, es_schema) ->
     let t_abstr = lookup_type_meta k metas in
     let es = List.map (fun e_schema -> meta_instantiate_is_term ~lvl metas e_schema) es_schema in
     fully_instantiate_abstraction (TT_instantiate.type_fully ?lvl:None) t_abstr es

and meta_instantiate_is_term ~lvl metas = function
  | Rule.TermBound k -> TT_mk.bound k

  | Rule.TermConstructor (c, args) ->
     let args = meta_instantiate_args ~lvl metas args
     in TT_mk.term_constructor c args

  | Rule.TermMeta (k, es_schema) ->
     let e_abstr = lookup_term_meta k metas in
     let es = List.map (fun e_schema -> meta_instantiate_is_term ~lvl metas e_schema) es_schema in
     fully_instantiate_abstraction (TT_instantiate.term_fully ?lvl:None) e_abstr es

and meta_instantiate_eq_type ~lvl metas (Rule.EqType (t1, t2)) =
  let t1 = meta_instantiate_is_type ~lvl metas t1
  and t2 = meta_instantiate_is_type ~lvl metas t2 in
  TT_mk.eq_type Assumption.empty t1 t2

and meta_instantiate_eq_term ~lvl metas (Rule.EqTerm (e1, e2, t)) =
  let e1 = meta_instantiate_is_term ~lvl metas e1
  and e2 = meta_instantiate_is_term ~lvl metas e2
  and t = meta_instantiate_is_type ~lvl metas t in
  TT_mk.eq_term Assumption.empty e1 e2 t

and meta_instantiate_args ~lvl metas args =
  List.map (meta_instantiate_arg ~lvl metas) args

and meta_instantiate_arg ~lvl metas = function
  | Rule.ArgumentIsType abstr ->
     let abstr = meta_instantiate_abstraction meta_instantiate_is_type ~lvl metas abstr
     in TT_mk.arg_is_type abstr

  | Rule.ArgumentIsTerm abstr ->
     let abstr = meta_instantiate_abstraction meta_instantiate_is_term ~lvl metas abstr
     in TT_mk.arg_is_term abstr

  | Rule.ArgumentEqType abstr ->
     (* XXX could do this lazily so that it's discarded when it's an
            argument in a premise, and computed only when it's an argument in
            a constructor in the output of a rule *)
     let abstr = meta_instantiate_abstraction meta_instantiate_eq_type ~lvl metas abstr
     in TT_mk.arg_eq_type abstr

  | Rule.ArgumentEqTerm abstr ->
     let abstr = meta_instantiate_abstraction meta_instantiate_eq_term ~lvl metas abstr
     in TT_mk.arg_eq_term abstr

and meta_instantiate_abstraction
    : 'a 'b . (lvl:int -> Indices.t -> 'a -> 'b) ->
      lvl:int -> Indices.t -> 'a Rule.abstraction -> 'b abstraction
  = fun inst_u ~lvl metas -> function

                          | Rule.NotAbstract u ->
                             let u = inst_u ~lvl metas u
                             in TT_mk.not_abstract u

                          | Rule.Abstract (x, t, abstr) ->
                             let t = meta_instantiate_is_type ~lvl metas t
                             and abstr = meta_instantiate_abstraction inst_u ~lvl:(lvl+1) metas abstr
                             in TT_mk.abstract x t abstr

let atom_name {atom_name=n;_} = n

let meta_name m = m.meta_name

(** [type_of_term sgn e] gives a type judgment [t], where [t] is the type of [e].
      Note that [t] itself gives no evidence that [e] actually has type [t].
      However, the assumptions of [e] are sufficient to show that [e] has
      type [t].  *)
let type_of_term sgn = function
  | TermAtom {atom_type=t; _} -> t

  | TermBound k ->
     (* We should never get here. If ever we need to compute the type of a
        term with bound variables, then we should have unabstracted the term
        beforehand, and asked about the type of the unabstracted version. *)
     assert false

  | TermConstructor (c, args) ->
     let (_premises, t_schema) = Signature.lookup_rule_is_term c sgn in
     (* we need not re-check that the premises match the arguments because
        we are computing the type of a term that was previously determined
        to be valid. *)
     let inds = Indices.of_list args in
     meta_instantiate_is_type ~lvl:0 inds t_schema

  | TermMeta ({meta_type;_}, args) ->
     fully_instantiate_abstraction (TT_instantiate.type_fully ?lvl:None) meta_type args

  | TermConvert (e, _, t) -> t


let type_at_abstraction = function
  | NotAbstract _ -> None
  | Abstract (_, t, _) -> Some t

let rec type_of_term_abstraction sgn = function
  | NotAbstract e ->
     let t = type_of_term sgn e in
     TT_mk.not_abstract t

  | Abstract (x, t, abstr) ->
     let a, abstr = TT_unabstract.abstraction TT_instantiate.term x t abstr in
     let t_abstr = type_of_term_abstraction sgn abstr in
     let t_abstr = TT_abstract.abstraction TT_abstract.ty a.atom_name t_abstr in
     TT_mk.abstract x t t_abstr

(** [natural_type sgn e] gives the judgment that the natural type [t] of [e] is derivable.
    We maintain the invariant that no further assumptions are needed (apart from those
    already present in [e]) to derive that [e] actually has type [t]. *)
let natural_type sgn = function
  | (TermAtom _ | TermBound _ | TermConstructor _ | TermMeta _) as e ->
     type_of_term sgn e

  | TermConvert (e, _, _) -> type_of_term sgn e

let natural_type_eq sgn e =
  let natural = natural_type sgn e
  and given = type_of_term sgn e in
  (* XXX should the assumptions here be empty, or the assumptions of [e] ? If
  we derived [e : given] via a conversion, eg

  ⊢ e' : natural   x : False ⊢ natural == given
  --------------------------------------------conv
  x  : False ⊢ e : given

  then we should include the assumptions of [e], i.e. [x], in the assumptions
  of [natural == given]

  NB: We should actually look into [e] and if it's a conversion, grab that
  assumption set.
   *)
  TT_mk.eq_type Assumption.empty natural given

let rec boundary_abstraction boundary_u = function
  | NotAbstract u -> TT_mk.not_abstract (boundary_u u)
  | Abstract (x, t, abstr) ->
     let b = boundary_abstraction boundary_u abstr in
     TT_mk.abstract x t b

let boundary_is_type_abstraction abstr =
  boundary_abstraction (fun _ -> ()) abstr

let boundary_is_term_abstraction sgn abstr =
  (* NB: this is _not_ like the others as it actually computes the type of a term *)
  type_of_term_abstraction sgn abstr

let boundary_eq_type_abstraction abstr = abstr

let boundary_eq_term_abstraction abstr = abstr

(* Check that the argument [p] matches the premise [s]. *)
let check_argument sgn metas s p =
  match s, p with

  | Rule.PremiseIsType s_abstr, ArgumentIsType p_abstr ->
     let s_abstr = meta_instantiate_abstraction (fun ~lvl _ () -> ()) ~lvl:0 metas s_abstr
     and p_abstr = boundary_is_type_abstraction p_abstr in
     if not (TT_alpha_equal.abstraction (fun () () -> true) s_abstr p_abstr) then
       TT_error.raise InvalidArgument

  | Rule.PremiseIsTerm s_abstr, ArgumentIsTerm p_abstr ->
     let s = meta_instantiate_abstraction meta_instantiate_is_type ~lvl:0 metas s_abstr
     and t = boundary_is_term_abstraction sgn p_abstr in
     begin
       match TT_alpha_equal.abstraction TT_alpha_equal.ty t s with
       | false -> TT_error.raise InvalidArgument
       | true -> ()
     end

  | Rule.PremiseEqType s_abstr, ArgumentEqType p_abstr ->
     let s_abstr = meta_instantiate_abstraction meta_instantiate_eq_type ~lvl:0 metas s_abstr
     and p_abstr = boundary_eq_type_abstraction p_abstr in
     if not (TT_alpha_equal.abstraction
               (fun (EqType (_, l1,r1)) (EqType (_, l2,r2)) ->
                 TT_alpha_equal.ty l1 l2 && TT_alpha_equal.ty r1 r2)
               s_abstr p_abstr)
     then
       TT_error.raise InvalidArgument

  | Rule.PremiseEqTerm s_abstr, ArgumentEqTerm p_abstr ->
     let s_abstr = meta_instantiate_abstraction meta_instantiate_eq_term ~lvl:0 metas s_abstr
     and p_abstr = boundary_eq_term_abstraction p_abstr in
     if not (TT_alpha_equal.abstraction
               (fun (EqTerm (_, e1,e2,t)) (EqTerm (_, e1',e2',t')) ->
                 TT_alpha_equal.term e1 e1'
                 && TT_alpha_equal.term e2 e2'
                 && TT_alpha_equal.ty t t')
               s_abstr p_abstr)
     then
       TT_error.raise InvalidArgument

  | Rule.PremiseIsType _, (ArgumentIsTerm _ | ArgumentEqType _ | ArgumentEqTerm _) -> TT_error.raise IsTypeExpected
  | Rule.PremiseIsTerm _, (ArgumentIsType _ | ArgumentEqType _ | ArgumentEqTerm _) -> TT_error.raise IsTermExpected
  | Rule.PremiseEqType _, (ArgumentIsType _ | ArgumentIsTerm _ | ArgumentEqTerm _) -> TT_error.raise EqTypeExpected
  | Rule.PremiseEqTerm _, (ArgumentIsType _ | ArgumentIsTerm _ | ArgumentEqType _) -> TT_error.raise EqTermExpected

let arg_of_argument = function
  | ArgumentIsType t -> TT_mk.arg_is_type t
  | ArgumentIsTerm e -> TT_mk.arg_is_term e
  | ArgumentEqType eq -> TT_mk.arg_eq_type eq
  | ArgumentEqTerm eq-> TT_mk.arg_eq_term eq

let match_argument sgn metas (s : Rule.premise) (p : argument) : argument =
  check_argument sgn metas s p ;
  arg_of_argument p

let match_arguments sgn (premises : Rule.premise list) (arguments : argument list) =
  let rec fold args_out = function
    | [], [] ->
       (* The arguments must _not_ be reversed because we refer to them by meta-variable
          de Bruijn indices, and therefore the last argument must have index 0. *)
       args_out
    | [], _::_ -> TT_error.raise TooManyArguments
    | _::_, [] -> TT_error.raise TooFewArguments
    | premise :: premises, argument :: arguments ->
       let metas = args_out in (* args also serves as the list of collected metas *)
       let argument = match_argument sgn metas premise argument in
       fold (Indices.cons argument args_out) (premises, arguments)
  in
  fold (Indices.of_list []) (premises, arguments)

(** Judgement formation *)

(** Lookup the de Bruijn index of a meta-variable. *)
let lookup_meta_index mv mvs =
  let rec search k = function
    | [] -> assert false
    | mv' :: mvs ->
       if Name.eq_meta mv mv' then
         k
       else
         search (k+1) mvs
  in
  search 0 mvs

(** The [mk_rule_XYZ] functions are auxiliary functions that should not be
   exposed. The external interface exopses the [form_rule_XYZ] functions defined
   below. *)

let rec mk_rule_is_type metas = function
  | TypeConstructor (c, args) ->
     let args = mk_rule_args metas args in
     Rule.TypeConstructor (c, args)

  | TypeMeta (mv, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     let k = lookup_meta_index mv.meta_name metas in
     Rule.TypeMeta (k, args)

and mk_rule_is_term metas = function
  | TermAtom _ ->
     (* this will be gone when we eliminate atoms *)
     failwith "a free atom cannot appear in a rule"

  | TermMeta (mv, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     let k = lookup_meta_index mv.meta_name metas in
     Rule.TermMeta (k, args)

  | TermConstructor (c, args) ->
     let args = mk_rule_args metas args in
     Rule.TermConstructor (c, args)

  | TermBound k ->
     Rule.TermBound k

  | TermConvert (e, asmp, t) ->
     let (free, is_type_meta, is_term_meta, eq_type_meta, eq_term_meta, bound)
       = Assumption.unpack asmp
         (* NB: We do not check that the types of the metas match because we assume that
            the type of a meta never changes. *)
     and metas_set = Name.MetaSet.of_list metas in
     let mem_metas_set mv _bnd = Name.MetaSet.mem mv metas_set in
     begin match Name.AtomMap.is_empty free
                 && Name.MetaMap.for_all mem_metas_set is_type_meta
                 && Name.MetaMap.for_all mem_metas_set is_term_meta
                 && Name.MetaMap.for_all mem_metas_set eq_type_meta
                 && Name.MetaMap.for_all mem_metas_set eq_term_meta
                 && Jdg_typedefs.BoundSet.is_empty bound
     with
     | true -> mk_rule_is_term metas e
     | false -> TT_error.raise ExtraAssumptions
     end

and mk_rule_eq_type metas (EqType (asmp, t1, t2)) =
    let _ = mk_rule_assumptions metas asmp
    and t1 = mk_rule_is_type metas t1
    and t2 = mk_rule_is_type metas t2 in
    Rule.EqType (t1, t2)

and mk_rule_eq_term metas (EqTerm (asmp, e1, e2, t)) =
    let _ = mk_rule_assumptions metas asmp
    and e1 = mk_rule_is_term metas e1
    and e2 = mk_rule_is_term metas e2
    and t = mk_rule_is_type metas t in
    Rule.EqTerm (e1, e2, t)

and mk_rule_assumptions metas asmp =
  Print.error "should check that asmp is a subset of metas or some such@." ;
  ()

and mk_rule_arg metas = function

  | ArgumentIsType abstr ->
     let abstr = mk_rule_abstraction mk_rule_is_type metas abstr in
     Rule.ArgumentIsType abstr

  | ArgumentIsTerm abstr ->
     let abstr = mk_rule_abstraction mk_rule_is_term metas abstr in
     Rule.ArgumentIsTerm abstr

  | ArgumentEqType abstr ->
     let abstr = mk_rule_abstraction mk_rule_eq_type metas abstr in
     Rule.ArgumentEqType abstr

  | ArgumentEqTerm abstr ->
     let abstr = mk_rule_abstraction mk_rule_eq_term metas abstr in
     Rule.ArgumentEqTerm abstr

and mk_rule_args metas args =
  List.map (mk_rule_arg metas) args

and mk_rule_abstraction
 : 'a 'b . (Name.meta list -> 'a -> 'b) -> Name.meta list -> 'a abstraction -> 'b Rule.abstraction
 = fun form_u metas -> function

  | NotAbstract u ->
     let u = form_u metas u in
     Rule.NotAbstract u

  | Abstract (x, t, abstr) ->
     let t = mk_rule_is_type metas t in
     let abstr = mk_rule_abstraction form_u metas abstr in
     Rule.Abstract (x, t, abstr)

let mk_rule_premise metas = function

  | BoundaryIsType abstr ->
     let abstr = mk_rule_abstraction (fun _ () -> ()) metas abstr in
     Rule.PremiseIsType abstr

  | BoundaryIsTerm abstr ->
     let abstr =
       mk_rule_abstraction (fun metas t -> mk_rule_is_type metas t) metas abstr
     in
     Rule.PremiseIsTerm abstr

  | BoundaryEqType abstr ->
     let abstr =
       mk_rule_abstraction
         (fun metas (t1, t2) ->
           let t1 = mk_rule_is_type metas t1
           and t2 = mk_rule_is_type metas t2 in
           Rule.EqType (t1, t2))
         metas abstr
     in
     Rule.PremiseEqType abstr

  | BoundaryEqTerm abstr ->
     let abstr =
       mk_rule_abstraction
         (fun metas (e1, e2, t) ->
           let e1 = mk_rule_is_term metas e1
           and e2 = mk_rule_is_term metas e2
           and t = mk_rule_is_type metas t in
           Rule.EqTerm (e1, e2, t))
         metas abstr
     in
     Rule.PremiseEqTerm abstr

let mk_rule_premises form_u prems u =
  let rec fold metas prems_out = function
    | [] ->
       let u = form_u metas u in
       let prems_out = List.rev prems_out in
       prems_out, u

    | (mv, prem) :: prems ->
       let prem = mk_rule_premise metas prem in
       fold (mv :: metas) (prem :: prems_out) prems
  in
  fold [] [] prems

let form_rule_is_type prems =
  mk_rule_premises (fun _ () -> ()) prems ()

let form_rule_is_term prems t =
  mk_rule_premises mk_rule_is_type prems t

let form_rule_eq_type prems (t1, t2) =
  mk_rule_premises
    (fun metas (t1, t2) ->
      let t1 = mk_rule_is_type metas t1
      and t2 = mk_rule_is_type metas t2 in
      (t1, t2))
    prems
    (t1, t2)

let form_rule_eq_term prems (e1, e2, t) =
  mk_rule_premises
    (fun metas (e1, e2, t) ->
      let e1 = mk_rule_is_term metas e1
      and e2 = mk_rule_is_term metas e2
      and t = mk_rule_is_type metas t in
      (e1, e2, t))
    prems
    (e1, e2, t)

(** Formation of judgements from rules *)

let form_is_type sgn c arguments =
  let prems, () = Signature.lookup_rule_is_type c sgn in
  (* [match_arguments] reverses the order of arguments for the benefit of instantiation *)
  let args = Indices.to_list (match_arguments sgn prems arguments) in
  TT_mk.type_constructor c args

let form_is_term sgn c arguments =
  let (premises, _boundary) = Signature.lookup_rule_is_term c sgn in
  (* [match_arguments] reverses the order of arguments for the benefit of instantiation *)
  let args = Indices.to_list (match_arguments sgn premises arguments) in
  TT_mk.term_constructor c args

let form_eq_type sgn c arguments =
  let (premises, (lhs_schema, rhs_schema)) =
    Signature.lookup_rule_eq_type c sgn in
  let inds = match_arguments sgn premises arguments in
  (* order of arguments not important in [TT_assumption.arguments],
     we could try avoiding a list reversal caused by [Indices.to_list]. *)
  let asmp = TT_assumption.arguments (Indices.to_list inds)
  and lhs = meta_instantiate_is_type ~lvl:0 inds lhs_schema
  and rhs = meta_instantiate_is_type ~lvl:0 inds rhs_schema
  in TT_mk.eq_type asmp lhs rhs

let form_eq_term sgn c arguments =
  let (premises, (e1_schema, e2_schema, t_schema)) =
    Signature.lookup_rule_eq_term c sgn in
  let inds = match_arguments sgn premises arguments in
  (* order of arguments not important in [TT_assumption.arguments],
     we could try avoiding a list reversal caused by [Indices.to_list]. *)
  let asmp = TT_assumption.arguments (Indices.to_list inds)
  and e1 = meta_instantiate_is_term ~lvl:0 inds e1_schema
  and e2 = meta_instantiate_is_term ~lvl:0 inds e2_schema
  and t = meta_instantiate_is_type ~lvl:0 inds t_schema
  in TT_mk.eq_term asmp e1 e2 t

let type_of_atom {atom_type=t;_} = t

(** Construct judgements *)

let form_is_term_atom = TT_mk.atom

let fresh_atom = TT_mk.fresh_atom

let fresh_is_type_meta = TT_mk.fresh_type_meta
let fresh_is_term_meta = TT_mk.fresh_term_meta
let fresh_eq_type_meta = TT_mk.fresh_eq_type_meta
let fresh_eq_term_meta = TT_mk.fresh_eq_term_meta

let rec check_term_arguments sgn abstr args =
  (* NB: We don't actually need to instantiate the body of the abstraction,
     because we only compare the types of the arguments with the abstraction *)
  let inst_u_no_op = fun _e ?lvl u -> u in
  match (abstr, args) with
  | NotAbstract u, [] -> ()
  | Abstract _, [] -> TT_error.raise TooFewArguments
  | NotAbstract _, _::_ -> TT_error.raise TooManyArguments
  | Abstract (x, t, abstr), arg :: args ->
     let t_arg = type_of_term sgn arg in
     if TT_alpha_equal.ty t t_arg
     then
       let abstr = TT_instantiate.abstraction inst_u_no_op arg abstr in
       check_term_arguments sgn abstr args
     else
       TT_error.raise InvalidApplication

let form_is_term_convert sgn e (EqType (asmp, t1, t2)) =
  match e with
  | TermConvert (e, asmp0, t0) ->
     if TT_alpha_equal.ty t0 t1 then
       (* here we rely on transitivity of equality *)
       let asmp = Assumption.union asmp0 (Assumption.union asmp (TT_assumption.ty t1))
       (* we could have used the assumptions of [t0] instead, because [t0] and [t1] are
            alpha equal, and so either can derive the type. Possible optimizations:
              (i) pick the smaller of the assumptions of [t0] or of [t1],
             (ii) pick the asumptions that are included in [t2]
            (iii) remove assumptions already present in [t2] from the assumption set
        *)
       in
       (* [e] itself is not a [TermConvert] by the maintained invariant. *)
       TT_mk.term_convert e asmp t2
     else
       error (InvalidConvert (t0, t1))

  | (TermAtom _ | TermBound _ | TermConstructor _ | TermMeta _) as e ->
     let t0 = natural_type sgn e in
     if TT_alpha_equal.ty t0 t1 then
       (* We need not include assumptions of [t1] because [t0] is alpha-equal
            to [t1] so we can use [t0] in place of [t1] if so desired. *)
       (* [e] is not a [TermConvert] by the above pattern-check *)
       TT_mk.term_convert e asmp t2
     else
       error (InvalidConvert (t0, t1))

let abstract_not_abstract u = TT_mk.not_abstract u

let abstract_is_type {atom_name=x; atom_type=t} abstr =
  (* XXX occurs check?! *)
  let abstr = TT_abstract.abstraction TT_abstract.ty x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let abstract_is_term {atom_name=x; atom_type=t} abstr =
  let abstr = TT_abstract.abstraction TT_abstract.term x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let abstract_eq_type {atom_name=x; atom_type=t} abstr =
  let abstr = TT_abstract.abstraction TT_abstract.eq_type x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let abstract_eq_term {atom_name=x; atom_type=t} abstr =
  let abstr = TT_abstract.abstraction TT_abstract.eq_term x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let abstract_boundary_is_type {atom_name=x; atom_type=t} abstr =
  let abstr = TT_abstract.abstraction (fun _a ?lvl t -> ()) x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let abstract_boundary_is_term {atom_name=x; atom_type=t} abstr =
  let abstr = TT_abstract.abstraction TT_abstract.ty x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let abstract_boundary_eq_type {atom_name=x; atom_type=t} abstr =
  let abstr = TT_abstract.abstraction
      (fun a ?lvl (lhs, rhs) ->
         let lhs = TT_abstract.ty ?lvl a lhs
         and rhs = TT_abstract.ty ?lvl a rhs in
      (lhs, rhs))
      x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let abstract_boundary_eq_term {atom_name=x; atom_type=t} abstr =
  let abstr = TT_abstract.abstraction
      (fun a ?lvl (lhs, rhs, t) ->
         let lhs = TT_abstract.term ?lvl a lhs
         and rhs = TT_abstract.term ?lvl a rhs
         and t = TT_abstract.ty ?lvl a t in
      (lhs, rhs, t))
      x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr


(** Destructors *)

let invert_arg = function
  | ArgumentIsTerm abstr -> ArgumentIsTerm abstr
  | ArgumentIsType abstr -> ArgumentIsType abstr
  | ArgumentEqType abstr -> ArgumentEqType abstr
  | ArgumentEqTerm abstr -> ArgumentEqTerm abstr

let invert_args args = List.map invert_arg args

let invert_is_term sgn = function

  | TermAtom a -> Stump.TermAtom a

  | TermBound _ -> assert false

  | TermConstructor (c, args) ->
     let arguments = invert_args args in
     Stump.TermConstructor (c, arguments)

  | TermMeta (mv, args) ->
     Stump.TermMeta (mv, args)

  | TermConvert (e, asmp, t) ->
     let t' = natural_type sgn e in
     let eq = TT_mk.eq_type asmp t' t in
     Stump.TermConvert (e, eq)

let invert_is_type = function
  | TypeConstructor (c, args) ->
     let arguments = invert_args args in
     Stump.TypeConstructor (c, arguments)
  | TypeMeta (mv, args) -> Stump.TypeMeta (mv, args)

let invert_eq_type (EqType (asmp, t1, t2)) = Stump.EqType (asmp, t1, t2)

let invert_eq_term (EqTerm (asmp, e1, e2, t)) = Stump.EqTerm (asmp, e1, e2, t)

let as_not_abstract = function
  | Abstract _ -> None
  | NotAbstract v -> Some v

let invert_abstraction ?atom_name inst_v = function
  | Abstract (x, t, abstr) ->
     let x = (match atom_name with None -> x | Some y -> y) in
     let a = TT_mk.fresh_atom x t in
     let abstr = TT_instantiate.abstraction inst_v (TT_mk.atom a) abstr in
     Stump.Abstract (a, abstr)
  | NotAbstract v -> Stump.NotAbstract v

let invert_is_type_abstraction ?atom_name t =
  invert_abstraction ?atom_name TT_instantiate.ty t

let invert_is_term_abstraction ?atom_name e =
  invert_abstraction ?atom_name TT_instantiate.term e

let invert_eq_type_abstraction ?atom_name eq =
  invert_abstraction ?atom_name TT_instantiate.eq_type eq

let invert_eq_term_abstraction ?atom_name eq =
  invert_abstraction ?atom_name TT_instantiate.eq_term eq

let context_is_type_abstraction = TT_context.abstraction TT_assumption.ty
let context_is_term_abstraction = TT_context.abstraction TT_assumption.term
let context_eq_type_abstraction = TT_context.abstraction TT_assumption.eq_type
let context_eq_term_abstraction = TT_context.abstraction TT_assumption.eq_term

let occurs_abstraction assumptions_u a abstr =
  let asmp = TT_assumption.abstraction assumptions_u abstr in
  Assumption.mem_atom a.atom_name asmp

let occurs_is_type_abstraction = occurs_abstraction TT_assumption.ty
let occurs_is_term_abstraction = occurs_abstraction TT_assumption.term
let occurs_eq_type_abstraction = occurs_abstraction TT_assumption.eq_type
let occurs_eq_term_abstraction = occurs_abstraction TT_assumption.eq_term


let apply_abstraction inst_u sgn abstr e0 =
  match abstr with
  | NotAbstract _ -> TT_error.raise AbstractionExpected
  | Abstract (x, t, abstr) ->
     begin match TT_alpha_equal.ty t (type_of_term sgn e0) with
     | false -> TT_error.raise InvalidSubstitution
     | true ->  TT_instantiate.abstraction inst_u e0 abstr
     end

let apply_is_type_abstraction sgn abstr e0 =
  apply_abstraction TT_instantiate.ty sgn abstr e0

let apply_is_term_abstraction sgn abstr e0 =
  apply_abstraction TT_instantiate.term sgn abstr e0

let apply_eq_type_abstraction sgn abstr e0 =
  apply_abstraction TT_instantiate.eq_type sgn abstr e0

let apply_eq_term_abstraction sgn abstr e0 =
  apply_abstraction TT_instantiate.eq_term sgn abstr e0

let rec fully_apply_abstraction inst_u sgn abstr = function
  | [] ->
     begin match abstr with
     | NotAbstract eq -> eq
     | Abstract _ -> TT_error.raise TooFewArguments
     end
  | arg :: args ->
     let abstr = apply_abstraction inst_u sgn abstr arg in
     fully_apply_abstraction inst_u sgn abstr args

(** Conversion *)

let convert_eq_term (EqTerm (asmp1, e1, e2, t0)) (EqType (asmp2, t1, t2)) =
  if TT_alpha_equal.ty t0 t1 then
    (* We could have used the assumptions of [t0] instead of [t1], see comments in [form_is_term]
       about possible optimizations. *)
    let asmp = Assumption.union asmp1 (Assumption.union asmp2 (TT_assumption.ty t1)) in
    TT_mk.eq_term asmp e1 e2 t2
  else
    error (InvalidConvert (t0, t1))

(** Meta-variables *)

let form_is_type_meta sgn m args =
  check_term_arguments sgn m.meta_type args ;
  TT_mk.type_meta m args

let form_is_term_meta sgn m args =
  check_term_arguments sgn m.meta_type args ;
  TT_mk.term_meta m args

let form_eq_type_meta sgn {meta_name ; meta_type} args =
  let asmp = Assumption.add_eq_type_meta meta_name meta_type Assumption.empty in
  let (lhs, rhs) =
    let inst_eq_type_boundary e0 ?lvl (lhs, rhs) =
      let lhs = TT_instantiate.ty e0 ?lvl lhs
      and rhs = TT_instantiate.ty e0 ?lvl rhs
      in (lhs, rhs)
    in
    fully_apply_abstraction inst_eq_type_boundary sgn meta_type args
  in
  TT_mk.eq_type asmp lhs rhs

let form_eq_term_meta sgn {meta_name ; meta_type} args =
  let asmp = Assumption.add_eq_term_meta meta_name meta_type Assumption.empty in
  let (lhs, rhs, t) =
    let inst_eq_term_boundary e0 ?lvl (lhs, rhs, t) =
      let lhs = TT_instantiate.term e0 ?lvl lhs
      and rhs = TT_instantiate.term e0 ?lvl rhs
      and t = TT_instantiate.ty e0 ?lvl t
      in (lhs, rhs, t)
    in
    fully_apply_abstraction inst_eq_term_boundary sgn meta_type args
  in
  TT_mk.eq_term asmp lhs rhs t

let meta_eta_expanded instantiate_meta form_meta abstract_meta sgn mv =
  let rec fold args = function

  | NotAbstract u ->
     TT_mk.not_abstract (form_meta sgn mv (List.rev args))

  | Abstract (x, ty, abstr) ->
     let a, abstr =
       TT_unabstract.abstraction instantiate_meta x ty abstr in
     let abstr = fold ((form_is_term_atom a) :: args) abstr in
     let abstr = TT_abstract.abstraction abstract_meta a.atom_name abstr in
     TT_mk.abstract x ty abstr

  in fold [] mv.meta_type

let is_type_meta_eta_expanded =
  meta_eta_expanded
    (fun _e0 ?lvl () -> ())
    form_is_type_meta
    TT_abstract.ty

let is_term_meta_eta_expanded =
  meta_eta_expanded
    TT_instantiate.ty
    form_is_term_meta
    TT_abstract.term

let eq_type_meta_eta_expanded =
  meta_eta_expanded
    (fun e0 ?lvl (lhs, rhs) ->
       TT_instantiate.ty e0 ?lvl lhs,
       TT_instantiate.ty e0 ?lvl rhs)
    form_eq_type_meta
    TT_abstract.eq_type

let eq_term_meta_eta_expanded =
  meta_eta_expanded
    (fun e0 ?lvl (lhs, rhs, t) ->
       TT_instantiate.term e0 ?lvl lhs,
       TT_instantiate.term e0 ?lvl rhs,
       TT_instantiate.ty e0 ?lvl t)
    form_eq_term_meta
    TT_abstract.eq_term


(** Constructors *)

let alpha_equal_term = TT_alpha_equal.term

let alpha_equal_type = TT_alpha_equal.ty

let alpha_equal_abstraction = TT_alpha_equal.abstraction

let mk_alpha_equal_type t1 t2 =
  match TT_alpha_equal.ty t1 t2 with
  | false -> None
  | true -> Some (TT_mk.eq_type Assumption.empty t1 t2)

(** Compare two terms for alpha equality. *)
let mk_alpha_equal_term sgn e1 e2 =
  let t1 = type_of_term sgn e1
  and t2 = type_of_term sgn e2
  in
  (* XXX if e1 and e2 are α-equal, we may apply uniqueness of typing to
     conclude that their types are equal, so we don't have to compute t1, t2,
     and t1 =α= t2. *)
  match TT_alpha_equal.ty t1 t2 with
  | false -> error (AlphaEqualTypeMismatch (t1, t2))
  | true ->
     begin match TT_alpha_equal.term e1 e2 with
     | false -> None
     | true ->
        (* We may keep the assumptions empty here. One might worry
           that the assumptions needed for [e2 : t2] have to be included,
           but this does not seem to be the case: we have [e2 : t2] and
           [t1 == t2] (without assumptions as they are alpha-equal!),
           hence by conversion [e2 : t1], and whatever assumptions are
           required for [e2 : t2], they're already present in [e2]. *)
        Some (TT_mk.eq_term Assumption.empty e1 e2 t1)
     end

let rec mk_alpha_equal_abstraction equal_u abstr1 abstr2 =
  match abstr1, abstr2 with
  | NotAbstract u1, NotAbstract u2 ->
     begin match equal_u u1 u2 with
     | None -> None
     | Some eq -> Some (TT_mk.not_abstract eq)
     end
  | Abstract (x1, t1, abstr1), Abstract (_x2, t2, abstr2) ->
     begin match alpha_equal_type t1 t2 with
     | false -> None
     | true ->
        begin match mk_alpha_equal_abstraction equal_u abstr1 abstr2 with
        | None -> None
        | Some eq -> Some (TT_mk.abstract x1 t1 eq)
        end
     end
  | (NotAbstract _, Abstract _)
  | (Abstract _, NotAbstract _) -> None

let symmetry_term (EqTerm (asmp, e1, e2, t)) = TT_mk.eq_term asmp e2 e1 t

let symmetry_type (EqType (asmp, t1, t2)) = TT_mk.eq_type asmp t2 t1

let transitivity_term (EqTerm (asmp, e1, e2, t)) (EqTerm (asmp', e1', e2', t')) =
  match TT_alpha_equal.ty t t' with
  | false -> error (AlphaEqualTypeMismatch (t, t'))
  | true ->
     begin match TT_alpha_equal.term e2 e1' with
     | false -> error (AlphaEqualTermMismatch (e2, e1'))
     | true ->
        (* XXX could use assumptions of [e1'] instead, or whichever is better. *)
        let asmp = Assumption.union asmp (Assumption.union asmp' (TT_assumption.term e2))
        in TT_mk.eq_term asmp e1 e2' t
     end

let transitivity_type (EqType (asmp1, t1, t2)) (EqType (asmp2, u1, u2)) =
  begin match TT_alpha_equal.ty t2 u1 with
  | false -> error (AlphaEqualTypeMismatch (t2, u1))
  | true ->
     (* XXX could use assumptions of [u1] instead, or whichever is better. *)
     let asmp = Assumption.union asmp1 (Assumption.union asmp2 (TT_assumption.ty t2))
     in TT_mk.eq_type asmp t1 u2
  end

(** Congruence rules *)

let process_congruence_args args =

  let rec check_endpoints check t1 t2 eq =
    match t1, t2, eq with
    | NotAbstract t1, NotAbstract t2, NotAbstract eq ->
       if not (check t1 t2 eq) then TT_error.raise InvalidCongruence
    | Abstract (_x1, u1, t1), Abstract (_x2, u2, t2), Abstract (_x', u', eq) ->
       if TT_alpha_equal.ty u1 u' || TT_alpha_equal.ty u2 u' then
         check_endpoints check t1 t2 eq
       else
         TT_error.raise InvalidCongruence
    | _, _, _ -> TT_error.raise InvalidCongruence

  in
  let rec fold asmp_out lhs rhs = function

    | [] -> (asmp_out, List.rev lhs, List.rev rhs)

    | CongrIsType (t1, t2, eq) :: eqs ->
       check_endpoints
         (fun t1 t2 (EqType (_, t1', t2')) ->
           TT_alpha_equal.ty t1 t1' && TT_alpha_equal.ty t2 t2')
         t1 t2 eq ;
       let asmp_out = Assumption.union asmp_out (TT_assumption.abstraction TT_assumption.eq_type eq)
       in fold asmp_out (ArgumentIsType t1 :: lhs) (ArgumentIsType t2 :: rhs) eqs

    | CongrIsTerm (e1, e2, eq) :: eqs ->
       check_endpoints
         (fun e1 e2 (EqTerm (_, e1', e2', _)) ->
           TT_alpha_equal.term e1 e1' && TT_alpha_equal.term e2 e2')
         e1 e2 eq ;
       let asmp_out = Assumption.union asmp_out (TT_assumption.abstraction TT_assumption.eq_term eq)
       in fold asmp_out (ArgumentIsTerm e1 :: lhs) (ArgumentIsTerm e2 :: rhs) eqs

    | CongrEqType (eq1, eq2) :: eqs ->
       let l = ArgumentEqType eq1
       and r = ArgumentEqType eq2
       in fold asmp_out (l :: lhs) (r :: rhs) eqs

    | CongrEqTerm (eq1, eq2) :: eqs ->
       let l = ArgumentEqTerm eq1
       and r = ArgumentEqTerm eq2
       in fold asmp_out (l :: lhs) (r :: rhs) eqs

  in fold Assumption.empty [] [] args


let congruence_type_constructor sgn c eqs =
  let (asmp, lhs, rhs) = process_congruence_args eqs in
  let t1 = form_is_type sgn c lhs
  and t2 = form_is_type sgn c rhs
  in TT_mk.eq_type asmp t1 t2

let congruence_term_constructor sgn c eqs =
  let (asmp, lhs, rhs) = process_congruence_args eqs in
  let e1 = form_is_term sgn c lhs
  and e2 = form_is_term sgn c rhs in
  let t = type_of_term sgn e1
  in TT_mk.eq_term asmp e1 e2 t

(** Printing functions *)

let print_is_type ?max_level ~penv t ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>@[<hov>%t@]@;<1 -2> type@]"
              (Print.char_vdash ())
              (TT_print.ty ~max_level:Level.highest ~penv t)

let print_is_term ?max_level ~penv e ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hov 4>%t@]"
              (Print.char_vdash ())
              (TT_print.term ~max_level:Level.highest ~penv e)

let print_eq_type ?max_level ~penv eq ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>%t@]"
              (Print.char_vdash ())
              (TT_print.eq_type ~max_level:Level.highest ~penv eq)

let print_eq_term ?max_level ~penv eq ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>%t@]"
              (Print.char_vdash ())
              (TT_print.eq_term ~max_level:Level.highest ~penv eq)

let print_is_type_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  TT_print.abstraction TT_occurs.ty print_is_type ?max_level ~penv abstr ppf

let print_is_term_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  TT_print.abstraction TT_occurs.term print_is_term ?max_level ~penv abstr ppf

let print_eq_type_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  TT_print.abstraction TT_occurs.eq_type print_eq_type ?max_level ~penv abstr ppf

let print_eq_term_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  TT_print.abstraction TT_occurs.eq_term print_eq_term ?max_level ~penv abstr ppf

let print_error = TT_print.error

module Json = TT_json.Json
