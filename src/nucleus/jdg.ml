type 'a abstraction = 'a TT.abstraction

(** Every judgement enforces that its context is minimal (strengthened). *)

type is_term = TT.term

type is_type = TT.ty

type is_atom = TT.atom

type is_type_meta = TT.type_meta
type is_term_meta = TT.term_meta
type eq_type_meta = TT.eq_type_meta
type eq_term_meta = TT.eq_term_meta

type eq_type = TT.eq_type

type eq_term = TT.eq_term

type is_term_abstraction = is_term abstraction
type is_type_abstraction = is_type abstraction
type eq_type_abstraction = eq_type abstraction
type eq_term_abstraction = eq_term abstraction

(** Stumps (defined below) are used to construct and invert judgements. The
   [form_XYZ] functions below take a stump and construct a judgement from it,
   whereas the [invert_XYZ] functions do the opposite. We can think of stumps as
   "stumps", i.e., the lowest level of a derivation tree. *)

(** Arguments of a constructor. *)
type argument =
  | ArgumentIsType of is_type abstraction
  | ArgumentIsTerm of is_term abstraction
  | ArgumentEqType of eq_type abstraction
  | ArgumentEqTerm of eq_term abstraction

type 'a meta = 'a TT.meta

type is_type_boundary = unit abstraction
type is_term_boundary = is_type abstraction
type eq_type_boundary = (is_type * is_type) abstraction
type eq_term_boundary = (is_term * is_term * is_type) abstraction

type boundary =
    | BoundaryType of is_type_boundary
    | BoundaryTerm of is_term_boundary
    | BoundaryEqType of eq_type_boundary
    | BoundaryEqTerm of eq_term_boundary

type assumption = (is_type, TT.premise_boundary) Assumption.t

type stump_is_type =
  | TypeConstructor of Name.constructor * argument list
  | TypeMeta of TT.type_meta * is_term list

type stump_is_term =
  | TermAtom of is_atom
  | TermConstructor of Name.constructor * argument list
  | TermMeta of TT.term_meta * is_term list
  | TermConvert of is_term * eq_type

type stump_eq_type =
  | EqType of assumption * is_type * is_type

type stump_eq_term =
  | EqTerm of assumption * is_term * is_term * is_type

type 'a stump_abstraction =
  | NotAbstract of 'a
  | Abstract of is_atom * 'a abstraction

type congruence_argument =
  | CongrIsType of is_type abstraction * is_type abstraction * eq_type abstraction
  | CongrIsTerm of is_term abstraction * is_term abstraction * eq_term abstraction
  | CongrEqType of eq_type abstraction * eq_type abstraction
  | CongrEqTerm of eq_term abstraction * eq_term abstraction

(** Error messages emitted by this module. *)

type error =
  | AlphaEqualTypeMismatch of TT.ty * TT.ty
  | AlphaEqualTermMismatch of TT.term * TT.term
  | InvalidConvert of TT.ty * TT.ty

exception Error of error

let error err = Pervasives.raise (Error err)

module Signature = struct
  module RuleMap = Name.IdentMap

  type t =
    { is_type : Rule.rule_is_type RuleMap.t
    ; is_term : Rule.rule_is_term RuleMap.t
    ; eq_type : Rule.rule_eq_type RuleMap.t
    ; eq_term : Rule.rule_eq_term RuleMap.t
    }

  let empty =
    { is_type = RuleMap.empty
    ; is_term = RuleMap.empty
    ; eq_type = RuleMap.empty
    ; eq_term = RuleMap.empty
    }

  let add_new c rule map = assert (not (RuleMap.mem c map)) ; RuleMap.add c rule map

  let add_rule_is_type c rule sgn = { sgn with is_type = add_new c rule sgn.is_type }
  let add_rule_is_term c rule sgn = { sgn with is_term = add_new c rule sgn.is_term }
  let add_rule_eq_type c rule sgn = { sgn with eq_type = add_new c rule sgn.eq_type }
  let add_rule_eq_term c rule sgn = { sgn with eq_term = add_new c rule sgn.eq_term }

  let lookup_rule_is_type c sgn = RuleMap.find c sgn.is_type
  let lookup_rule_is_term c sgn = RuleMap.find c sgn.is_term
  let lookup_rule_eq_type c sgn = RuleMap.find c sgn.eq_type
  let lookup_rule_eq_term c sgn = RuleMap.find c sgn.eq_term

end (* module Signature *)

(** Creation of rules of inference from judgements. *)

(** Manipulation of rules of inference. *)

(** [fully_apply_abstraction inst_u abstr args] fully applies an abstraction to the given arguments. *)
let fully_instantiate_abstraction inst_u abstr args =
  let rec fold es abstr args =
    match abstr, args with
    | TT.NotAbstract u, [] -> inst_u es u
    | TT.Abstract (_, _, abstr), e :: args -> fold (e :: es) abstr args
    | TT.Abstract _, [] -> failwith "too few arguments"
    | TT.NotAbstract _, _::_ -> failwith "too many arguments"
  in
  fold [] abstr args

let lookup_term_meta k metas =
  match List.nth metas k with
  | TT.ArgIsTerm e_abstr -> e_abstr
  | TT.ArgIsType _ | TT.ArgEqType _ | TT.ArgEqTerm _ -> failwith "term expected"

let lookup_type_meta k metas =
  match List.nth metas k with
  | TT.ArgIsType t_abstr -> t_abstr
  | TT.ArgIsTerm _ | TT.ArgEqType _ | TT.ArgEqTerm _ -> failwith "type expected"

let rec meta_instantiate_is_type ~lvl metas = function
  | Rule.TypeConstructor (c, args) ->
     let args = meta_instantiate_args ~lvl metas args
     in TT.mk_type_constructor c args

  | Rule.TypeMeta (k, es_schema) ->
     let t_abstr = lookup_type_meta k metas in
     let es = List.map (fun e_schema -> meta_instantiate_is_term ~lvl metas e_schema) es_schema in
     fully_instantiate_abstraction (TT.fully_instantiate_type ?lvl:None) t_abstr es

and meta_instantiate_is_term ~lvl metas = function
  | Rule.TermBound k -> TT.mk_bound k

  | Rule.TermConstructor (c, args) ->
     let args = meta_instantiate_args ~lvl metas args
     in TT.mk_term_constructor c args

  | Rule.TermMeta (k, es_schema) ->
     let e_abstr = lookup_term_meta k metas in
     let es = List.map (fun e_schema -> meta_instantiate_is_term ~lvl metas e_schema) es_schema in
     fully_instantiate_abstraction (TT.fully_instantiate_term ?lvl:None) e_abstr es

and meta_instantiate_eq_type ~lvl metas (Rule.EqType (asmp, t1, t2)) =
  let asmp = meta_instantiate_assumptions ~lvl metas asmp
  and t1 = meta_instantiate_is_type ~lvl metas t1
  and t2 = meta_instantiate_is_type ~lvl metas t2 in
  TT.mk_eq_type asmp t1 t2

and meta_instantiate_eq_term ~lvl metas (Rule.EqTerm (asmp, e1, e2, t)) =
  let asmp = meta_instantiate_assumptions ~lvl metas asmp
  and e1 = meta_instantiate_is_term ~lvl metas e1
  and e2 = meta_instantiate_is_term ~lvl metas e2
  and t = meta_instantiate_is_type ~lvl metas t in
  TT.mk_eq_term asmp e1 e2 t

and meta_instantiate_assumptions ~lvl metas asmp =
  failwith "todo"

and meta_instantiate_args ~lvl metas args =
  List.map (meta_instantiate_arg ~lvl metas) args

and meta_instantiate_arg ~lvl metas = function
  | Rule.ArgIsType abstr ->
     let abstr = meta_instantiate_abstraction meta_instantiate_is_type ~lvl metas abstr
     in TT.mk_arg_is_type abstr

  | Rule.ArgIsTerm abstr ->
     let abstr = meta_instantiate_abstraction meta_instantiate_is_term ~lvl metas abstr
     in TT.mk_arg_is_term abstr

  | Rule.ArgEqType abstr ->
     (* XXX could do this lazily so that it's discarded when it's an
            argument in a premise, and computed only when it's an argument in
            a constructor in the output of a rule *)
     let abstr = meta_instantiate_abstraction meta_instantiate_eq_type ~lvl metas abstr
     in TT.mk_arg_eq_type abstr

  | Rule.ArgEqTerm abstr ->
     let abstr = meta_instantiate_abstraction meta_instantiate_eq_term ~lvl metas abstr
     in TT.mk_arg_eq_term abstr

and meta_instantiate_abstraction
    : 'a 'b . (lvl:int -> TT.argument list -> 'a -> 'b) ->
      lvl:int -> TT.argument list -> 'a Rule.abstraction -> 'b TT.abstraction
  = fun inst_u ~lvl metas -> function

                          | Rule.NotAbstract u ->
                             let u = inst_u ~lvl metas u
                             in TT.mk_not_abstract u

                          | Rule.Abstract (x, t, abstr) ->
                             let t = meta_instantiate_is_type ~lvl metas t
                             and abstr = meta_instantiate_abstraction inst_u ~lvl:(lvl+1) metas abstr
                             in TT.mk_abstract x t abstr

let meta_instantiate_terms metas es_schema =
  List.map
    (fun e_schema -> meta_instantiate_is_term ~lvl:0 metas e_schema)
    es_schema


let rec check_type (metas : TT.argument list) (schema : Rule.ty) (argument : TT.ty) =
  match schema, argument with

  | Rule.TypeConstructor (c_schema, args_schema), TT.TypeConstructor (c, args) ->
     if Name.eq_ident c_schema c then
       check_args metas args_schema args
     else
       failwith "some mismatch"

  | Rule.TypeMeta (k, es_schema), ty ->
     begin
       (* XXX TODO List.nth could fail miserably here *)
       match List.nth metas k with

       | TT.ArgIsType abstr ->
          let es = meta_instantiate_terms metas es_schema in
          let ty' = fully_instantiate_abstraction (TT.fully_instantiate_type ?lvl:None) abstr es in
          if not (TT.alpha_equal_type ty ty') then
            failwith "type mismatch"

       | TT.ArgIsTerm _ | TT.ArgEqType _ | TT.ArgEqTerm _ ->
          failwith "expected a type meta-variable but got something else"
     end

  | Rule.TypeConstructor _, TT.TypeMeta _ -> failwith "rule wants a constructor but got a meta"

and check_term (metas : TT.argument list) (schema : Rule.term) (argument : TT.term) =
  match schema, argument with

  | Rule.TermBound k, TT.TermBound n ->
     if not (TT.equal_bound k n) then
       failwith "mismatch"

  | Rule.TermConstructor (c, args_schema), TT.TermConstructor (c', args) ->
     if Name.eq_ident c c' then
       check_args metas args_schema args
     else
       failwith "mismatch"

  | Rule.TermMeta (k, es_schema), e ->
     begin
       (* XXX TODO List.nth could fail miserably here *)
       match List.nth metas k with

       | TT.ArgIsTerm abstr ->
          let es = meta_instantiate_terms metas es_schema in
          let e' = fully_instantiate_abstraction (TT.fully_instantiate_term ?lvl:None) abstr es in
          if not (TT.alpha_equal_term e e') then
            failwith "term mismatch"

       | TT.ArgIsType _ | TT.ArgEqType _ | TT.ArgEqTerm _ ->
          failwith "expected a term meta-variable but got something else"
     end

  | _, _ -> failwith "other cases are errors"


and check_args metas args_schema args =
  match args_schema, args with

  | [], [] -> ()

  | arg_schema :: args_schema, arg :: args ->
     check_arg metas arg_schema arg ;
     check_args metas args_schema args

  | [], _::_ | _::_, [] -> failwith "too many or too few arguments"

and check_arg metas arg_schema arg =
  match arg_schema, arg with
  | Rule.ArgIsType t_schema, TT.ArgIsType t -> check_abstraction check_type metas t_schema t
  | Rule.ArgIsTerm e_schema, TT.ArgIsTerm e -> check_abstraction check_term metas e_schema e
  | Rule.ArgEqType _, TT.ArgEqType _ -> ()
  | Rule.ArgEqTerm _, TT.ArgEqTerm _ -> ()
  | _, _ -> failwith "check_arg failed"

and check_abstraction
    : 'a 'b . (TT.argument list -> 'a -> 'b -> unit) ->
      TT.argument list ->
      'a Rule.abstraction -> 'b TT.abstraction -> unit
  =  fun check_u metas s_abstr p_abstr ->
  match s_abstr, p_abstr with

  | Rule.NotAbstract u_schema, TT.NotAbstract u ->
     check_u metas u_schema u

  | Rule.Abstract (_, t_schema, s_abstr), TT.Abstract (_, t, p_abstr) ->
     check_type metas t_schema t ;
     check_abstraction check_u metas s_abstr p_abstr

  | _, _ -> failwith "TODO please reasonable error in Jdg.check_abstraction"


let atom_name {TT.atom_name=n;_} = n

(** [type_of_term sgn e] gives a type judgment [t], where [t] is the type of [e].
      Note that [t] itself gives no evidence that [e] actually has type [t].
      However, the assumptions of [e] are sufficient to show that [e] has
      type [t].  *)
let type_of_term sgn = function
  | TT.TermAtom {TT.atom_type=t; _} -> t

  | TT.TermBound k ->
     (* We should never get here. If ever we need to compute the type of a
        term with bound variables, then we should have unabstracted the term
        beforehand, and asked about the type of the unabstracted version. *)
     assert false

  | TT.TermConstructor (c, args) ->
     let (_premises, t_schema) = Signature.lookup_rule_is_term c sgn in
     (* we need not re-check that the premises match the arguments because
        we are computing the type of a term that was previously determined
        to be valid. *)
     meta_instantiate_is_type ~lvl:0 args t_schema

  | TT.TermMeta ({TT.meta_type;_}, args) ->
     fully_instantiate_abstraction (TT.fully_instantiate_type ?lvl:None) meta_type args

  | TT.TermConvert (e, _, t) -> t


let rec type_of_term_abstraction sgn = function
  | TT.NotAbstract e ->
     let t = type_of_term sgn e in
     TT.mk_not_abstract t

  | TT.Abstract (x, t, abstr) ->
     let a, abstr = TT.unabstract_abstraction TT.instantiate_term x t abstr in
     let t_abstr = type_of_term_abstraction sgn abstr in
     let t_abstr = TT.abstract_abstraction TT.abstract_type a.TT.atom_name t_abstr in
     TT.mk_abstract x t t_abstr

(** [natural_type sgn e] gives the judgment that the natural type [t] of [e] is derivable.
    We maintain the invariant that no further assumptions are needed (apart from those
    already present in [e]) to derive that [e] actually has type [t]. *)
let natural_type sgn = function
  | (TT.TermAtom _ | TT.TermBound _ | TT.TermConstructor _ | TT.TermMeta _) as e ->
     type_of_term sgn e

  | TT.TermConvert (e, _, _) -> type_of_term sgn e

let natural_type_eq sgn e =
  let natural = natural_type sgn e
  and given = type_of_term sgn e in
  TT.mk_eq_type Assumption.empty natural given

let check_argument sgn metas s p =
  match s, p with

  | Rule.PremiseIsType s_abstr, ArgumentIsType p_abstr ->
     check_abstraction
       (fun _ _ _ -> ())
       metas s_abstr p_abstr

  | Rule.PremiseIsTerm s_abstr, ArgumentIsTerm p_abstr ->
     check_abstraction
       (fun metas t_schema e -> check_type metas t_schema (type_of_term sgn e))
       metas s_abstr p_abstr

  | Rule.PremiseEqType s_abstr, ArgumentEqType p_abstr ->
     check_abstraction
       (fun metas (t1_schema, t2_schema) (TT.EqType (_asmp, t1, t2)) ->
         check_type metas t1_schema t1 ;
         check_type metas t2_schema t2)
       metas s_abstr p_abstr

  | Rule.PremiseEqTerm s_abstr, ArgumentEqTerm p_abstr ->
     check_abstraction
       (fun metas (e1_schema, e2_schema, t_schema) (TT.EqTerm (_asmp, e1, e2, t)) ->
         check_term metas e1_schema e1 ;
         check_term metas e2_schema e2 ;
         check_type metas t_schema t)
       metas
       s_abstr p_abstr

  | _, _ -> failwith "TODO better error in check_argument"

let arg_of_argument = function
  | ArgumentIsType t -> TT.mk_arg_is_type t
  | ArgumentIsTerm e -> TT.mk_arg_is_term e
  | ArgumentEqType eq -> TT.mk_arg_eq_type eq
  | ArgumentEqTerm eq-> TT.mk_arg_eq_term eq

let match_argument sgn metas (s : Rule.premise) (p : argument) : TT.argument =
  check_argument sgn metas s p ;
  arg_of_argument p

let match_arguments sgn (premises : Rule.premise list) (arguments : argument list) =
  let rec fold args_out = function
    | [], [] -> List.rev args_out
    | [], _::_ -> failwith "too many arguments"
    | _::_, [] -> failwith "too few arguments"
    | premise :: premises, argument :: arguments ->
       let metas = args_out in (* args also serves as the list of collected metas *)
       let argument = match_argument sgn metas premise argument in
       fold (argument :: args_out) (premises, arguments)
  in
  fold [] (premises, arguments)

(** Judgement formation *)

(** Lookup the de Bruijn level of a meta-variable.

    There is a certain trickiness to this function:

    * the list of metavariables [mvs] is given in the reverse order, i.e.,
      de Bruijn level 0 is the last element of the list.

    * we want de Bruijn levels rather than indices because when a rule is
      applied we get the arguments in the order of premises
    NB: for meta-variables we use de Bruijn levels rather than indices becuase
    the arguments of a rule instance are given as a list, so it is easier to
    use indices.
 *)
let lookup_meta_index mv mvs =
  let rec search k = function
    | [] -> assert false
    | mv' :: mvs ->
       if Name.eq_meta mv mv' then
         k
       else
         search (k+1) mvs
  in
  List.length mvs - 1 - search 0 mvs

(** The [mk_rule_XYZ] functions are auxiliary functions that should not be
   exposed. The external interface exopses the [form_rule_XYZ] functions defined
   below. *)

let rec mk_rule_is_type metas = function
  | TT.TypeConstructor (c, args) ->
     let args = mk_rule_args metas args in
     Rule.TypeConstructor (c, args)

  | TT.TypeMeta (mv, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     let k = lookup_meta_index mv.TT.meta_name metas in
     Rule.TypeMeta (k, args)

and mk_rule_is_term metas = function
  | TT.TermAtom _ ->
     (* this will be gone when we eliminate atoms *)
     failwith "an free atom cannot appear in a rule"

  | TT.TermMeta (mv, args) ->
     let args = List.map (mk_rule_is_term metas) args in
     let k = lookup_meta_index mv.TT.meta_name metas in
     Rule.TermMeta (k, args)

  | TT.TermConstructor (c, args) ->
     let args = mk_rule_args metas args in
     Rule.TermConstructor (c, args)

  | TT.TermBound k ->
     Rule.TermBound k

  | TT.TermConvert (e, asmp, t) ->
     (* XXX TODO do something about the assumption set. I think it needs to be a subset of metas. *)
     Print.error "should do someting about assumptions sets, hello?@." ;
     mk_rule_is_term metas e

and mk_rule_eq_type metas (TT.EqType (asmp, t1, t2)) =
    let asmp = mk_rule_assumptions metas asmp
    and t1 = mk_rule_is_type metas t1
    and t2 = mk_rule_is_type metas t2 in
    Rule.EqType (asmp, t1, t2)

and mk_rule_eq_term metas (TT.EqTerm (asmp, e1, e2, t)) =
    let asmp = mk_rule_assumptions metas asmp
    and e1 = mk_rule_is_term metas e1
    and e2 = mk_rule_is_term metas e2
    and t = mk_rule_is_type metas t in
    Rule.EqTerm (asmp, e1, e2, t)

and mk_rule_assumptions metas asmp =
  failwith "should check that asmp is a subset of metas or some such"

and mk_rule_arg metas = function

  | TT.ArgIsType abstr ->
     let abstr = mk_rule_abstraction mk_rule_is_type metas abstr in
     Rule.ArgIsType abstr

  | TT.ArgIsTerm abstr ->
     let abstr = mk_rule_abstraction mk_rule_is_term metas abstr in
     Rule.ArgIsTerm abstr

  | TT.ArgEqType abstr ->
     let abstr = mk_rule_abstraction mk_rule_eq_type metas abstr in
     Rule.ArgEqType abstr

  | TT.ArgEqTerm abstr ->
     let abstr = mk_rule_abstraction mk_rule_eq_term metas abstr in
     Rule.ArgEqTerm abstr

and mk_rule_args metas args =
  List.map (mk_rule_arg metas) args

and mk_rule_abstraction
 : 'a 'b . (Name.meta list -> 'a -> 'b) -> Name.meta list -> 'a TT.abstraction -> 'b Rule.abstraction
 = fun form_u metas -> function

  | TT.NotAbstract u ->
     let u = form_u metas u in
     Rule.NotAbstract u

  | TT.Abstract (x, t, abstr) ->
     let t = mk_rule_is_type metas t in
     let abstr = mk_rule_abstraction form_u metas abstr in
     Rule.Abstract (x, t, abstr)

let mk_rule_premise metas = function

  | BoundaryType abstr ->
     let abstr = mk_rule_abstraction (fun _ () -> ()) metas abstr in
     Rule.PremiseIsType abstr

  | BoundaryTerm abstr ->
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
           (t1, t2))
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
           (e1, e2, t))
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
  let arguments = match_arguments sgn prems arguments in
  TT.mk_type_constructor c arguments

let form_is_term sgn c arguments =
  let (premises, _boundary) = Signature.lookup_rule_is_term c sgn in
  let arguments = match_arguments sgn premises arguments in
  TT.mk_term_constructor c arguments

let form_eq_type sgn c arguments =
  let (premises, (lhs_schema, rhs_schema)) =
    Signature.lookup_rule_eq_type c sgn in
  let arguments = match_arguments sgn premises arguments in
  let asmp = TT.assumptions_arguments arguments
  and lhs = meta_instantiate_is_type ~lvl:0 arguments lhs_schema
  and rhs = meta_instantiate_is_type ~lvl:0 arguments rhs_schema
  in TT.mk_eq_type asmp lhs rhs

let form_eq_term sgn c arguments =
  let (premises, (e1_schema, e2_schema, t_schema)) =
    Signature.lookup_rule_eq_term c sgn in
  let args = match_arguments sgn premises arguments in
  let asmp = TT.assumptions_arguments args
  and e1 = meta_instantiate_is_term ~lvl:0 args e1_schema
  and e2 = meta_instantiate_is_term ~lvl:0 args e2_schema
  and t = meta_instantiate_is_type ~lvl:0 args t_schema
  in TT.mk_eq_term asmp e1 e2 t

let type_of_atom {TT.atom_type=t;_} = t

(** Construct judgements *)

let form_is_term_atom = TT.mk_atom

let fresh_atom = TT.fresh_atom

let fresh_is_type_meta = TT.fresh_type_meta
let fresh_is_term_meta = TT.fresh_term_meta
let fresh_eq_type_meta = TT.fresh_eq_type_meta
let fresh_eq_term_meta = TT.fresh_eq_term_meta

let rec check_term_arguments sgn abstr args = match (abstr, args) with
  | TT.NotAbstract u, [] -> ()
  | TT.Abstract _, [] -> assert false (* not enough arguments *)
  | TT.NotAbstract _, _::_ -> assert false (* too many arguments *)
  | TT.Abstract (x, t, abstr), arg :: args ->
     if TT.alpha_equal_type t (type_of_term sgn arg)
     then check_term_arguments sgn abstr args
     else failwith "invalid application"

let form_is_term_convert sgn e (TT.EqType (asmp, t1, t2)) =
  match e with
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
       error (InvalidConvert (t0, t1))

  | (TT.TermAtom _ | TT.TermBound _ | TT.TermConstructor _ | TT.TermMeta _) as e ->
     let t0 = natural_type sgn e in
     if TT.alpha_equal_type t0 t1 then
       (* We need not include assumptions of [t1] because [t0] is alpha-equal
            to [t1] so we can use [t0] in place of [t1] if so desired. *)
       (* [e] is not a [TermConvert] by the above pattern-check *)
       TT.mk_term_convert e asmp t2
     else
       error (InvalidConvert (t0, t1))

let abstract_not_abstract u = TT.mk_not_abstract u

let abstract_is_type {TT.atom_name=x; atom_type=t} abstr =
  (* XXX occurs check?! *)
  let abstr = TT.abstract_abstraction TT.abstract_type x abstr in
  TT.mk_abstract (Name.ident_of_atom x) t abstr

let abstract_is_term {TT.atom_name=x; atom_type=t} abstr =
  let abstr = TT.abstract_abstraction TT.abstract_term x abstr in
  TT.mk_abstract (Name.ident_of_atom x) t abstr

let abstract_eq_type {TT.atom_name=x; atom_type=t} abstr =
  let abstr = TT.abstract_abstraction TT.abstract_eq_type x abstr in
  TT.mk_abstract (Name.ident_of_atom x) t abstr

let abstract_eq_term {TT.atom_name=x; atom_type=t} abstr =
  let abstr = TT.abstract_abstraction TT.abstract_eq_term x abstr in
  TT.mk_abstract (Name.ident_of_atom x) t abstr

let abstract_boundary_is_type {TT.atom_name=x; atom_type=t} abstr =
  let abstr = TT.abstract_abstraction (fun _a ?lvl t -> ()) x abstr in
  TT.mk_abstract (Name.ident_of_atom x) t abstr

let abstract_boundary_is_term {TT.atom_name=x; atom_type=t} abstr =
  let abstr = TT.abstract_abstraction TT.abstract_type x abstr in
  TT.mk_abstract (Name.ident_of_atom x) t abstr

let abstract_boundary_eq_type {TT.atom_name=x; atom_type=t} abstr =
  let abstr = TT.abstract_abstraction
      (fun a ?lvl (lhs, rhs) ->
         let lhs = TT.abstract_type ?lvl a lhs
         and rhs = TT.abstract_type ?lvl a rhs in
      (lhs, rhs))
      x abstr in
  TT.mk_abstract (Name.ident_of_atom x) t abstr

let abstract_boundary_eq_term {TT.atom_name=x; atom_type=t} abstr =
  let abstr = TT.abstract_abstraction
      (fun a ?lvl (lhs, rhs, t) ->
         let lhs = TT.abstract_term ?lvl a lhs
         and rhs = TT.abstract_term ?lvl a rhs
         and t = TT.abstract_type ?lvl a t in
      (lhs, rhs, t))
      x abstr in
  TT.mk_abstract (Name.ident_of_atom x) t abstr


(** Destructors *)

let invert_arg = function
  | TT.ArgIsTerm abstr -> ArgumentIsTerm abstr
  | TT.ArgIsType abstr -> ArgumentIsType abstr
  | TT.ArgEqType abstr -> ArgumentEqType abstr
  | TT.ArgEqTerm abstr -> ArgumentEqTerm abstr

let invert_args args = List.map invert_arg args

let invert_is_term sgn = function

  | TT.TermAtom a -> TermAtom a

  | TT.TermBound _ -> assert false

  | TT.TermConstructor (c, args) ->
     let arguments = invert_args args in
     TermConstructor (c, arguments)

  | TT.TermMeta (mv, args) ->
     TermMeta (mv, args)

  | TT.TermConvert (e, asmp, t) ->
     let t' = natural_type sgn e in
     let eq = TT.mk_eq_type asmp t' t in
     TermConvert (e, eq)

let invert_is_type = function
  | TT.TypeConstructor (c, args) ->
     let arguments = invert_args args in
     TypeConstructor (c, arguments)
  | TT.TypeMeta (mv, args) -> TypeMeta (mv, args)

let invert_eq_type (TT.EqType (asmp, t1, t2)) = EqType (asmp, t1, t2)

let invert_eq_term (TT.EqTerm (asmp, e1, e2, t)) = EqTerm (asmp, e1, e2, t)

let invert_abstraction ?atom_name inst_v = function
  | TT.Abstract (x, t, abstr) ->
     let x = (match atom_name with None -> x | Some y -> y) in
     let a = TT.fresh_atom x t in
     let abstr = TT.instantiate_abstraction inst_v (TT.mk_atom a) abstr in
     Abstract (a, abstr)
  | TT.NotAbstract v -> NotAbstract v

let invert_is_type_abstraction ?atom_name t =
  invert_abstraction ?atom_name TT.instantiate_type t

let invert_is_term_abstraction ?atom_name e =
  invert_abstraction ?atom_name TT.instantiate_term e

let invert_eq_type_abstraction ?atom_name eq =
  invert_abstraction ?atom_name TT.instantiate_eq_type eq

let invert_eq_term_abstraction ?atom_name eq =
  invert_abstraction ?atom_name TT.instantiate_eq_term eq

let context_is_type_abstraction = TT.context_abstraction TT.assumptions_type
let context_is_term_abstraction = TT.context_abstraction TT.assumptions_term
let context_eq_type_abstraction = TT.context_abstraction TT.assumptions_eq_type
let context_eq_term_abstraction = TT.context_abstraction TT.assumptions_eq_term

let occurs_abstraction assumptions_u a abstr =
  let asmp = TT.(assumptions_abstraction assumptions_u abstr) in
  Assumption.mem_atom a.TT.atom_name asmp

let occurs_is_type_abstraction = occurs_abstraction TT.assumptions_type
let occurs_is_term_abstraction = occurs_abstraction TT.assumptions_term
let occurs_eq_type_abstraction = occurs_abstraction TT.assumptions_eq_type
let occurs_eq_term_abstraction = occurs_abstraction TT.assumptions_eq_term


let apply_abstraction inst_u sgn abstr e0 =
  match abstr with
  | TT.NotAbstract _ -> failwith "foo"
  | TT.Abstract (x, t, abstr) ->
     begin match TT.alpha_equal_type t (type_of_term sgn e0) with
     | false -> failwith "bar"
     | true ->  TT.instantiate_abstraction inst_u e0 abstr
     end

let apply_is_type_abstraction sgn abstr e0 =
  apply_abstraction TT.instantiate_type sgn abstr e0

let apply_is_term_abstraction sgn abstr e0 =
  apply_abstraction TT.instantiate_term sgn abstr e0

let apply_eq_type_abstraction sgn abstr e0 =
  apply_abstraction TT.instantiate_eq_type sgn abstr e0

let apply_eq_term_abstraction sgn abstr e0 =
  apply_abstraction TT.instantiate_eq_term sgn abstr e0

let rec fully_apply_abstraction inst_u sgn abstr = function
  | [] ->
     begin match abstr with
     | TT.NotAbstract eq -> eq
     | TT.Abstract _ -> failwith "not enough arguments"
     end
  | arg :: args ->
     let abstr = apply_abstraction inst_u sgn abstr arg in
     fully_apply_abstraction inst_u sgn abstr args

(** Conversion *)

let convert_eq_term (TT.EqTerm (asmp1, e1, e2, t0)) (TT.EqType (asmp2, t1, t2)) =
  if TT.alpha_equal_type t0 t1 then
    (* We could have used the assumptions of [t0] instead of [t1], see comments in [form_is_term]
       about possible optimizations. *)
    let asmp = Assumption.union asmp1 (Assumption.union asmp2 (TT.assumptions_type t1)) in
    TT.mk_eq_term asmp e1 e2 t2
  else
    error (InvalidConvert (t0, t1))

(** Meta-variables *)

let form_is_type_meta sgn m args =
  check_term_arguments sgn m.TT.meta_type args ;
  TT.mk_type_meta m args

let form_is_term_meta sgn m args =
  check_term_arguments sgn m.TT.meta_type args ;
  TT.mk_term_meta m args

let form_eq_type_meta sgn TT.{meta_name ; meta_type} args =
  let asmp = Assumption.singleton_meta meta_name (TT.BoundaryEqType meta_type) in
  let (lhs, rhs) =
    let inst_eq_type_boundary e0 ?lvl (lhs, rhs) =
      let lhs = TT.instantiate_type e0 ?lvl lhs
      and rhs = TT.instantiate_type e0 ?lvl rhs
      in (lhs, rhs)
    in
    fully_apply_abstraction inst_eq_type_boundary sgn meta_type args
  in
  TT.mk_eq_type asmp lhs rhs

let form_eq_term_meta sgn TT.{meta_name ; meta_type} args =
  let asmp = Assumption.singleton_meta meta_name (TT.BoundaryEqTerm meta_type) in
  let (lhs, rhs, t) =
    let inst_eq_term_boundary e0 ?lvl (lhs, rhs, t) =
      let lhs = TT.instantiate_term e0 ?lvl lhs
      and rhs = TT.instantiate_term e0 ?lvl rhs
      and t = TT.instantiate_type e0 ?lvl t
      in (lhs, rhs, t)
    in
    fully_apply_abstraction inst_eq_term_boundary sgn meta_type args
  in
  TT.mk_eq_term asmp lhs rhs t

let meta_eta_expanded instantiate_meta form_meta abstract_meta sgn mv =
  let rec fold args = function
  | TT.NotAbstract u -> TT.mk_not_abstract (form_meta sgn mv (List.rev args))
  | TT.Abstract (x, ty, abstr) ->
     let a, abstr =
       TT.unabstract_abstraction instantiate_meta x ty abstr in
     let abstr = fold ((form_is_term_atom a) :: args) abstr in
     TT.abstract_abstraction abstract_meta a.TT.atom_name abstr
  in fold [] mv.TT.meta_type

let is_type_meta_eta_expanded =
  meta_eta_expanded
    (fun _e0 ?lvl () -> ())
    form_is_type_meta
    TT.abstract_type

let is_term_meta_eta_expanded =
  meta_eta_expanded
    TT.instantiate_type
    form_is_term_meta
    TT.abstract_term

let eq_type_meta_eta_expanded =
  meta_eta_expanded
    (fun e0 ?lvl (lhs, rhs) ->
       TT.instantiate_type e0 ?lvl lhs,
       TT.instantiate_type e0 ?lvl rhs)
    form_eq_type_meta
    TT.abstract_eq_type

let eq_term_meta_eta_expanded =
  meta_eta_expanded
    (fun e0 ?lvl (lhs, rhs, t) ->
       TT.instantiate_term e0 ?lvl lhs,
       TT.instantiate_term e0 ?lvl rhs,
       TT.instantiate_type e0 ?lvl t)
    form_eq_term_meta
    TT.abstract_eq_term


(** Constructors *)

let reflexivity_term sgn e =
  let t = type_of_term sgn e in
  TT.mk_eq_term Assumption.empty e e t

let reflexivity_type t =
  TT.mk_eq_type Assumption.empty t t

let alpha_equal_term = TT.alpha_equal_term

let alpha_equal_type = TT.alpha_equal_type

let alpha_equal_abstraction = TT.alpha_equal_abstraction

let mk_alpha_equal_type t1 t2 =
  match TT.alpha_equal_type t1 t2 with
  | false -> None
  | true -> Some (TT.mk_eq_type Assumption.empty t1 t2)

(** Compare two terms for alpha equality. *)
let mk_alpha_equal_term sgn e1 e2 =
  let t1 = type_of_term sgn e1
  and t2 = type_of_term sgn e2
  in
  (* XXX if e1 and e2 are α-equal, we may apply uniqueness of typing to
     conclude that their types are equal, so we don't have to compute t1, t2,
     and t1 =α= t2. *)
  match TT.alpha_equal_type t1 t2 with
  | false -> error (AlphaEqualTypeMismatch (t1, t2))
  | true ->
     begin match TT.alpha_equal_term e1 e2 with
     | false -> None
     | true ->
        (* We may keep the assumptions empty here. One might worry
           that the assumptions needed for [e2 : t2] have to be included,
           but this does not seem to be the case: we have [e2 : t2] and
           [t1 == t2] (without assumptions as they are alpha-equal!),
           hence by conversion [e2 : t1], and whatever assumptions are
           required for [e2 : t2], they're already present in [e2]. *)
        Some (TT.mk_eq_term Assumption.empty e1 e2 t1)
     end

let rec mk_alpha_equal_abstraction equal_u abstr1 abstr2 =
  match abstr1, abstr2 with
  | TT.NotAbstract u1, TT.NotAbstract u2 ->
     begin match equal_u u1 u2 with
     | None -> None
     | Some eq -> Some (TT.mk_not_abstract eq)
     end
  | TT.Abstract (x1, t1, abstr1), TT.Abstract (_x2, t2, abstr2) ->
     begin match alpha_equal_type t1 t2 with
     | false -> None
     | true ->
        begin match mk_alpha_equal_abstraction equal_u abstr1 abstr2 with
        | None -> None
        | Some eq -> Some (TT.mk_abstract x1 t1 eq)
        end
     end
  | (TT.NotAbstract _, TT.Abstract _)
  | (TT.Abstract _, TT.NotAbstract _) -> None

let symmetry_term (TT.EqTerm (asmp, e1, e2, t)) = TT.mk_eq_term asmp e2 e1 t

let symmetry_type (TT.EqType (asmp, t1, t2)) = TT.mk_eq_type asmp t2 t1

let transitivity_term (TT.EqTerm (asmp, e1, e2, t)) (TT.EqTerm (asmp', e1', e2', t')) =
  match TT.alpha_equal_type t t' with
  | false -> error (AlphaEqualTypeMismatch (t, t'))
  | true ->
     begin match TT.alpha_equal_term e2 e1' with
     | false -> error (AlphaEqualTermMismatch (e2, e1'))
     | true ->
        (* XXX could use assumptions of [e1'] instead, or whichever is better. *)
        let asmp = Assumption.union asmp (Assumption.union asmp' (TT.assumptions_term e2))
        in TT.mk_eq_term asmp e1 e2' t
     end

let transitivity_type (TT.EqType (asmp1, t1, t2)) (TT.EqType (asmp2, u1, u2)) =
  begin match TT.alpha_equal_type t2 u1 with
  | false -> error (AlphaEqualTypeMismatch (t2, u1))
  | true ->
     (* XXX could use assumptions of [u1] instead, or whichever is better. *)
     let asmp = Assumption.union asmp1 (Assumption.union asmp2 (TT.assumptions_type t2))
     in TT.mk_eq_type asmp t1 u2
  end

(** Congruence rules *)

let process_congruence_args args =

  let rec check_endpoints check t1 t2 eq =
    match t1, t2, eq with
    | TT.NotAbstract t1, TT.NotAbstract t2, TT.NotAbstract eq ->
       if not (check t1 t2 eq) then failwith "some error"
    | TT.Abstract (_x1, u1, t1), TT.Abstract (_x2, u2, t2), TT.Abstract (_x', u', eq) ->
       if TT.alpha_equal_type u1 u' || TT.alpha_equal_type u2 u' then
         check_endpoints check t1 t2 eq
       else
         failwith "mismatch"
    | _, _, _ -> failwith "wrong lengths"

  in
  let rec fold asmp_out lhs rhs = function

    | [] -> (asmp_out, List.rev lhs, List.rev rhs)

    | CongrIsType (t1, t2, eq) :: eqs ->
       check_endpoints
         (fun t1 t2 (TT.EqType (_, t1', t2')) ->
           TT.alpha_equal_type t1 t1' && TT.alpha_equal_type t2 t2')
         t1 t2 eq ;
       let asmp_out = Assumption.union asmp_out (TT.assumptions_abstraction TT.assumptions_eq_type eq)
       in fold asmp_out (ArgumentIsType t1 :: lhs) (ArgumentIsType t2 :: rhs) eqs

    | CongrIsTerm (e1, e2, eq) :: eqs ->
       check_endpoints
         (fun e1 e2 (TT.EqTerm (_, e1', e2', _)) ->
           TT.alpha_equal_term e1 e1' && TT.alpha_equal_term e2 e2')
         e1 e2 eq ;
       let asmp_out = Assumption.union asmp_out (TT.assumptions_abstraction TT.assumptions_eq_term eq)
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
  in TT.mk_eq_type asmp t1 t2

let congruence_term_constructor sgn c eqs =
  let (asmp, lhs, rhs) = process_congruence_args eqs in
  let e1 = form_is_term sgn c lhs
  and e2 = form_is_term sgn c rhs in
  let t = type_of_term sgn e1
  in TT.mk_eq_term asmp e1 e2 t

(** Printing functions *)

let print_is_term ?max_level ~penv e ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>@[<hov>%t@]@;<1 -2>@]"
              (Print.char_vdash ())
              (TT.print_term ~max_level:Level.highest ~penv e)
              (* XXX print the type of the term also *)

let print_is_type ?max_level ~penv t ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>@[<hov>%t@]@;<1 -2> type@]"
              (Print.char_vdash ())
              (TT.print_type ~max_level:Level.highest ~penv t)

let print_eq_type ?max_level ~penv (TT.EqType (_asmp, t1, t2)) ppf =
  (* TODO: print _asmp? *)
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>@[<hov>%t@]@ %s@ @[<hov>%t@]@]"
              (Print.char_vdash ())
              (TT.print_type ~penv t1)
              (Print.char_equal ())
              (TT.print_type ~penv t2)

let print_eq_term ?max_level ~penv (TT.EqTerm (_asmp, e1, e2, t)) ppf =
  (* TODO: print _asmp? *)
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%s @[<hv>@[<hov>%t@]@ %s@ @[<hov>%t@]@ :@ @[<hov>%t@]@]"
              (Print.char_vdash ())
              (TT.print_term ~penv e1)
              (Print.char_equal ())
              (TT.print_term ~penv e2)
              (TT.print_type ~penv t)


let print_is_term_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  TT.print_abstraction TT.occurs_term print_is_term ?max_level ~penv abstr ppf

let print_is_type_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  TT.print_abstraction TT.occurs_type print_is_type ?max_level ~penv abstr ppf

let print_eq_type_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  TT.print_abstraction TT.occurs_eq_type print_eq_type ?max_level ~penv abstr ppf

let print_eq_term_abstraction ?max_level ~penv abstr ppf =
  (* TODO: print invisible assumptions, or maybe the entire context *)
  TT.print_abstraction TT.occurs_eq_term print_eq_term ?max_level ~penv abstr ppf

let print_error ~penv err ppf =
  match err with

  | InvalidConvert (t1, t2) ->
     Format.fprintf ppf "Trying to convert something at@ %t@ using an equality on@ %t@."
                    (TT.print_type ~penv t1) (TT.print_type ~penv t2)

  | AlphaEqualTypeMismatch (t1, t2) ->
     Format.fprintf ppf "The types@ %t@ and@ %t@ should be alpha equal."
                    (TT.print_type ~penv t1) (TT.print_type ~penv t2)

  | AlphaEqualTermMismatch (e1, e2) ->
     Format.fprintf ppf "The terms@ %t@ and@ %t@ should be alpha equal."
                    (TT.print_term ~penv e1) (TT.print_term ~penv e2)

module Json =
  struct

    let rec abstraction json_u = function
      | TT.NotAbstract u -> Json.tag "NotAbstract" [json_u u]
      | TT.Abstract (x, t, abstr) ->
         Json.tag "Abstract" [Name.Json.ident x; TT.Json.ty t; abstraction json_u abstr]

    let is_term e = Json.tag "IsTerm" [TT.Json.term e]

    let is_type t = Json.tag "IsType" [TT.Json.ty t]

    let eq_term (TT.EqTerm (asmp, e1, e2, t)) =
      Json.tag "EqTerm" [Assumption.Json.assumptions asmp; TT.Json.term e1; TT.Json.term e2; TT.Json.ty t]

    let eq_type (TT.EqType (asmp, t1, t2)) =
      Json.tag "EqType" [Assumption.Json.assumptions asmp; TT.Json.ty t1; TT.Json.ty t2]

  end
