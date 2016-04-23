
type coercible =
  | NotCoercible
  | Convertible of Jdg.eq_ty
  | Coercible of Jdg.term

let name_alpha = Name.make (Name.greek 0)

let predefined_aml_types = let open Input in
  let loc = Location.unknown in
  let ty_alpha = ML_TyApply (name_alpha, []), loc in
  let decl_option = DefMLType [Name.Predefined.option, ([name_alpha],
    ML_Sum [
    (Name.Predefined.none, []);
    (Name.Predefined.some, [ty_alpha])
    ])], loc
  and decl_list = DefMLTypeRec [Name.Predefined.list, ([name_alpha],
    ML_Sum [
    (Name.Predefined.nil, []);
    (Name.Predefined.cons, [ty_alpha; (ML_TyApply (Name.Predefined.list, [ty_alpha]), loc)])
    ])], loc
  and decl_coercible = DefMLType [Name.Predefined.coercible_ty, ([],
    ML_Sum [
    (Name.Predefined.notcoercible, []);
    (Name.Predefined.convertible, [ML_Judgment, loc]);
    (Name.Predefined.coercible_constructor, [ML_Judgment, loc])
    ])], loc
  in
  [decl_option; decl_list; decl_coercible]

let predefined_ops = let open Input in
  let loc = Location.unknown in
  let decl_equal = DeclOperation (Name.Predefined.equal, ([ML_Judgment, loc; ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  and decl_as_prod = DeclOperation (Name.Predefined.as_prod, ([ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  and decl_as_eq = DeclOperation (Name.Predefined.as_eq, ([ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  and decl_coerce = DeclOperation (Name.Predefined.coerce, ([ML_Judgment, loc; ML_Judgment, loc], (ML_TyApply (Name.Predefined.coercible_ty, []), loc))), loc
  and decl_coerce_fun = DeclOperation (Name.Predefined.coerce_fun, ([ML_Judgment, loc], (ML_TyApply (Name.Predefined.coercible_ty, []), loc))), loc
  in
  [decl_equal; decl_as_prod; decl_as_eq; decl_coerce; decl_coerce_fun]

let predefined_bound = let open Input in
  let loc = Location.unknown in
  let decl_hyps = TopDynamic (Name.Predefined.hypotheses, (List [], loc)), loc in
  let force_hyps_type = TopDo (Let ([Name.anonymous, [],
    Some (ML_Forall ([], (ML_TyApply (Name.Predefined.list, [ML_Judgment, loc]) , loc)), loc),
    (Var Name.Predefined.hypotheses, loc)], (Tuple [], loc)), loc), loc in
  [decl_hyps; force_hyps_type]

let predefined_bound_names =
  [Name.Predefined.hypotheses]

let definitions = List.concat [predefined_aml_types; predefined_ops; predefined_bound]


let list_nil = Runtime.mk_tag Name.Predefined.nil []

let list_cons v lst = Runtime.mk_tag Name.Predefined.cons [v; lst]

let rec mk_list = function
  | [] -> list_nil
  | x :: xs -> list_cons x (mk_list xs)

let as_list ~loc v =
  match Runtime.as_list_opt v with
  | Some lst -> lst
  | None -> Runtime.(error ~loc (ListExpected v))

let from_option = function
  | Some v -> Runtime.mk_tag Name.Predefined.some [v]
  | None -> Runtime.mk_tag Name.Predefined.none []

let as_option ~loc = function
  | Runtime.Tag (t,[]) when (Name.eq_ident t Name.Predefined.none)  -> None
  | Runtime.Tag (t,[x]) when (Name.eq_ident t Name.Predefined.some) -> Some x
  | (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _ | Runtime.String _) as v ->
     Runtime.(error ~loc (OptionExpected v))

let as_coercible ~loc = function
  | Runtime.Tag (t, []) when Name.eq_ident t Name.Predefined.notcoercible ->
    NotCoercible
  | Runtime.Tag (t, [v]) when Name.eq_ident t Name.Predefined.convertible ->
    let j = Runtime.as_term ~loc v in
    let jeq = Jdg.reflect_ty_eq ~loc j in
    Convertible jeq
  | Runtime.Tag (t, [v]) when Name.eq_ident t Name.Predefined.coercible_constructor ->
    let j = Runtime.as_term ~loc v in
    Coercible j
  | (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _ | Runtime.String _) as v ->
     Runtime.(error ~loc (CoercibleExpected v))

let (>>=) = Runtime.bind

let as_term_option ~loc v =
  match as_option ~loc v with
    | Some v -> Some (Runtime.as_term ~loc v)
    | None -> None

let operation_equal ~loc j1 j2 =
  let v1 = Runtime.mk_term j1
  and v2 = Runtime.mk_term j2 in
  Runtime.operation Name.Predefined.equal [v1;v2] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

let operation_coerce ~loc j1 j2 =
  let v1 = Runtime.mk_term j1
  and v2 = Runtime.mk_term (Jdg.term_of_ty j2) in
  Runtime.operation Name.Predefined.coerce [v1;v2] >>= fun v ->
  Runtime.return (as_coercible ~loc v)

let operation_coerce_fun ~loc j =
  let v = Runtime.mk_term j in
  Runtime.operation Name.Predefined.coerce_fun [v] >>= fun v ->
  Runtime.return (as_coercible ~loc v)

let operation_as_prod ~loc j =
  let v = Runtime.mk_term j in
  Runtime.operation Name.Predefined.as_prod [v] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

let operation_as_eq ~loc j =
  let v = Runtime.mk_term j in
  Runtime.operation Name.Predefined.as_eq [v] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

let add_abstracting j m =
  let loc = Location.unknown in
  let k = match Name.level_of_ident Name.Predefined.hypotheses predefined_bound_names with
    | Some k -> k
    | None -> assert false
  in
  let v = Runtime.mk_term j in
  Runtime.index_of_level k >>= fun k ->
  Runtime.lookup_bound ~loc k >>= fun hyps ->
  let hyps = list_cons v hyps in
  Runtime.now ~loc k hyps m

