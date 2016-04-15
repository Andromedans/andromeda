
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
  and decl_empty = DefMLType [Name.Predefined.empty, ([],
  ML_Sum [])], loc
  in
  [decl_option; decl_list; decl_empty]

let predefined_ops = let open Input in
  let loc = Location.unknown in
  let decl_equal = DeclOperation (Name.Predefined.equal, ([ML_Judgment, loc; ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  and decl_as_prod = DeclOperation (Name.Predefined.as_prod, ([ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  and decl_as_eq = DeclOperation (Name.Predefined.as_eq, ([ML_Judgment, loc], (ML_TyApply (Name.Predefined.option, [ML_Judgment, loc]), loc))), loc
  in
  [decl_equal; decl_as_prod; decl_as_eq]

let definitions = List.concat [predefined_aml_types; predefined_ops]

let rec mk_list = function
  | [] -> Runtime.mk_tag Name.Predefined.nil []
  | x :: xs -> Runtime.mk_tag Name.Predefined.cons [x; mk_list xs]

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

let operation_as_prod ~loc j =
  let v = Runtime.mk_term j in
  Runtime.operation Name.Predefined.as_prod [v] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

let operation_as_eq ~loc j =
  let v = Runtime.mk_term j in
  Runtime.operation Name.Predefined.as_eq [v] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

