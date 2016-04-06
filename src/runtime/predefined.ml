let name_some          = Name.make "Some"
let name_none          = Name.make "None"
let name_cons          = Name.cons
let name_nil           = Name.nil

let name_option = Name.make "option"

let name_list = Name.make "list"

let name_alpha = Name.make (Name.greek 0)

let predefined_aml_types = let open Input in
  let loc = Location.unknown in
  let ty_alpha = ML_TyApply (name_alpha, []), loc in
  let decl_option = DefMLType [name_option, ([name_alpha],
    ML_Sum [
    (name_none, []);
    (name_some, [ty_alpha])
    ])], loc
  and decl_list = DefMLTypeRec [name_list, ([name_alpha],
    ML_Sum [
    (Name.nil, []);
    (Name.cons, [ty_alpha; (ML_TyApply (name_list, [ty_alpha]), loc)])
    ])], loc
  in
  [decl_option; decl_list]

let name_equal        = Name.make "equal"
let name_as_prod      = Name.make "as_prod"
let name_as_eq        = Name.make "as_eq"

let predefined_ops = let open Input in
  let loc = Location.unknown in
  let decl_equal = DeclOperation (name_equal, ([ML_Judgment, loc; ML_Judgment, loc], (ML_TyApply (name_option, [ML_Judgment, loc]), loc))), loc
  and decl_as_prod = DeclOperation (name_as_prod, ([ML_Judgment, loc], (ML_TyApply (name_option, [ML_Judgment, loc]), loc))), loc
  and decl_as_eq = DeclOperation (name_as_eq, ([ML_Judgment, loc], (ML_TyApply (name_option, [ML_Judgment, loc]), loc))), loc
  in
  [decl_equal; decl_as_prod; decl_as_eq]

let definitions = List.concat [predefined_aml_types; predefined_ops]

let rec mk_list = function
  | [] -> Runtime.mk_tag name_nil []
  | x :: xs -> Runtime.mk_tag name_cons [x; mk_list xs]

let rec as_list_opt = function
  | Runtime.Tag (t, []) when Name.eq_ident t name_nil -> Some []
  | Runtime.Tag (t, [x;xs]) when Name.eq_ident t name_cons ->
     begin
       match as_list_opt xs with
       | None -> None
       | Some xs -> Some (x :: xs)
     end
  | (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ | Runtime.Ref _ | Runtime.String _) ->
     None

let as_list ~loc v =
  match as_list_opt v with
  | Some lst -> lst
  | None -> Runtime.(error ~loc (ListExpected v))

let from_option = function
  | Some v -> Runtime.mk_tag name_some [v]
  | None -> Runtime.mk_tag name_none []

let as_option ~loc = function
  | Runtime.Tag (t,[]) when (Name.eq_ident t name_none)  -> None
  | Runtime.Tag (t,[x]) when (Name.eq_ident t name_some) -> Some x
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
  Runtime.operation name_equal [v1;v2] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

let operation_as_prod ~loc j =
  let v = Runtime.mk_term j in
  Runtime.operation name_as_prod [v] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

let operation_as_eq ~loc j =
  let v = Runtime.mk_term j in
  Runtime.operation name_as_eq [v] >>= fun v ->
  Runtime.return (as_term_option ~loc v)

