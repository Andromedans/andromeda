(************************)
(* Built-in Definitions *)
(************************)

let name_alpha = Name.mk_name (Name.greek 0)

(* If you change the order of constructors you have to fix them lower down as well. *)
let predefined_ml_types =
  let unloc x = Location.locate x Location.unknown in
  let ty_alpha = unloc (Input.ML_TyApply (Name.path_direct name_alpha, [])) in
  let un_ml_is_term = unloc (Input.ML_Judgement (Input.ML_NotAbstract Input.ML_IsTerm)) in
  let un_ml_eq_type = unloc (Input.ML_Judgement (Input.ML_NotAbstract Input.ML_EqType)) in
  let decl_bool = Input.DefMLType [Name.Predefined.bool, ([],
    Input.ML_Sum [
    (Name.Predefined.mlfalse, []);
    (Name.Predefined.mltrue, [])
    ])] in
  let decl_option = Input.DefMLType [Name.Predefined.option, ([Some name_alpha],
    Input.ML_Sum [
    (Name.Predefined.none, []);
    (Name.Predefined.some, [ty_alpha])
    ])]

  and decl_list = Input.DefMLTypeRec [Name.Predefined.list, ([Some name_alpha],
    Input.ML_Sum [
    (Name.Predefined.nil, []);
    (Name.Predefined.cons, [ty_alpha; unloc (Input.ML_TyApply (Name.path_direct Name.Predefined.list, [ty_alpha]))])
    ])]

  and decl_coercible = Input.DefMLType [Name.Predefined.coercible_ty, ([],
    Input.ML_Sum [
    (Name.Predefined.notcoercible, []) ;
    (Name.Predefined.convertible, [un_ml_eq_type]);
    (Name.Predefined.coercible_constructor, [un_ml_is_term])
    ])]

  and decl_order = Input.DefMLType [Name.Predefined.mlorder, ([],
    Input.ML_Sum [
      (Name.Predefined.mlless, []) ;
      (Name.Predefined.mlequal, []) ;
      (Name.Predefined.mlgreater, [])
      ])]
  in

  [unloc decl_bool; unloc decl_option; unloc decl_list; unloc decl_coercible; unloc decl_order]

let predefined_ops =
  let unloc x = Location.locate x Location.unknown in
  let un_ml_is_type = unloc (Input.ML_Judgement (Input.ML_NotAbstract Input.ML_IsType)) in
  let un_ml_is_term = unloc (Input.ML_Judgement (Input.ML_NotAbstract Input.ML_IsTerm)) in
  let un_ml_eq_type = unloc (Input.ML_Judgement (Input.ML_NotAbstract Input.ML_EqType)) in
  let un_ml_eq_term = unloc (Input.ML_Judgement (Input.ML_NotAbstract Input.ML_EqTerm)) in
  let decl_equal_term =
    Input.DeclOperation
      (Name.Predefined.equal_term,
       ([un_ml_is_term; un_ml_is_term],
        unloc (Input.ML_TyApply (Name.path_direct Name.Predefined.option, [un_ml_eq_term]))))
  and decl_equal_type =
    Input.DeclOperation
      (Name.Predefined.equal_type,
       ([un_ml_is_type; un_ml_is_type],
        unloc (Input.ML_TyApply (Name.path_direct Name.Predefined.option, [un_ml_eq_type]))))
  and decl_coerce =
    Input.DeclOperation
      (Name.Predefined.coerce,
       ([un_ml_is_term; un_ml_is_type],
        unloc (Input.ML_TyApply (Name.path_direct Name.Predefined.coercible_ty, []))))
  in
  [unloc decl_equal_term;
   unloc decl_equal_type;
   unloc decl_coerce]

let predefined_bound =
  let unloc x = Location.locate x Location.unknown in
  let un_ml_is_term = unloc (Input.ML_Judgement (Input.ML_NotAbstract Input.ML_IsTerm)) in
  let hyps_annot = unloc (Input.ML_TyApply (Name.path_direct Name.Predefined.list, [un_ml_is_term])) in
  let decl_hyps = Input.TopDynamic
                    (Name.Predefined.hypotheses, Input.Arg_annot_ty hyps_annot, unloc (Input.List [])) in
  [unloc decl_hyps]

let initial = List.concat [predefined_ml_types; predefined_ops; predefined_bound]
