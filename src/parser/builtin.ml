(* All built-in definitions are placed in a module called [ML].
   Below is the content of that module. *)

let name_alpha = Name.mk_name (Name.greek 0)

let unloc x = Location.locate x Location.unknown

let builtin_ml_types =
  let ty_alpha = unloc (Input.ML_TyApply (Name.PName name_alpha, [])) in
  let decl_bool = Input.DefMLType [Name.Builtin.bool_name, ([],
    Input.ML_Sum [
    (Name.Builtin.mlfalse_name, []);
    (Name.Builtin.mltrue_name, [])
    ])] in
  let decl_option = Input.DefMLType [Name.Builtin.option_name, ([Some name_alpha],
    Input.ML_Sum [
    (Name.Builtin.none_name, []);
    (Name.Builtin.some_name, [ty_alpha])
    ])]

  and decl_order = Input.DefMLType [Name.Builtin.mlorder_name, ([],
    Input.ML_Sum [
      (Name.Builtin.mlless_name, []) ;
      (Name.Builtin.mlequal_name, []) ;
      (Name.Builtin.mlgreater_name, [])
      ])]
  in
  [unloc decl_bool; unloc decl_option; unloc decl_order]

let builtin_ops =
  let un_ml_judgement = unloc (Input.ML_Judgement) in
  let un_ml_boundary = unloc (Input.ML_Boundary) in
  let decl_equal_term =
    Input.DeclOperation
      (Name.Builtin.equal_term_name,
       ([un_ml_judgement; un_ml_judgement],
        unloc (Input.ML_TyApply (Name.PName Name.Builtin.option_name, [un_ml_judgement]))))
  and decl_equal_type =
    Input.DeclOperation
      (Name.Builtin.equal_type_name,
       ([un_ml_judgement; un_ml_judgement],
        unloc (Input.ML_TyApply (Name.PName Name.Builtin.option_name, [un_ml_judgement]))))
  and decl_coerce =
    Input.DeclOperation
      (Name.Builtin.coerce_name,
       ([un_ml_judgement; un_ml_boundary],
        unloc (Input.ML_TyApply (Name.PName Name.Builtin.option_name, [un_ml_judgement]))))
  in
  [unloc decl_equal_term;
   unloc decl_equal_type;
   unloc decl_coerce]

let builtin_ml_values =
  let un_ml_judgement = unloc (Input.ML_Judgement) in
  let hyps_annot = unloc (Input.ML_TyApply (Name.PName Name.Builtin.list_name, [un_ml_judgement])) in
  let empty_list = unloc (Input.Spine (unloc (Input.Name (Name.PName Name.Builtin.nil_name)), [])) in
  let decl_hyps = Input.TopDynamic
                    (Name.Builtin.hypotheses_name, Input.Arg_annot_ty hyps_annot, empty_list) in
  [unloc decl_hyps]

let initial =
  let ty_alpha = unloc (Input.ML_TyApply (Name.PName name_alpha, [])) in
  let decl_list = Input.DefMLTypeRec [Name.Builtin.list_name, ([Some name_alpha],
    Input.ML_Sum [
    (Name.Builtin.nil_name, []);
    (Name.Builtin.cons_name, [ty_alpha; unloc (Input.ML_TyApply (Name.PName Name.Builtin.list_name, [ty_alpha]))])
    ])]
  in
  [ unloc decl_list ;
    unloc (Input.TopModule
      (Name.Builtin.ml_name,
       List.concat [builtin_ml_types; builtin_ops; builtin_ml_values]))
  ]
