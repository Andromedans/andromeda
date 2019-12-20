(* All built-in definitions are placed in a module called [ML].
   Below is the content of that module. *)

let name_alpha = Name.mk_name (Name.greek 0)

let unloc x = Location.mark ~at:Location.unknown x

let builtin_ml_types =
  let ty_alpha = unloc (Sugared.ML_TyApply (Name.PName name_alpha, [])) in
  let decl_bool = Sugared.DefMLType [Name.Builtin.bool_name, ([],
    Sugared.ML_Sum [
    (Name.Builtin.mlfalse_name, []);
    (Name.Builtin.mltrue_name, [])
    ])] in
  let decl_option = Sugared.DefMLType [Name.Builtin.option_name, ([Some name_alpha],
    Sugared.ML_Sum [
    (Name.Builtin.none_name, []);
    (Name.Builtin.some_name, [ty_alpha])
    ])]

  and decl_order = Sugared.DefMLType [Name.Builtin.mlorder_name, ([],
    Sugared.ML_Sum [
      (Name.Builtin.mlless_name, []) ;
      (Name.Builtin.mlequal_name, []) ;
      (Name.Builtin.mlgreater_name, [])
      ])]
  in
  [unloc decl_bool; unloc decl_option; unloc decl_order]

let builtin_ops =
  let un_ml_judgement = unloc (Sugared.ML_Judgement) in
  let un_ml_boundary = unloc (Sugared.ML_Boundary) in
  let decl_equal_term =
    Sugared.DeclOperation
      (Name.Builtin.equal_term_name,
       ([un_ml_judgement; un_ml_judgement],
        unloc (Sugared.ML_TyApply (Name.PName Name.Builtin.option_name, [un_ml_judgement]))))
  and decl_equal_type =
    Sugared.DeclOperation
      (Name.Builtin.equal_type_name,
       ([un_ml_judgement; un_ml_judgement],
        unloc (Sugared.ML_TyApply (Name.PName Name.Builtin.option_name, [un_ml_judgement]))))
  and decl_coerce =
    Sugared.DeclOperation
      (Name.Builtin.coerce_name,
       ([un_ml_judgement; un_ml_boundary],
        unloc (Sugared.ML_TyApply (Name.PName Name.Builtin.option_name, [un_ml_judgement]))))
  in
  [unloc decl_equal_term;
   unloc decl_equal_type;
   unloc decl_coerce]

let builtin_ml_values =
  []

let initial =
  let ty_alpha = unloc (Sugared.ML_TyApply (Name.PName name_alpha, [])) in
  let decl_list = Sugared.DefMLTypeRec [Name.Builtin.list_name, ([Some name_alpha],
    Sugared.ML_Sum [
    (Name.Builtin.nil_name, []);
    (Name.Builtin.cons_name, [ty_alpha; unloc (Sugared.ML_TyApply (Name.PName Name.Builtin.list_name, [ty_alpha]))])
    ])]
  in
  [ unloc decl_list ;
    unloc (Sugared.TopModule
      (Name.Builtin.ml_name,
       List.concat [builtin_ml_types; builtin_ops; builtin_ml_values]))
  ]
