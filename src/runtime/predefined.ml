type coercible =
  | NotCoercible
  | Convertible of Nucleus.eq_type_abstraction
  | Coercible of Nucleus.is_term_abstraction

(************************)
(* Built-in Definitions *)
(************************)

let name_alpha = Name.mk_ident (Name.greek 0)

let predefined_aml_types =
  let unloc x = Location.locate x Location.unknown in
  let ty_alpha = unloc (Input.ML_TyApply (name_alpha, [])) in
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
    (Name.Predefined.cons, [ty_alpha; unloc (Input.ML_TyApply (Name.Predefined.list, [ty_alpha]))])
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
        unloc (Input.ML_TyApply (Name.Predefined.option, [un_ml_eq_term]))))
  and decl_equal_type =
    Input.DeclOperation
      (Name.Predefined.equal_type,
       ([un_ml_is_type; un_ml_is_type],
        unloc (Input.ML_TyApply (Name.Predefined.option, [un_ml_eq_type]))))
  and decl_coerce =
    Input.DeclOperation
      (Name.Predefined.coerce,
       ([un_ml_is_term; un_ml_is_type],
        unloc (Input.ML_TyApply (Name.Predefined.coercible_ty, []))))
  in
  [unloc decl_equal_term;
   unloc decl_equal_type;
   unloc decl_coerce]

let predefined_bound =
  let unloc x = Location.locate x Location.unknown in
  let un_ml_is_term = unloc (Input.ML_Judgement (Input.ML_NotAbstract Input.ML_IsTerm)) in
  let hyps_annot = unloc (Input.ML_TyApply (Name.Predefined.list, [un_ml_is_term])) in
  let decl_hyps = Input.TopDynamic
                    (Name.Predefined.hypotheses, Input.Arg_annot_ty hyps_annot, unloc (Input.List [])) in
  [unloc decl_hyps]

let predefined_bound_names =
  [Name.Predefined.hypotheses]

let definitions = List.concat [predefined_aml_types; predefined_ops; predefined_bound]

(************************)
(* AML list <-> ML list *)
(************************)

let list_nil        = Runtime.mk_tag Name.Predefined.nil []
let list_cons v lst = Runtime.mk_tag Name.Predefined.cons [v; lst]

let rec mk_list = function
  | []      -> list_nil
  | x :: xs -> list_cons x (mk_list xs)

let as_list ~loc v =
  match Runtime.as_list_opt v with
  | Some lst -> lst
  | None -> Runtime.(error ~loc (ListExpected v))


(****************************)
(* AML option <-> ML option *)
(****************************)

let from_option = function
  | Some v -> Runtime.mk_tag Name.Predefined.some [v]
  | None -> Runtime.mk_tag Name.Predefined.none []

let as_option ~loc = function
  | Runtime.Tag (t,[]) when (Name.eq_ident t Name.Predefined.none)  -> None
  | Runtime.Tag (t,[x]) when (Name.eq_ident t Name.Predefined.some) -> Some x
  | (Runtime.IsType _ | Runtime.IsTerm _ | Runtime.EqType _ | Runtime.EqTerm _ |
     Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _ | Runtime.Dyn _ | Runtime.String _) as v ->
     Runtime.(error ~loc (OptionExpected v))



(**********************************)
(* AML coercible <-> ML coercible *)
(**********************************)

let as_coercible ~loc = function
  | Runtime.Tag (t, []) when Name.eq_ident t Name.Predefined.notcoercible ->
    NotCoercible
  | Runtime.Tag (t, [v]) when Name.eq_ident t Name.Predefined.convertible ->
    let eq = Runtime.as_eq_type_abstraction ~loc v in
    Convertible eq
  | Runtime.Tag (t, [v]) when Name.eq_ident t Name.Predefined.coercible_constructor ->
    let e = Runtime.as_is_term_abstraction ~loc v in
    Coercible e
  | (Runtime.IsType _ | Runtime.IsTerm _ | Runtime.EqType _ | Runtime.EqTerm _ |
     Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _ | Runtime.Dyn _ | Runtime.String _) as v ->
     Runtime.(error ~loc (CoercibleExpected v))


(***************************************)
(* Computations that invoke operations *)
(***************************************)

(* Maps AML-value-to-(term)-judgment across an option.
   Fails if given Some value that is not a judgment.
 *)

let as_eq_term_option ~loc v =
  match as_option ~loc v with
    | Some v -> Some (Runtime.as_eq_term ~loc v)
    | None -> None

let as_eq_type_option ~loc v =
  match as_option ~loc v with
    | Some v -> Some (Runtime.as_eq_type ~loc v)
    | None -> None

let (>>=) = Runtime.bind

let operation_equal_term ~loc e1 e2 =
  let v1 = Runtime.mk_is_term (Nucleus.abstract_not_abstract e1)
  and v2 = Runtime.mk_is_term (Nucleus.abstract_not_abstract e2) in
  Runtime.operation Name.Predefined.equal_term [v1;v2] >>= fun v ->
  Runtime.return (as_eq_term_option ~loc v)

let operation_equal_type ~loc t1 t2 =
  let v1 = Runtime.mk_is_type (Nucleus.abstract_not_abstract t1)
  and v2 = Runtime.mk_is_type (Nucleus.abstract_not_abstract t2) in
  Runtime.operation Name.Predefined.equal_type [v1;v2] >>= fun v ->
  Runtime.return (as_eq_type_option ~loc v)

let operation_coerce ~loc e t =
  let v1 = Runtime.mk_is_term e
  and v2 = Runtime.mk_is_type t in
  Runtime.operation Name.Predefined.coerce [v1;v2] >>= fun v ->
  Runtime.return (as_coercible ~loc v)

(*********)
(* Other *)
(*********)

(* Possibly this should be in Runtime?
   It seems to be here only because predefined_bound_names
   isn't in the interface.
*)

let add_abstracting j m =
  let loc = Location.unknown in
  (* In practice k will be 0 because hypothesis is the first dynamic variable *)
  let k = match Name.level_of_ident Name.Predefined.hypotheses predefined_bound_names with
    | Some k -> k
    | None -> assert false
  in
  let v = Runtime.mk_is_term j in               (* The given variable as an AML value *)
  Runtime.index_of_level k >>= fun k ->         (* Switch k from counting from the
                                                   beginning to counting from the end *)
  Runtime.lookup_bound ~loc k >>= fun hypsx ->   (* Get the AML list of [hypotheses] *)
  let hypsx = Runtime.as_dyn ~loc hypsx in
  Runtime.lookup_dyn hypsx >>= fun hyps ->
  let hyps = list_cons v hyps in                (* Add v to the front of that AML list *)
  Runtime.now hypsx hyps m                     (* Run computation m in this dynamic scope *)
