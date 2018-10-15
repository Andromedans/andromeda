type coercible =
  | NotCoercible
  | Convertible of Jdg.eq_type
  | Coercible of Jdg.is_term

(************************)
(* Built-in Definitions *)
(************************)

let name_alpha = Name.make (Name.greek 0)

let predefined_aml_types = let open Input in
  let unloc x = Location.locate x Location.unknown in
  let ty_alpha = unloc (ML_TyApply (name_alpha, [])) in
  let un_ml_is_term = unloc (ML_Judgement (ML_NotAbstract ML_IsTerm)) in
  let un_ml_eq_type = unloc (ML_Judgement (ML_NotAbstract ML_EqType)) in
  let decl_option = DefMLType [Name.Predefined.option, ([name_alpha],
    ML_Sum [
    (Name.Predefined.none, []);
    (Name.Predefined.some, [ty_alpha])
    ])]
  and decl_list = DefMLTypeRec [Name.Predefined.list, ([name_alpha],
    ML_Sum [
    (Name.Predefined.nil, []);
    (Name.Predefined.cons, [ty_alpha; unloc (ML_TyApply (Name.Predefined.list, [ty_alpha]))])
    ])]
  and decl_coercible = DefMLType [Name.Predefined.coercible_ty, ([],
    ML_Sum [
    (Name.Predefined.notcoercible, []);
    (Name.Predefined.convertible, [un_ml_eq_type]);
    (Name.Predefined.coercible_constructor, [un_ml_is_term])
    ])]
  in
  [unloc decl_option; unloc decl_list; unloc decl_coercible]

let predefined_ops = let open Input in
  let unloc x = Location.locate x Location.unknown in
  let un_ml_is_type = unloc (ML_Judgement (ML_NotAbstract ML_IsType)) in
  let un_ml_is_term = unloc (ML_Judgement (ML_NotAbstract ML_IsTerm)) in
  let un_ml_eq_type = unloc (ML_Judgement (ML_NotAbstract ML_EqType)) in
  let un_ml_eq_term = unloc (ML_Judgement (ML_NotAbstract ML_EqTerm)) in
  let decl_equal_term = DeclOperation (Name.Predefined.equal_term, ([un_ml_is_term; un_ml_is_term], unloc (ML_TyApply (Name.Predefined.option, [un_ml_eq_term]))))
  and decl_equal_type = DeclOperation (Name.Predefined.equal_type, ([un_ml_is_type; un_ml_is_type], unloc (ML_TyApply (Name.Predefined.option, [un_ml_eq_type]))))
  and decl_as_prod = DeclOperation (Name.Predefined.as_prod, ([un_ml_is_type], unloc (ML_TyApply (Name.Predefined.option, [un_ml_eq_type]))))
  and decl_coerce = DeclOperation (Name.Predefined.coerce, ([un_ml_is_term; un_ml_is_type], unloc (ML_TyApply (Name.Predefined.coercible_ty, []))))
  and decl_coerce_fun = DeclOperation (Name.Predefined.coerce_fun, ([un_ml_is_term], unloc (ML_TyApply (Name.Predefined.coercible_ty, []))))
  in
  [unloc decl_equal_term;
   unloc decl_equal_type;
   unloc decl_as_prod;
   unloc decl_coerce;
   unloc decl_coerce_fun]

let predefined_bound = let open Input in
  let unloc x = Location.locate x Location.unknown in
  let un_ml_is_term = unloc (ML_Judgement (ML_NotAbstract ML_IsTerm)) in
  let hyps_annot = unloc (ML_TyApply (Name.Predefined.list, [un_ml_is_term])) in
  let decl_hyps = TopDynamic
                    (Name.Predefined.hypotheses, Arg_annot_ty hyps_annot, unloc (List [])) in
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
    let eq = Runtime.as_eq_type ~loc v in
    Convertible eq
  | Runtime.Tag (t, [v]) when Name.eq_ident t Name.Predefined.coercible_constructor ->
    let e = Runtime.as_is_term ~loc v in
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
  let v1 = Runtime.mk_is_term (Jdg.form_not_abstract e1)
  and v2 = Runtime.mk_is_term (Jdg.form_not_abstract e2) in
  Runtime.operation Name.Predefined.equal_term [v1;v2] >>= fun v ->
  Runtime.return (as_eq_term_option ~loc v)

let operation_equal_type ~loc t1 t2 =
  let v1 = Runtime.mk_is_type (Jdg.form_not_abstract t1)
  and v2 = Runtime.mk_is_type (Jdg.form_not_abstract t2) in
  Runtime.operation Name.Predefined.equal_type [v1;v2] >>= fun v ->
  Runtime.return (as_eq_type_option ~loc v)

let operation_coerce ~loc e t =
  let v1 = Runtime.mk_is_term (Jdg.form_not_abstract e)
  and v2 = Runtime.mk_is_type (Jdg.form_not_abstract t) in
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
