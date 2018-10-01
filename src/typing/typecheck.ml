
let (>>=) = Tyenv.(>>=)
let return = Tyenv.return

let locate ~loc v = Location.locate v loc

let judgement_mismatch ~loc jdg_expected jdg_actual =
  let t1 = Mlty.Judgement (Mlty.NotAbstract jdg_expected)
  and t2 = Mlty.Judgement (Mlty.NotAbstract jdg_actual)
  in Mlty.error ~loc (Mlty.TypeMismatch (t1, t2))

(** Is a computation generalizable *)
type generalizable =
  | Generalizable
  | Ungeneralizable

let rec generalizable c =
  match c.Location.thing with
  (* yes *)
  | Rsyntax.Bound _ | Rsyntax.Function _ | Rsyntax.Handler _| Rsyntax.String _ ->
     Generalizable
  | Rsyntax.AML_Constructor (_, cs) | Rsyntax.Tuple cs ->
    if List.for_all (fun c -> generalizable c = Generalizable) cs
    then Generalizable
    else Ungeneralizable
  | Rsyntax.Let (_, c)
  | Rsyntax.LetRec (_, c)
  | Rsyntax.Sequence (_, c) -> generalizable c

  (* no *)
  | Rsyntax.Operation _
  | Rsyntax.With _
  | Rsyntax.Now _
  | Rsyntax.Current _
  | Rsyntax.Lookup _
  | Rsyntax.Update _
  | Rsyntax.Ref _
  | Rsyntax.Assume _
  | Rsyntax.Where _
  | Rsyntax.Match _
  | Rsyntax.Ascribe _
  | Rsyntax.TT_Constructor _
  | Rsyntax.Abstract _
  | Rsyntax.Yield _
  | Rsyntax.Apply _
  | Rsyntax.CongrAbstractTy _
  | Rsyntax.CongrAbstract _
  | Rsyntax.Reflexivity_term _
  | Rsyntax.Reflexivity_type _
  | Rsyntax.Symmetry_term _
  | Rsyntax.Symmetry_type _
  | Rsyntax.Transitivity_term _
  | Rsyntax.Transitivity_type _
  | Rsyntax.Occurs _
  | Rsyntax.Context _
  | Rsyntax.Natural _ -> Ungeneralizable

let rec tt_judgement = function
  | Dsyntax.ML_IsType -> Mlty.IsType
  | Dsyntax.ML_IsTerm -> Mlty.IsTerm
  | Dsyntax.ML_EqType -> Mlty.EqType
  | Dsyntax.ML_EqTerm -> Mlty.EqTerm

let rec tt_abstracted_judgement = function
  | Dsyntax.ML_NotAbstract frm ->
     let frm = tt_judgement frm
     in Mlty.NotAbstract frm
  | Dsyntax.ML_Abstract (frm, abstr) ->
     let frm = tt_judgement frm
     and abstr = tt_abstracted_judgement abstr
     in Mlty.Abstract (frm, abstr)

let rec ml_ty params {Location.thing=t; loc} =
  match t with

  | Dsyntax.ML_Arrow (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Mlty.Arrow (t1, t2)

  | Dsyntax.ML_Prod ts ->
    let ts = List.map (ml_ty params) ts in
    Mlty.Prod ts

  | Dsyntax.ML_TyApply (x, k, ts) ->
    let ts = List.map (ml_ty params) ts in
    Mlty.App (x, k, ts)

  | Dsyntax.ML_Handler (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Mlty.Handler (t1, t2)

  | Dsyntax.ML_Ref t ->
     let t = ml_ty params t in
     Mlty.Ref t

  | Dsyntax.ML_Dynamic t ->
     let t = ml_ty params t in
     Mlty.Dynamic t

  | Dsyntax.ML_Judgement abstr ->
     let abstr = tt_abstracted_judgement abstr
     in Mlty.Judgement abstr

  | Dsyntax.ML_String ->
     Mlty.String

  | Dsyntax.ML_Bound p ->
     Mlty.Param (List.nth params p)

  | Dsyntax.ML_Anonymous ->
     Mlty.fresh_type ()

let ml_schema {Location.thing=(Dsyntax.ML_Forall (params, t)); _} =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  let t = ml_ty params t in
  (params, t)

(** Type inference for TT patterns is a bit annoying because we cannot tell
    which judgement form a TT pattern might match (consider a pattern variable).
    Thus, we first attempt to discover which judgement form it must be,
    using the auxiliary function [tt_patter_infer_form] below. *)

(** Compute the judgement form from an AML type, if possible. *)
let tt_form_from_type = function
  | Mlty.Judgement abstr ->
     let rec form = function
       | Mlty.NotAbstract frm -> Some frm
       | Mlty.Abstract (_, abstr) -> form abstr
     in
     form abstr
  | Mlty.String
  | Mlty.Meta _
  | Mlty.Param _
  | Mlty.Prod _
  | Mlty.Arrow (_, _)
  | Mlty.Handler (_, _)
  | Mlty.App (_, _, _)
  | Mlty.Ref _
  | Mlty.Dynamic _ -> None

(** Infer the judgement form from a pattern. *)
let rec tt_infer_form {Location.thing=p';_} =
  match p' with
  | Dsyntax.Patt_TT_Anonymous
  | Dsyntax.Patt_TT_NewVar _
  | Dsyntax.Patt_TT_EquVar _ ->
     Tyenv.return None

  | Dsyntax.Patt_TT_Interpolate k ->
     Tyenv.lookup_var k >>= fun t ->
     Tyenv.return (tt_form_from_type t)

  | Dsyntax.Patt_TT_As (p1, p2) ->
     begin
       tt_infer_form p1 >>=
         function
         | Some _ as f -> Tyenv.return f
         | None ->
            begin tt_infer_form p2 >>=
              function
              | None -> Tyenv.return None
              | Some _ as f -> Tyenv.return f
            end
     end

  | Dsyntax.Patt_TT_Constructor (c, ps) ->
     Tyenv.lookup_tt_constructor c >>= fun (_, t) ->
     Tyenv.return (Some t)

  | Dsyntax.Patt_TT_GenAtom _ ->
     Tyenv.return (Some Mlty.IsTerm)

  | Dsyntax.Patt_TT_IsTerm _ ->
     Tyenv.return (Some Mlty.IsTerm)

  | Dsyntax.Patt_TT_EqType _ ->
     Tyenv.return (Some Mlty.EqType)

  | Dsyntax.Patt_TT_EqTerm _ ->
     Tyenv.return (Some Mlty.EqTerm)

  | Dsyntax.Patt_TT_Abstraction (_, _, _, abstr) ->
     tt_infer_form abstr

let rec is_type_pattern {Location.thing=p';loc} =
  match p' with

  | Dsyntax.Patt_TT_Anonymous ->
     Tyenv.return (locate ~loc Pattern.IsType_Anonymous)

  | Dsyntax.Patt_TT_NewVar (x, k) ->
     let t = Mlty.Judgement (Mlty.NotAbstract Mlty.IsType) in
     Tyenv.add_var x t (Tyenv.return (locate ~loc (Pattern.IsType_NewVar k)))

  | Dsyntax.Patt_TT_EquVar k ->
     check_var k (Mlty.NotAbstract Mlty.IsType) >>= fun () ->
     Tyenv.return (locate ~loc (Pattern.IsType_EquVar k))

  | Dsyntax.Patt_TT_Interpolate k ->
     check_var k (Mlty.NotAbstract Mlty.IsType) >>= fun () ->
     Tyenv.return (locate ~loc (Pattern.IsType_Interpolate k))

  | Dsyntax.Patt_TT_As (p1, p2) ->
     is_type_pattern p1 >>= fun p1 ->
     is_type_pattern p2 >>= fun p2 ->
     Tyenv.return (locate ~loc (Pattern.IsType_As (p1, p2)))

  | Dsyntax.Patt_TT_Constructor (c, ps) ->
     Tyenv.lookup_tt_constructor c >>=
       begin function
         |  (args, Mlty.IsType) ->
             check_tt_args args ps >>= fun ps ->
             Tyenv.return (locate ~loc (Pattern.IsType_Constructor (c, ps)))
         | (_, ((Mlty.IsTerm | Mlty.EqType | Mlty.EqTerm) as frm)) ->
            judgement_mismatch ~loc Mlty.IsType frm
       end

  | Dsyntax.Patt_TT_GenAtom _
  | Dsyntax.Patt_TT_IsTerm _ ->
     judgement_mismatch ~loc Mlty.IsType Mlty.IsTerm

  | Dsyntax.Patt_TT_EqType _ ->
     judgement_mismatch ~loc Mlty.IsType Mlty.EqType

  | Dsyntax.Patt_TT_EqTerm _ ->
     judgement_mismatch ~loc Mlty.IsType Mlty.EqTerm

  | Dsyntax.Patt_TT_Abstraction _ ->
     Mlty.error ~loc (Mlty.UnexpectedJudgementAbstraction Mlty.IsType)

(** Infer the type of a TT pattern. *)
let rec tt_pattern p =
  tt_infer_form p >>= function
  | None ->  Mlty.error ~loc:p.Location.loc Mlty.UnknownJudgementForm
  | Some (Mlty.IsType) -> tt_is_type_pattern p
  | Some (Mlty.IsTerm) -> tt_is_term_pattern p
  | Some (Mlty.EqType) -> tt_eq_type_pattern p
  | Some (Mlty.EqTerm) -> tt_eq_term_pattern p

(** Check the type of a pattern. *)
and check_tt_pattern {Location.thing=p';loc} t =
  match p' with
  | Dsyntax.Patt_TT_Anonymous
  | Dsyntax.Patt_TT_NewVar _
  | Dsyntax.Patt_TT_EquVar _
  | Dsyntax.Patt_TT_Interpolate _
  | Dsyntax.Patt_TT_As _
  | Dsyntax.TT_Constructor _
  | Dsyntax.Patt_TT_GenAtom _
  | Dsyntax.Patt_TT_IsTerm _
  | Dsyntax.Patt_TT_EqType _
  | Dsyntax.Patt_TT_EqTerm _
  | Dsyntax.Patt_TT_Abstraction _ ->
     failwith "not finished"

(** Infer the type of a pattern *)
let rec pattern {Location.thing=p;loc} =
  match p with
  | Dsyntax.Patt_Anonymous ->
     Tyenv.return (locate ~loc Pattern.Anonymous, Mlty.fresh_type ())

  | Dsyntax.Patt_NewVar (x, k) ->
     let t = Mlty.fresh_type () in
     Tyenv.add_var x t
     Tyenv.return (locate ~loc (Pattern.NewVar k), Mlty.fresh_type ())

  | Dsyntax.Patt_EquVar k ->
     Tyenv.return (locate ~loc (Pattern.EquVar k), Mlty.fresh_type ())

  | Dsyntax.Patt_Interpolate k ->
     Tyenv.lookup_var k >>= fun t ->
     Tyenv.return (locate ~loc (Pattern.Interpolate k), t)

  | Dsyntax.Patt_As (p1, p2) ->
     pattern p1 >>= fun (p1, t1) ->
     check_pattern p2 t1 >>= fun p2 ->
     Tyenv.return (locate ~loc (Pattern.As (p1, p2)), t1)

  | Dsyntax.Patt_Judgement p ->
     tt_pattern ~loc p

  | Dsyntax.Patt_Constr (c, ps) ->
    Tyenv.lookup_aml_constructor c >>= fun (ts, out) ->
    let rec fold qs ps ts =
      match ps, ts with
      | [], [] ->
         let qs = List.rev qs in
         Tyenv.return (locate ~loc (Pattern.Constructor (c, qs)), out)
      | p::ps, t::ts ->
        check_pattern p t >>= fun q ->
        fold (q::qs) ps ts
      | [], _::_ | _::_, [] ->
         assert false
    in
    fold [] ps ts

  | Dsyntax.Patt_Tuple ps ->
    let rec fold qs ts = function
      | [] ->
         let qs = List.rev qs
         and ts = List.rev ts in
         Tyenv.return (locate ~loc (Pattern.Tuple qs), Mlty.Prod ts)
      | p :: ps ->
         pattern p >>= fun (q, t) ->
         fold (q :: qs) (t :: ts) ps
    in
    fold [] [] ps

and check_pattern {Location.thing=p'; loc} t =
  match p' with
  | Dsyntax.Patt_Anonymous ->
     Tyenv.return (locate ~loc Pattern.Anonymous)

  | Dsyntax.Patt_NewVar k ->
     Tyenv.return (locate ~loc (Pattern.NewVar k))

  | Dsyntax.Patt_EquVar k ->
     Tyenv.return (locate ~loc (Pattern.EquVar k))

  | Dsyntax.Patt_Interpolate _
  | Dsyntax.Patt_Constr _
  | Dsyntax.Patt_Tuple _ ->
     pattern p >>= fun (p, t') ->
     Tyenv.add_equation ~loc:p.Location.loc t' t >>= fun () ->
     Tyenv.return p

  | Dsyntax.Patt_As (p1, p2) ->
     check_pattern p1 t >>= fun p1 ->
     check_pattern p2 t >>= fun p2 ->
     Tyenv.return (locate ~loc (Pattern.As (p1, p2)))

  | Dsyntax.Patt_Judgement _ ->
     check_tt_pattern ~loc p t

let match_case xs p t m =
  check_pattern p t >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | x :: xs ->
      let t = Mlty.fresh_type () in
      Tyenv.add_var x t (add_vars xts)
  in
  add_vars (List.rev xs)

let match_op_case xs ps popt argts m =
  let pts = List.combine ps argts in
  begin match popt with
    | Some p ->
       Tyenv.predefined_type Name.Predefined.option [Mlty.IsType] >>= fun t ->
       Tyenv.return ((p, t) :: pts)
    | None ->
       Tyenv.return pts
  end >>= fun pts ->
  let rec fold = function
    | [] -> Tyenv.return ()
    | (p, t) :: pts ->
      check_pattern p t >>= fun () ->
      fold pts
  in
  fold pts >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | x :: xs ->
       let t = Mlty.fresh_type () in
       Tyenv.add_var x t (add_vars xs)
  in
  add_vars (List.rev xs)

let rec comp ({Location.thing=c; loc} : Dsyntax.comp) : (Rsyntax.comp * Mlty.ty) Tyenv.tyenvM =
  match c with
  | Dsyntax.Bound k ->
    Tyenv.lookup_var k >>= fun t ->
    return (locate ~loc (Rsyntax.Bound k), t)

  | Dsyntax.Function (x, annot, c) ->
     let a =
       begin
         match annot with
         | Dsyntax.Arg_annot_none -> Mlty.fresh_type ()
         | Dsyntax.Arg_annot_ty t -> ml_ty [] t
       end
     in
     Tyenv.add_var x a (comp c) >>= fun (c, b) ->
     Tyenv.return (locate ~loc (Rsyntax.Function (x, c)), Mlty.Arrow (a, b))

  | Dsyntax.Handler h ->
     handler ~loc h >>= fun (h, t) ->
     return (locate ~loc (Rsyntax.Handler h), t)

  | Dsyntax.Constructor (c, cs) ->
    Tyenv.lookup_constructor c >>= fun (ts, out) ->
    let tcs = List.combine ts cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        Tyenv.return (locate ~loc (Rsyntax.Constructor (c, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Dsyntax.Tuple cs ->
    let rec fold annot ts = function
      | [] ->
        let ts = List.rev ts
        and cs = List.rev annot in
        Tyenv.return (locate ~loc (Rsyntax.Tuple cs), Mlty.Prod ts)
      | c :: cs ->
        comp c >>= fun (c, t) ->
        fold (c :: annot) (t :: ts) cs
    in
    fold [] [] cs

  | Dsyntax.Operation (op, cs) ->
    Tyenv.lookup_op op >>= fun (expected, out) ->
    let tcs = List.combine expected cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        Tyenv.return (locate ~loc (Rsyntax.Operation (op, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Dsyntax.With (h, c) ->
    comp h >>= fun (h, th) ->
    Tyenv.as_handler ~loc:h.Location.loc th >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    Tyenv.return (locate ~loc (Rsyntax.With (h, c)), b)

  | Dsyntax.Let (xcs, c) ->
    let_clauses xcs >>= fun clauses ->
    let rec fold = function
      | [] ->
        comp c >>= fun (c, t) ->
        return (locate ~loc (Rsyntax.Let (clauses, c)), t)
      | Rsyntax.Let_clause_ML (x, sch, _) :: rem ->
        Tyenv.add_let x sch (fold rem)
      | Rsyntax.Let_clause_patt (xts, _, _) :: rem ->
         let rec fold' = function
           | [] -> fold rem
           | (x, t) :: xts -> Tyenv.add_let x t (fold' xts)
         in
         fold' (List.rev xts)
    in
    fold clauses

  | Dsyntax.LetRec (xycs, c) ->
    let_rec_clauses xycs >>= fun clauses ->
    let rec fold = function
      | [] ->
        comp c >>= fun (c, t) ->
        return (locate ~loc (Rsyntax.LetRec (clauses, c)), t)
      | (x, _, s, _) :: rem ->
        Tyenv.add_let x s (fold rem)
    in
    fold clauses

  | Dsyntax.MLAscribe (c, sch) ->
      let sch = ml_schema sch in
      comp c >>= fun (c, t) ->
       begin
         match generalizable c with
         | Generalizable ->
            Tyenv.generalizes_to ~loc:c.Location.loc t sch
         | Ungeneralizable ->
            begin
              match sch with
              | ([], tsch) ->
                 Tyenv.add_equation ~loc:c.Location.loc t tsch
              | (_::_, _) ->
                 Mlty.error ~loc:c.Location.loc Mlty.ValueRestriction
            end
       end >>= fun () -> Tyenv.return (c, t)

  | Dsyntax.Now (x, c1, c2) ->
     comp x >>= fun (x, tx) ->
     Tyenv.as_dynamic ~loc:x.Location.loc tx >>= fun tx ->
     check_comp c1 tx >>= fun c1 ->
     comp c2 >>= fun (c2, t) ->
     return (locate ~loc (Rsyntax.Now (x, c1, c2)), t)

  | Dsyntax.Current c ->
     comp c >>= fun (c, t) ->
     Tyenv.as_dynamic ~loc:c.Location.loc t >>= fun t ->
     return (locate ~loc (Rsyntax.Current c), t)

  | Dsyntax.Lookup c ->
    comp c >>= fun (c, t) ->
    Tyenv.as_ref ~loc:c.Location.loc t >>= fun t ->
    return (locate ~loc (Rsyntax.Lookup c), t)

  | Dsyntax.Update (c1, c2) ->
    comp c1 >>= fun (c1, t1) ->
    Tyenv.as_ref ~loc:c1.Location.loc t1 >>= fun t ->
    check_comp c2 t >>= fun c2 ->
    Tyenv.return (locate ~loc (Rsyntax.Update (c1, c2)), Mlty.unit_ty)

  | Dsyntax.Ref c ->
    comp c >>= fun (c, t) ->
    Tyenv.return (locate ~loc (Rsyntax.Ref c), Mlty.Ref t)

  | Dsyntax.Sequence (c1, c2) ->
    comp c1 >>= fun (c1, _) ->
    (* TODO warn if not unit? *)
    comp c2 >>= fun (c2, t) ->
    return (locate ~loc (Rsyntax.Sequence (c1, c2)), t)

  | Dsyntax.Assume ((x, a), c) ->
    check_comp a Mlty.IsType >>= fun a ->
    Tyenv.add_var x Mlty.IsTerm (comp c) >>= fun (c, t) ->
    return (locate ~loc (Rsyntax.Assume ((x, a), c)), t)

  | Dsyntax.Where (c1, c2, c3) ->
    check_comp c1 Mlty.IsTerm >>= fun c1 ->
    check_comp c2 Mlty.IsTerm >>= fun c2 ->
    check_comp c3 Mlty.IsTerm >>= fun c3 ->
    Tyenv.return (locate ~loc (Rsyntax.Where (c1, c2, c3)), Mlty.IsTerm)

  | Dsyntax.Match (c, cases) ->
    comp c >>= fun (c, tc) ->
    match_cases ~loc tc cases >>= fun (cases, t) ->
    return (locate ~loc (Rsyntax.Match (c, cases)), t)

  | Dsyntax.Ascribe (c1, c2) ->
    check_comp c1 Mlty.IsTerm >>= fun c1 ->
    check_comp c2 Mlty.IsType >>= fun c2 ->
    Tyenv.return (locate ~loc (Rsyntax.Ascribe (c1, c2)), Mlty.IsTerm)

  | Dsyntax.Constant c -> Tyenv.return (locate ~loc (Rsyntax.Constant c), Mlty.IsTerm)

  | Dsyntax.Abstract (x, copt, c) ->
    begin match copt with
      | Some ct -> check_comp ct (Mlty.IsType Mlty.NotAbstract) >>= fun ct -> return (Some ct)
      | None -> Tyenv.return None
    end >>= fun copt ->
    Tyenv.add_var x (Mlty.IsTerm Mlty.NotAbstract) (comp c) >>= fun (c,t) ->
    let t =
      begin match t with
      | Mlty.IsType abstr -> Mlty.IsType (Mlty.Abstract abstr)
      | Mlty.IsTerm abstr -> Mlty.IsType (Mlty.Abstract abstr)
      | Mlty.EqType abstr -> Mlty.IsType (Mlty.Abstract abstr)
      | Mlty.EqTerm abstr -> Mlty.IsType (Mlty.Abstract abstr)
      | (String | Meta _ | Param _ | Prod _ | Arrow _ | Handler _ | App _ | Ref _|Dynamic _) as t ->
         Mlty.error ~loc (Mlty.JudgementExpected t)
      end
    in
    Tyenv.return (locate ~loc (Rsyntax.Abstract (x, copt, c)), t)

  | Dsyntax.Apply (c1, c2) ->
     comp c1 >>= fun (c1, t1) ->
     comp c2 >>= fun (c2, t2) ->
     let out = Mlty.fresh_type () in
     Tyenv.add_application ~loc t1 t2 out >>= fun () ->
     Tyenv.return (locate ~loc (Rsyntax.Apply (c1, c2)), out)

  | Dsyntax.Yield c ->
    Tyenv.lookup_continuation >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    Tyenv.return (locate ~loc (Rsyntax.Yield c), b)

  | Dsyntax.CongrAbstractTy (c1, c2, c3) ->
    check_comp c1 Mlty.IsTerm >>= fun c1 ->
    check_comp c2 Mlty.EqType >>= fun c2 ->
    check_comp c3 Mlty.EqType >>= fun c3 ->
    return (locate ~loc (Rsyntax.CongrAbstractTy (c1, c2, c3)), Mlty.EqType)

  | Dsyntax.CongrAbstract (c1, c2, c3, c4) ->
    check_comp c1 Mlty.IsTerm >>= fun c1 ->
    check_comp c2 Mlty.EqType >>= fun c2 ->
    check_comp c3 Mlty.EqType >>= fun c3 ->
    check_comp c4 Mlty.EqTerm >>= fun c4 ->
    return (locate ~loc (Rsyntax.CongrAbstract (c1, c2, c3, c4)), Mlty.EqTerm)

  | Dsyntax.Reflexivity_type c ->
     check_comp c Mlty.IsType >>= fun c ->
     return (locate ~loc (Rsyntax.Reflexivity_type c), Mlty.EqType)

  | Dsyntax.Symmetry_type c ->
     check_comp c Mlty.EqType >>= fun c ->
     return (locate ~loc (Rsyntax.Symmetry_type c), Mlty.EqType)

  | Dsyntax.Transitivity_type (c1, c2) ->
     check_comp c1 Mlty.EqType >>= fun c1 ->
     check_comp c2 Mlty.EqType >>= fun c2 ->
     return (locate ~loc (Rsyntax.Transitivity_type (c1, c2)), Mlty.EqType)

  | Dsyntax.Reflexivity_term c ->
     check_comp c Mlty.IsTerm >>= fun c ->
     return (locate ~loc (Rsyntax.Reflexivity_term c), Mlty.EqTerm)

  | Dsyntax.Symmetry_term c ->
     check_comp c Mlty.EqTerm >>= fun c ->
     return (locate ~loc (Rsyntax.Symmetry_term c), Mlty.EqTerm)

  | Dsyntax.Transitivity_term (c1, c2) ->
     check_comp c1 Mlty.EqTerm >>= fun c1 ->
     check_comp c2 Mlty.EqTerm >>= fun c2 ->
     return (locate ~loc (Rsyntax.Transitivity_term (c1, c2)), Mlty.EqTerm)

  | Dsyntax.String s -> Tyenv.return (locate ~loc (Rsyntax.String s), Mlty.String)

  | Dsyntax.Occurs (c1, c2) ->
    check_comp c1 Mlty.IsTerm >>= fun c1 ->
    check_comp c2 Mlty.IsTerm >>= fun c2 ->
    Tyenv.predefined_type Name.Predefined.option [Mlty.IsType] >>= fun t ->
    return (locate ~loc (Rsyntax.Occurs (c1, c2)), t)

  | Dsyntax.Context c ->
    check_comp c Mlty.IsTerm >>= fun c ->
    Tyenv.predefined_type Name.Predefined.list [Mlty.IsTerm] >>= fun t ->
    return (locate ~loc (Rsyntax.Context c), t)

  | Dsyntax.Natural c ->
    check_comp c Mlty.IsTerm >>= fun c ->
    return (locate ~loc (Rsyntax.Natural c), Mlty.EqType)

and check_comp c t =
  comp c >>= fun (c, t') ->
  Tyenv.add_equation ~loc:c.Location.loc t' t >>= fun () ->
  return c

and handler ~loc {Dsyntax.handler_val=handler_val;handler_ops;handler_finally} =
  let input = Mlty.fresh_type () in
  begin match handler_val with
    | [] -> Tyenv.return ([], input)
    | _ :: _ -> match_cases ~loc input handler_val
  end >>= fun (handler_val, output) ->
  begin match handler_finally with
    | [] -> Tyenv.return ([], output)
    | _ :: _ -> match_cases ~loc output handler_finally
  end >>= fun (handler_finally, final) ->
  let rec fold ops = function
    | [] ->
      return (List.fold_left (fun acc (x, v) -> Name.IdentMap.add x v acc) Name.IdentMap.empty ops)
    | (op, cases) :: rem ->
      match_op_cases op cases output >>= fun cases ->
      fold ((op, cases) :: ops) rem
  in
  fold [] (Name.IdentMap.bindings handler_ops) >>= fun handler_ops ->
  Tyenv.return ({Rsyntax.handler_val=handler_val;handler_ops;handler_finally}, Mlty.Handler (input, final))

and match_cases ~loc t cases =
  match cases with
    | [] ->
      Tyenv.return ([], Mlty.fresh_type ())
    | (xs, p, c) :: others ->
      match_case xs p t (comp c) >>= fun (c, out) ->
      let rec fold cases = function
        | [] ->
          let cases = List.rev cases in
          Tyenv.return (cases, out)
        | (xs, p, c) :: others ->
          match_case xs p t (check_comp c out) >>= fun c ->
          fold ((xs, p, c) :: cases) others
      in
      fold [xs, p, c] others

and match_op_cases op cases output =
  Tyenv.op_cases op ~output (fun argts ->
  let rec fold cases = function
    | [] -> Tyenv.return (List.rev cases)
    | (xs, ps, popt, c) :: rem ->
      match_op_case xs ps popt argts (check_comp c output) >>= fun c ->
      fold ((xs, ps, popt, c) :: cases) rem
  in
  fold [] cases)

and let_clauses (clauses_in : Dsyntax.let_clause list) : Rsyntax.let_clause list Tyenv.tyenvM =
  let rec fold clauses_out = function

    | [] -> Tyenv.return (List.rev clauses_out)

    | Dsyntax.Let_clause_ML (x, annot, c) :: clauses_in ->
      comp c >>= fun (c, t) ->
       begin
         match generalizable c with
         | Generalizable ->
            begin match annot with
            | Dsyntax.Let_annot_schema sch ->
               let sch = ml_schema sch in
               Tyenv.generalizes_to ~loc:c.Location.loc t sch >>= fun () ->
               return sch
            | Dsyntax.Let_annot_none ->
               Tyenv.generalize t
            end
         | Ungeneralizable ->
            begin match annot with
            | Dsyntax.Let_annot_schema sch ->
               let sch = ml_schema sch in
               begin match sch with
               | ([], tsch) ->
                  Tyenv.add_equation ~loc:c.Location.loc t tsch >>= fun () ->
                  return sch
               | (_::_, _) ->
                  Mlty.error ~loc:c.Location.loc Mlty.ValueRestriction
              end
            | Dsyntax.Let_annot_none ->
               Tyenv.ungeneralize t
            end
       end >>= fun sch ->
       fold (Rsyntax.Let_clause_ML (x, sch, c) :: clauses_out) clauses_in

  | Dsyntax.Let_clause_patt (xs, pt, annot, c) :: clauses_in ->
     comp c >>= fun (c, t) ->
     let xts = List.map (fun x -> x, Mlty.fresh_type ()) xs in
     check_pattern xts pt t >>= fun () ->
     begin match generalizable c with
     | Generalizable ->
        begin match annot with
        | Dsyntax.Let_annot_schema sch ->
           let sch = ml_schema sch in
           Tyenv.generalizes_to ~loc:c.Location.loc t sch
        | Dsyntax.Let_annot_none -> Tyenv.return ()
        end >>= fun () ->
        let rec fold' xss = function
          | [] -> fold (Rsyntax.Let_clause_patt (List.rev xss, pt, c) :: clauses_out) clauses_in
          | (x,t) :: xts -> Tyenv.generalize t >>= fun sch -> fold' ((x,sch) :: xss) xts
        in
        fold' [] xts
     | Ungeneralizable ->
        begin match annot with
        | Dsyntax.Let_annot_schema sch ->
           let sch = ml_schema sch in
           begin match sch with
           | ([], tsch) -> Tyenv.add_equation ~loc:c.Location.loc t tsch
           | (_::_, _) -> Mlty.error ~loc:c.Location.loc Mlty.ValueRestriction
           end
        | Dsyntax.Let_annot_none -> Tyenv.return ()
        end >>= fun () ->
        let rec fold' xss = function
          | [] -> fold (Rsyntax.Let_clause_patt (List.rev xss, pt, c) :: clauses_out) clauses_in
          | (x,t) :: xts -> Tyenv.ungeneralize t >>= fun sch -> fold' ((x,sch) :: xss) xts
        in
        fold' [] xts
     end
  in
  fold [] clauses_in

and let_rec_clauses (fycs : Dsyntax.letrec_clause list) : Rsyntax.letrec_clause list Tyenv.tyenvM =
  let rec bind_functions acc = function
    | (f, (y, a), annot, c) :: rem ->
       let a =
         begin
           match a with
           | Dsyntax.Arg_annot_none -> Mlty.fresh_type ()
           | Dsyntax.Arg_annot_ty t -> ml_ty [] t
         end
       and b = Mlty.fresh_type () in
       begin
         match annot with
         | Dsyntax.Let_annot_none ->
            Tyenv.ungeneralize (Mlty.Arrow (a, b)) >>= fun sch ->
            return (sch, None)
         | Dsyntax.Let_annot_schema sch ->
            let sch = ml_schema sch in
            return (sch, Some sch)
       end >>= fun (sch, schopt) ->
       Tyenv.add_let f sch (bind_functions ((f, schopt, y, a, c, b) :: acc) rem)

    | [] ->
       let rec check_bodies acc = function
         | [] -> Tyenv.return (List.rev acc)

         | (f, schopt, y, a, c, b) :: rem ->
            Tyenv.add_var y a (check_comp c b) >>= fun c ->
            check_bodies ((f, schopt, y, a, c, b) :: acc) rem
       in
       check_bodies [] (List.rev acc)
  in
  bind_functions [] fycs >>= fun lst ->
  let rec fold acc = function
    | [] -> Tyenv.return (List.rev acc)

    | (f, Some sch, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalizes_to ~loc:c.Location.loc t sch >>= fun () ->
       fold ((f, y, sch, c) :: acc) rem

    | (f, None, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalize t >>= fun sch ->
       fold ((f, y, sch, c) :: acc) rem
  in
  fold [] lst

let top_handler ~loc lst =
  let rec fold cases = function
    | [] -> Tyenv.return (List.rev cases)
    | (op, (xs, y, c)) :: lst ->
      Tyenv.lookup_op op >>= fun (argts, out) ->
      let xts = List.combine xs argts in
      let rec bind = function
        | [] ->
          let bindy m = match y with
            | Some y ->
               Tyenv.predefined_type Name.Predefined.option [Mlty.IsType] >>= fun jdg_opt ->
               Tyenv.add_var y jdg_opt m
            | None -> m
          in
          bindy (check_comp c out)
        | (x, t) :: xts ->
          Tyenv.add_var x t (bind xts)
      in
      bind xts >>= fun c ->
      fold ((op, (xs, y, c)) :: cases) lst
  in
  fold [] lst

let add_tydef env (t, (params, def)) =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  match def with

    | Dsyntax.ML_Alias t' ->
       let t' = ml_ty params t' in
       Tyenv.topadd_tydef t (Mlty.Alias (params, t')) env

    | Dsyntax.ML_Sum constructors ->
       let constructors = List.map (fun (c, ts) -> c, List.map (ml_ty params) ts) constructors in
       Tyenv.topadd_tydef t (Mlty.Sum (params, constructors)) env

let rec toplevel env ({Location.thing=c; loc} : Dsyntax.toplevel) =
  match c with
  (* Desugar is the only place where recursion/nonrecursion matters *)
  | Dsyntax.DefMLType tydefs ->
    let env = List.fold_left add_tydef env tydefs in
    env, locate ~loc (Rsyntax.DefMLType tydefs)

  | Dsyntax.DefMLTypeRec tydefs ->
    let env = List.fold_left add_tydef env tydefs in
    env, locate ~loc (Rsyntax.DefMLTypeRec tydefs)

  | Dsyntax.DeclOperation (op, (tys_in, ty_out)) ->
    let tys_in = List.map (ml_ty []) tys_in in
    let ty_out = ml_ty [] ty_out in
    let env = Tyenv.topadd_operation op (tys_in, ty_out) env in
    env, locate ~loc (Rsyntax.DeclOperation (op, (tys_in, ty_out)))

  | Dsyntax.DeclConstants (cs, t) ->
    let env, t = Tyenv.at_toplevel env (check_comp t Mlty.IsType) in
    env, locate ~loc (Rsyntax.DeclConstants (cs, t))

  | Dsyntax.DeclExternal (x, sch, s) ->
     let sch = ml_schema sch in
     let env = Tyenv.topadd_let x sch env in
     env, locate ~loc (Rsyntax.DeclExternal (x, sch, s))

  | Dsyntax.TopHandle lst ->
    let env, lst = Tyenv.at_toplevel env (top_handler ~loc lst) in
    env, locate ~loc (Rsyntax.TopHandle lst)

  | Dsyntax.TopLet clauses ->
     let rec fold env = function
       | [] -> env
       | Rsyntax.Let_clause_ML (x, sch, _) :: clauses ->
          let env = Tyenv.topadd_let x sch env in
          fold env clauses
       | Rsyntax.Let_clause_patt (xss, _, _) :: clauses ->
          let env =
            List.fold_right (fun (x, sch) env -> Tyenv.topadd_let x sch env) xss env
          in
          fold env clauses
     in
     let env, clauses = Tyenv.at_toplevel env (let_clauses clauses) in
     let env = fold env clauses in
     env, locate ~loc (Rsyntax.TopLet clauses)

  | Dsyntax.TopLetRec xycs ->
    let env, xycs = Tyenv.at_toplevel env (let_rec_clauses xycs) in
    let env = List.fold_left (fun env (x, _, s, _) -> Tyenv.topadd_let x s env) env xycs in
    env, locate ~loc (Rsyntax.TopLetRec xycs)

  | Dsyntax.TopDynamic (x, annot, c) ->
    let env, (c, sch) =
      Tyenv.at_toplevel env
        (comp c >>= fun (c, t) ->
         match annot with
         | Dsyntax.Arg_annot_none ->
            Tyenv.ungeneralize (Mlty.Dynamic t) >>= fun sch ->
            return (c, sch)
         | Dsyntax.Arg_annot_ty t' ->
            let t' = ml_ty [] t' in
            Tyenv.add_equation ~loc:c.Location.loc t t' >>= fun () ->
            Tyenv.ungeneralize (Mlty.Dynamic t') >>= fun sch ->
            return (c, sch)
        )
    in
    let env = Tyenv.topadd_let x sch env in
    env, locate ~loc (Rsyntax.TopDynamic (x, sch, c))

  | Dsyntax.TopNow (x, c) ->
     let env, (x, c) =
       Tyenv.at_toplevel env (comp x >>= fun (x, tx) ->
                              Tyenv.as_dynamic ~loc:x.Location.loc tx >>= fun tx ->
                              check_comp c tx >>= fun c ->
                              return (x,c))
     in
     env, locate ~loc (Rsyntax.TopNow (x, c))

  | Dsyntax.TopDo c ->
    let env, (c, _) = Tyenv.at_toplevel env (comp c) in
    env, locate ~loc (Rsyntax.TopDo c)

  | Dsyntax.TopFail c ->
    let env, (c, _) = Tyenv.at_toplevel env (comp c) in
    env, locate ~loc (Rsyntax.TopFail c)

  | Dsyntax.Verbosity v ->
    env, locate ~loc (Rsyntax.Verbosity v)

  | Dsyntax.Included fcs ->
    let rec fold_files env fcs = function
      | [] ->
        let fcs = List.rev fcs in
        env, fcs
      | (f, cs) :: rem ->
        let env, cs = List.fold_left (fun (env, cs) c ->
            let env, c = toplevel env c in
            (env, c :: cs))
          (env, []) cs
        in
        let cs = List.rev cs in
        fold_files env ((f, cs) :: fcs) rem
    in
    let env, fcs = fold_files env [] fcs in
    env, locate ~loc (Rsyntax.Included fcs)
