(* ***** Predefined operations and conversion from AML to OCaml ***** *)

(** Conversions between OCaml list and ML list *)

let tag_nil, _, _ = Typecheck.Builtin.nil
let tag_cons, _, _ = Typecheck.Builtin.cons

let tag_none, _, _ = Typecheck.Builtin.none
let tag_some, _, _ = Typecheck.Builtin.some

(* let tag_notcoercible, _, _ = Typecheck.Builtin.notcoercible
 * let tag_convertible, _, _ = Typecheck.Builtin.convertible
 * let tag_coercible_constructor, _, _ = Typecheck.Builtin.coercible_constructor *)

let tag_mlless, _, _ = Typecheck.Builtin.mlless
let tag_mlequal, _, _ = Typecheck.Builtin.mlequal
let tag_mlgreater, _, _ = Typecheck.Builtin.mlgreater

let equal_term, _ = Typecheck.Builtin.equal_term
let equal_type, _ = Typecheck.Builtin.equal_type
let coerce, _ = Typecheck.Builtin.coerce

let list_nil = Runtime.mk_tag tag_nil []

let list_cons v lst = Runtime.mk_tag tag_cons [v; lst]

let rec mk_list = function
  | []      -> list_nil
  | x :: xs -> list_cons x (mk_list xs)

(* let as_list ~at v = *)
(*   match Runtime.as_list_opt v with *)
(*   | Some lst -> lst *)
(*   | None -> Runtime.(error ~at (ListExpected v)) *)

(** Conversion between Ocaml option and ML option *)

let mk_option = function
  | Some v -> Runtime.mk_tag tag_some [v]
  | None -> Runtime.mk_tag tag_none []

let as_option ~at = function
  | Runtime.Tag (t, []) when (Runtime.equal_tag t tag_none)  -> None
  | Runtime.Tag (t, [x]) when (Runtime.equal_tag t tag_some) -> Some x
  | Runtime.(Judgement _ | Boundary _ | Closure _ | Handler _ |
             Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
     Runtime.(error ~at (OptionExpected v))

let as_judgement_option ~at v =
  match as_option ~at v with
  | None -> None
  | Some (Runtime.Judgement jdg) -> Some jdg
  | Some (Runtime.(Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v) ->
     Runtime.(error ~at (JudgementExpected v))

(** Conversion between OCaml coercible and ML coercible *)

(* let as_coercible ~at = function
 *
 *   | Runtime.Tag (t, []) when Runtime.equal_tag t tag_notcoercible ->
 *     Runtime.NotCoercible
 *
 *   | Runtime.Tag (t, [v]) when Runtime.equal_tag t tag_convertible ->
 *     let eq = Runtime.as_eq_type_abstraction ~at v in
 *     Runtime.Convertible eq
 *
 *   | Runtime.Tag (t, [v]) when Runtime.equal_tag t tag_coercible_constructor ->
 *     let e = Runtime.as_is_term_abstraction ~at v in
 *     Runtime.Coercible e
 *
 *   | Runtime.(Judgement _ | Boundary _  | Closure _ | Handler _ | Tag _ | Tuple _ |
 *              Ref _ | Dyn _ | String _) as v ->
 *      Runtime.(error ~at (CoercibleExpected v)) *)

(** Conversion from OCaml [Runtime.order] to  [ML.order]. *)
let mlless = Runtime.mk_tag tag_mlless []
let mlequal = Runtime.mk_tag tag_mlequal []
let mlgreater = Runtime.mk_tag tag_mlgreater []

(** Computations that invoke operations *)

(* Map ML-value-to-(term)-judgment across an option. Fail if given Some value
   that is not a judgment. *)

let as_eq_term_option ~at v =
  match as_option ~at v with
    | Some v -> Some (Runtime.as_eq_term ~at v)
    | None -> None

let as_eq_type_option ~at v =
  match as_option ~at v with
    | Some v -> Some (Runtime.as_eq_type ~at v)
    | None -> None

let (>>=) = Runtime.bind
let return = Runtime.return

let operation_equal_term ~at e1 e2 =
  let v1 = Runtime.mk_judgement (Nucleus.(abstract_not_abstract (JudgementIsTerm e1)))
  and v2 = Runtime.mk_judgement (Nucleus.(abstract_not_abstract (JudgementIsTerm e2))) in
  Runtime.operation equal_term [v1;v2] >>= fun v ->
  return (as_eq_term_option ~at v)

let operation_equal_type ~at t1 t2 =
  let v1 = Runtime.mk_judgement (Nucleus.(abstract_not_abstract (JudgementIsType t1)))
  and v2 = Runtime.mk_judgement (Nucleus.(abstract_not_abstract (JudgementIsType t2))) in
  Runtime.operation equal_type [v1;v2] >>= fun v ->
  return (as_eq_type_option ~at v)

let operation_coerce ~at jdg bdry =
  let v1 = Runtime.Judgement jdg
  and v2 = Runtime.Boundary bdry in
  Runtime.operation coerce [v1;v2] >>= fun v ->
  return (as_judgement_option ~at v)

let add_abstracting e m =
  (* The given variable as an ML value *)
  let v = Runtime.mk_judgement (Nucleus.(abstract_not_abstract (JudgementIsTerm e))) in
  (* Get the ML list of [hypotheses] *)
  Runtime.hypotheses >>= fun hyps_dyn ->
  Runtime.lookup_dyn hyps_dyn >>= fun hyps ->
  (* Add v to the front of that ML list *)
  let hyps = list_cons v hyps in
  (* Run computation m in this dynamic scope *)
  Runtime.now hyps_dyn hyps m
