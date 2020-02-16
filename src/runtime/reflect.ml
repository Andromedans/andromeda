(* ***** Predefined operations and conversion from AML to OCaml ***** *)

(** Conversions between OCaml list and ML list *)

let tag_nil, _, _ = Typecheck.Builtin.nil
let tag_cons, _, _ = Typecheck.Builtin.cons

let tag_none, _, _ = Typecheck.Builtin.none
let tag_some, _, _ = Typecheck.Builtin.some

let tag_mlless, _, _ = Typecheck.Builtin.mlless
let tag_mlequal, _, _ = Typecheck.Builtin.mlequal
let tag_mlgreater, _, _ = Typecheck.Builtin.mlgreater

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

(* let as_option ~at = function *)
(*   | Runtime.Tag (t, []) when (Runtime.equal_tag t tag_none)  -> None *)
(*   | Runtime.Tag (t, [x]) when (Runtime.equal_tag t tag_some) -> Some x *)
(*   | Runtime.(Judgement _ | Boundary _ | Derivation _ | External _ | Closure _ | Handler _ | *)
(*              Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v -> *)
(*      Runtime.(error ~at (OptionExpected v)) *)

(* let as_judgement_option ~at v = *)
(*   match as_option ~at v with *)
(*   | None -> None *)
(*   | Some (Runtime.Judgement jdg) -> Some jdg *)
(*   | Some (Runtime.(Boundary _ | Closure _ | External _ | Derivation _ | *)
(*           Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v) -> *)
(*      Runtime.(error ~at (JudgementExpected v)) *)

(** Conversion between OCaml coercible and ML coercible *)

(** Conversion from OCaml [Runtime.order] to  [ML.order]. *)
let mlless = Runtime.mk_tag tag_mlless []
let mlequal = Runtime.mk_tag tag_mlequal []
let mlgreater = Runtime.mk_tag tag_mlgreater []

(** Computations that invoke operations *)

let (>>=) = Runtime.bind
let return = Runtime.return

let operation_equal_type ~at t1 t2 =
  let v1 = Runtime.mk_judgement (Nucleus.(abstract_not_abstract (JudgementIsType t1)))
  and v2 = Runtime.mk_judgement (Nucleus.(abstract_not_abstract (JudgementIsType t2))) in
  Runtime.operation equal_type [v1;v2] >>= fun v ->
  return (Runtime.as_eq_type ~at v)

let operation_coerce ~at jdg bdry =
  let v1 = Runtime.Judgement jdg
  and v2 = Runtime.Boundary bdry in
  Runtime.operation coerce [v1;v2] >>= fun v ->
  return (Runtime.as_judgement_abstraction ~at v)
