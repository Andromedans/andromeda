(* ***** Predefined operations and conversion from AML to OCaml ***** *)

(** Conversions between OCaml list and ML list *)

let (_, tag_nil) = Desugar.Builtin.nil
let (_, tag_cons) = Desugar.Builtin.cons

let (_, tag_none) = Desugar.Builtin.none
let (_, tag_some) = Desugar.Builtin.some

let (_, tag_notcoercible) = Desugar.Builtin.notcoercible
let (_, tag_convertible) = Desugar.Builtin.convertible
let (_, tag_coercible_constructor) = Desugar.Builtin.coercible_constructor

let (_, tag_mlless) = Desugar.Builtin.mlless
let (_, tag_mlequal) = Desugar.Builtin.mlequal
let (_, tag_mlgreater) = Desugar.Builtin.mlgreater


let equal_term, _ = Typecheck.Builtin.equal_term
let equal_type, _ = Typecheck.Builtin.equal_type
let coerce, _ = Typecheck.Builtin.coerce

let list_nil = Runtime.mk_tag tag_nil []

let list_cons v lst = Runtime.mk_tag tag_cons [v; lst]

let rec mk_list = function
  | []      -> list_nil
  | x :: xs -> list_cons x (mk_list xs)

(* let as_list ~loc v = *)
(*   match Runtime.as_list_opt v with *)
(*   | Some lst -> lst *)
(*   | None -> Runtime.(error ~loc (ListExpected v)) *)

(** Conversion between Ocaml option and ML option *)

let mk_option = function
  | Some v -> Runtime.mk_tag tag_some [v]
  | None -> Runtime.mk_tag tag_none []

let as_option ~loc = function
  | Runtime.Tag (t, []) when (Runtime.equal_tag t tag_none)  -> None
  | Runtime.Tag (t, [x]) when (Runtime.equal_tag t tag_some) -> Some x
  | (Runtime.IsType _ | Runtime.IsTerm _ | Runtime.EqType _ | Runtime.EqTerm _ |
     Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _ | Runtime.Dyn _ | Runtime.String _) as v ->
     Runtime.(error ~loc (OptionExpected v))

(** Conversion between OCaml coercible and ML coercible *)

let as_coercible ~loc = function

  | Runtime.Tag (t, []) when Runtime.equal_tag t tag_notcoercible ->
    Runtime.NotCoercible

  | Runtime.Tag (t, [v]) when Runtime.equal_tag t tag_convertible ->
    let eq = Runtime.as_eq_type_abstraction ~loc v in
    Runtime.Convertible eq

  | Runtime.Tag (t, [v]) when Runtime.equal_tag t tag_coercible_constructor ->
    let e = Runtime.as_is_term_abstraction ~loc v in
    Runtime.Coercible e

  | (Runtime.IsType _ | Runtime.IsTerm _ | Runtime.EqType _ | Runtime.EqTerm _ |
     Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _ | Runtime.Dyn _ | Runtime.String _) as v ->
     Runtime.(error ~loc (CoercibleExpected v))

(** Conversion from OCaml [Runtime.order] to  [ML.order]. *)
let mlless = Runtime.mk_tag tag_mlless []
let mlequal = Runtime.mk_tag tag_mlequal []
let mlgreater = Runtime.mk_tag tag_mlgreater []

(** Computations that invoke operations *)

(* Map ML-value-to-(term)-judgment across an option. Fail if given Some value
   that is not a judgment. *)

let as_eq_term_option ~loc v =
  match as_option ~loc v with
    | Some v -> Some (Runtime.as_eq_term ~loc v)
    | None -> None

let as_eq_type_option ~loc v =
  match as_option ~loc v with
    | Some v -> Some (Runtime.as_eq_type ~loc v)
    | None -> None

let (>>=) = Runtime.bind
let return = Runtime.return

let operation_equal_term ~loc e1 e2 =
  let v1 = Runtime.mk_is_term (Nucleus.abstract_not_abstract e1)
  and v2 = Runtime.mk_is_term (Nucleus.abstract_not_abstract e2) in
  Runtime.operation equal_term [v1;v2] >>= fun v ->
  return (as_eq_term_option ~loc v)

let operation_equal_type ~loc t1 t2 =
  let v1 = Runtime.mk_is_type (Nucleus.abstract_not_abstract t1)
  and v2 = Runtime.mk_is_type (Nucleus.abstract_not_abstract t2) in
  Runtime.operation equal_type [v1;v2] >>= fun v ->
  return (as_eq_type_option ~loc v)

let operation_coerce ~loc e t =
  let v1 = Runtime.mk_is_term e
  and v2 = Runtime.mk_is_type t in
  Runtime.operation coerce [v1;v2] >>= fun v ->
  return (as_coercible ~loc v)

let add_abstracting j m =
  let v = Runtime.mk_is_term j in             (* The given variable as an ML value *)
  Runtime.hypotheses >>= fun hyps_dyn ->      (* Get the ML list of [hypotheses] *)
  Runtime.lookup_dyn hyps_dyn >>= fun hyps ->
  let hyps = list_cons v hyps in              (* Add v to the front of that ML list *)
  Runtime.now hyps_dyn hyps m                 (* Run computation m in this dynamic scope *)
