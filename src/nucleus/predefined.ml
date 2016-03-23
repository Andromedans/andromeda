let name_some          = Name.make "Some"
let name_none          = Name.make "None"
let name_cons          = Name.cons
let name_nil           = Name.nil

let predefined_aml_types =
  let decl_option =
    ["mltype option α = ";
     "  | None";
     "  | Some of α";
     "end"]
  and decl_list =
    ["mltype rec list α =";
    "  | nil";
    "  | ( :: ) of α and list α";
     "end"]
  in
  List.map (String.concat "\n") [decl_option; decl_list]
  |> (String.concat "\n")

let name_equal        = Name.make "equal"
let name_as_prod      = Name.make "as_prod"
let name_as_eq        = Name.make "as_eq"

let predefined_ops =
  let ops =
    ["operation equal : Judgement -> Judgement -> option Judgement";
     "operation as_prod : Judgement -> option Judgement";
     "operation as_eq : Judgement -> option Judgement"] in
  String.concat "\n" ops

let definitions = String.concat "\n" [predefined_aml_types; predefined_ops]

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
  | (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ | Runtime.Ref _ | Runtime.String _ | Runtime.Ident _) ->
     None

let as_list ~loc v =
  match as_list_opt v with
  | Some lst -> lst
  | None -> Error.runtime ~loc "expected a list but got %s" (Runtime.name_of v)

let from_option = function
  | None -> Runtime.mk_tag name_none []
  | Some v -> Runtime.mk_tag name_some [v]

let as_option ~loc = function
  | Runtime.Tag (t,[]) when (Name.eq_ident t name_none)  -> None
  | Runtime.Tag (t,[x]) when (Name.eq_ident t name_some) -> Some x
  | (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ | Runtime.Ref _ | Runtime.String _ | Runtime.Ident _) as v ->
     Error.runtime ~loc "expected an option but got %s" (Runtime.name_of v)

let operation_equal v1 v2 =
  Runtime.operation name_equal [v1;v2]

let operation_as_prod v =
  Runtime.operation name_as_prod [v]

let operation_as_eq v =
  Runtime.operation name_as_eq [v]

