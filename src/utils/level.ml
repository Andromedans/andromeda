type t = int

let parenthesize ~at_level ~max_level = max_level < at_level

type infix =
  | Infix0
  | Infix1
  | InfixCons
  | Infix2
  | Infix3
  | Infix4

let highest = 1000
let least = 0

let no_parens = least

let prefix = 50
let prefix_arg = 50

let constructor = 100
let constructor_arg = constructor - 1

let meta = constructor
let meta_arg = meta - 1

let infix = function
  | Infix4 -> (200, 199, 200)
  | Infix3 -> (300, 300, 299)
  | Infix2 -> (400, 400, 399)
  | InfixCons -> (450, 449, 450)
  | Infix1 -> (500, 499, 500)
  | Infix0 -> (600, 600, 599)

let eq = 700
let eq_left = eq - 1
let eq_right = eq - 1

let abstraction = 800
let abstraction_body = abstraction
let binder = abstraction

let judgement = 850
let judgement_thesis = judgement - 1

let derive = judgement

let boundary = judgement
let boundary_thesis = judgement_thesis

let assumptions = judgement - 1

let ml_app = constructor
let ml_app_arg = ml_app - 1

let ml_tag = ml_app
let ml_tag_arg = ml_tag - 1

let ml_operation = constructor
let ml_operation_arg = ml_operation - 1

let ml_tuple = highest
let ml_tuple_arg = 800

let ml_prod = 400
let ml_prod_arg = ml_prod - 1

let ml_arr = 500
let ml_arr_left = ml_arr - 1
let ml_arr_right = ml_arr

let ml_handler = ml_arr
let ml_handler_left = ml_arr_left
let ml_handler_right = ml_arr_right

let ml_forall_r = highest
