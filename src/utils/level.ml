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

let proj = no_parens
let proj_left = no_parens

let prefix = 50
let prefix_arg = 50

let app = 100
let app_left = app
let app_right = app - 1

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

let binder = 800
let in_binder = binder
let arr = binder
let arr_left = arr - 1
let arr_right = arr

let ascription = 950

let jdg = highest

let ml_app = 300
let ml_app_arg = ml_app - 1

let ml_prod = 400
let ml_prod_arg = ml_prod - 1

let ml_arr = 500
let ml_arr_left = ml_arr - 1
let ml_arr_right = ml_arr

let ml_handler = ml_arr
let ml_handler_left = ml_arr_left
let ml_handler_right = ml_arr_right

let ml_forall_r = highest

