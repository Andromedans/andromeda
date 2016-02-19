type t = int

type infix =
  | Infix0
  | Infix1
  | Infix2
  | Infix3
  | Infix4

let highest = 1000

let no_parens = 0

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

let struct_clause = 900
let sig_clause = 900

let ascription = highest

let jdg = 4

