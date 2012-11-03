type variable =
  | String of string
  | Dummy
  | Gensym of string * int

let fresh_var =
  let k = ref 0 in
    fun x ->
      let x = (match x with
        | String x -> x
        | Gensym (x, _) -> x
        | Dummy -> "_")
      in
        incr k ; Gensym (x, !k)

type universe = int

type expr =
  | Var of variable
  | Universe of universe
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr

and abstraction = variable * expr * expr

type directive =
  | Quit
  | Help
  | Context
  | Assume of variable * expr

type toplevel =
  | Expr of expr
  | Directive of directive
