type variable = Concrete.variable

type universe = Concrete.universe

type expr =
  | Var of variable
  | Bound of int
  | App of expr * expr
  | Universe of universe
  | Pi of abstraction
  | Lambda of abstraction

and abstraction = variable * expr * expr

(* Compilation from concrete syntax. *)
let compile ctx e =
  let rec compile k 

 function
  | Concrete.Var x -> (try List.assoc x ctx with Not_found -> Var x)
  | Concrete.Universe u -> Universe u
  | Concrete.Pi a -> Pi (compile_abstraction env a)
  | Concrete.Lambda a -> Lambda (compile_abstraction env a)
  | Concrete.App (e1, e2) -> App (compile env e1, compile env e2)

and compile_abstraction env (x, t, e) =
  (x, compile env t, fun v -> compile ((x,v)::env) e)

(* Conversion back to concrete syntax, for pretty-printing. *)
let rec uncompile = function
  | Var x -> Concrete.Var x
  | App (e1, e2) -> Concrete.App (uncompile e1, uncompile e2)
  | Universe u -> Concrete.Universe u
  | Pi a -> Concrete.Pi (uncompile_vabstraction a)
  | Lambda a -> Concrete.Lambda (uncompile_vabstraction a)

and uncompile_vabstraction (x, t, f) =
  let x = Concrete.fresh_var x in
    (x, uncompile t, uncompile (f (Var x)))
