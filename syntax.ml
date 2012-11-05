type variable = Concrete.variable

type universe = Concrete.universe

type value =
  | Var of variable
  | App of value * value
  | Universe of universe
  | Pi of abstraction
  | Lambda of abstraction

and abstraction = variable * value * (value -> value)

(* Compilation from concrete. *)
let compile e =
  let rec compile env = function
    | Concrete.Var x -> (try List.assoc x env with Not_found -> Var x)
    | Concrete.Universe u -> Universe u
    | Concrete.Pi a -> Pi (compile_abstraction env a)
    | Concrete.Lambda a -> Lambda (compile_abstraction env a)
    | Concrete.App (e1, e2) -> App (compile env e1, compile env e2)
  and compile_abstraction env (x, t, e) =
    (x, compile env t, fun v -> compile ((x,v)::env) e)
  in
    compile [] e

(* Conversion back to concrete syntax, for pretty-printing. *)
let rec uneval = function
  | Var x -> Concrete.Var x
  | App (e1, e2) -> Concrete.App (uneval e1, uneval e2)
  | Universe u -> Concrete.Universe u
  | Pi a -> Concrete.Pi (uneval_vabstraction a)
  | Lambda a -> Concrete.Lambda (uneval_vabstraction a)

and uneval_vabstraction (x, t, f) =
  let x = Concrete.fresh_var x in
    (x, uneval t, uneval (f (Var x)))
