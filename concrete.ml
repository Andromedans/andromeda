type variable =
  | String of string
  | Gensym of string * int
  | Dummy

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
  | Parameter of variable * expr
  | Check of expr
  | Eval of expr

let fresh_var =
  let k = ref 0 in
    function
      | String x | Gensym (x, _) -> (incr k ; Gensym (x, !k))
      | Dummy -> (incr k ; Gensym ("_", !k))

let rec occurs x = function
  | Var y -> x = y
  | Universe _ -> false
  | Pi (y, e1, e2)
  | Lambda (y, e1, e2) -> occurs x e1 || (x <> y && occurs x e2)
  | App (e1, e2) -> occurs x e1 || occurs x e2

(* This nasty function is used to rename bound variables before
   they are shown to the user. *)
let beautify =
  (* Split a variable name into base and numerical postfix. *)
  let split s =
    let n = String.length s in
    let i = ref (n - 1) in
      while !i >= 0 && '0' <= s.[!i] && s.[!i] <= '9' do decr i done ;
      if !i < 0 || !i = n - 1 
      then (s, None)
      else
        let k = int_of_string (String.sub s (!i+1) (n - !i - 1)) in
          (String.sub s 0 (!i+1), Some k)
  in
  let rec used x = function
    | [] -> false
    | (_, (String y | Gensym (y, _))) :: lst -> x = y || used x lst
    | (_, Dummy) :: lst -> used x lst
  in
  let find_available x sbst =
    let x = (match x with String x | Gensym (x, _) -> x | Dummy -> "_") in
    if not (used x sbst)
    then x
    else 
      let (y, k) = split x in
      let k = ref (match k with Some k -> k | None -> 0) in
        while used (y ^ string_of_int !k) sbst do incr k done ;
        y ^ string_of_int !k
  in
  let rec beautify sbst = function
    | Var x -> (try Var (List.assoc x sbst) with Not_found -> Var x)
    | Universe k -> Universe k
    | Pi a -> Pi (beautify_abstraction sbst a)
    | Lambda a -> Lambda (beautify_abstraction sbst a)
    | App (e1, e2) -> App (beautify sbst e1, beautify sbst e2)
  and beautify_abstraction sbst (x, e1, e2) =
    let e1 = beautify sbst e1 in
    let y = 
      if occurs x e2
      then String (find_available x sbst)
      else Dummy
    in
      (y, e1, beautify ((x,y) :: sbst) e2)
  in
    beautify []
