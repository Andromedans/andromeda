(** Renaming of bound variables for pretty printing. *)

open Syntax

(** Split a variable name into base and numerical postfix, e.g.,
   ["x42"] is split into [("x", 42)]. *)
let split s =
  let n = String.length s in
  let i = ref (n - 1) in
    while !i >= 0 && '0' <= s.[!i] && s.[!i] <= '9' do decr i done ;
    if !i < 0 || !i = n - 1 
    then (s, None)
    else
      let k = int_of_string (String.sub s (!i+1) (n - !i - 1)) in
        (String.sub s 0 (!i+1), Some k)

(** Given a variable [x] and substitution of variables to variables, does [x] appear
    in the codomain of the substitution? *)
let rec used x = function
  | [] -> false
  | (_, (Common.String y | Common.Gensym (y, _))) :: lst -> x = y || used x lst
  | (_, Common.Anonymous) :: lst -> used x lst

(** Given a variable [x] and a substitution of variables to variables, find a variant of
    [x] which does not appear in the codomain of the substitution. *)
let find_available x sbst =
  let x = (match x with Common.String x | Common.Gensym (x, _) -> x | Common.Anonymous -> "_") in
    if not (used x sbst)
    then x
    else 
      let (y, k) = split x in
      let k = ref (match k with Some k -> k | None -> 0) in
        while used (y ^ string_of_int !k) sbst do incr k done ;
        y ^ string_of_int !k

(** Does [x] occur freely in the given expression? *)
let rec occurs x (e, _) =
  match e with
    | Var y -> x = y
    | EVar _ -> false
    | Universe _ -> false
    | Pi a | Lambda a -> occurs_abstraction x a
    | App (e1, e2) -> occurs x e1 || occurs x e2
    | Ascribe (e1, e2) -> occurs x e1 || occurs x e2

and occurs_abstraction x (y, e1, e2) =
  occurs x e1 || (x <> y && occurs x e2)

(** Rename bound variables in the given expression for the purposes of
    pretty printing. *)
let beautify =
  let rec beautify sbst (e, loc) =
    (match e with
      | Var x -> (try Var (List.assoc x sbst) with Not_found -> Var x)
      | EVar (k, ctx, e) -> EVar (k, ctx, beautify sbst e)
      | Universe k -> Universe k
      | Pi a -> Pi (beautify_abstraction sbst a)
      | Lambda a -> Lambda (beautify_abstraction sbst a)
      | App (e1, e2) -> App (beautify sbst e1, beautify sbst e2)
      | Ascribe (e1, e2) -> Ascribe (beautify sbst e1, beautify sbst e2)),
    loc
      
  and beautify_abstraction sbst (x, e1, e2) =
    let y = 
      if occurs x e2
      then Common.String (find_available x sbst)
      else Common.Anonymous
    in
      (y, beautify sbst e1, beautify ((x,y) :: sbst) e2)
  in
    beautify []
