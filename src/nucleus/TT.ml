(** The abstract syntax of Andromedan type theory (TT). *)

type bound = int

type ty =
  | TypeConstructor of Name.constructor * argument list

and term =
  | TermAtom of ty atom
  | TermBound of bound
  | TermConstructor of Name.constructor * argument list
  | TermConvert of term * assumption * ty

and eq_type = EqType of assumption * ty * ty

and eq_term = EqTerm of assumption * term * term * ty

and assumption = ty Assumption.t

and 't atom = { atom_name : Name.atom ; atom_type : 't }

(** An argument of a term or a type constructor *)
and argument =
  | ArgIsTerm of term abstraction
  | ArgIsType of ty abstraction
  | ArgEqType of eq_type abstraction
  | ArgEqTerm of eq_term abstraction

(** An abstracted entity. Note that abstractions only ever appear as arguments
   to constructors. Thus we do not carry any type information for the abstracted
   variable, as it can be recovered from the constructor. *)
and 'a abstraction =
  | Abstract of Name.ident * ty * 'a abstraction
  | NotAbstract of 'a


let equal_bound (i : bound) (j : bound) = (i = j)

(** Manipulation of assumptions. *)

(** The assumptions of a term [e] are the atoms and bound variables appearing in [e]. *)
let rec assumptions_term ?(lvl=0) = function

  | TermAtom {atom_name=x; atom_type=t} ->
     Assumption.add_free x t (assumptions_type ~lvl t)

  | TermBound k ->
     if k < lvl then
       Assumption.empty
     else
       Assumption.singleton_bound (k - lvl)

  | TermConstructor (_, args) ->
     assumptions_arguments ~lvl args

  | TermConvert (e, asmp', t) ->
     Assumption.union
       asmp'
       (Assumption.union (assumptions_term ~lvl e) (assumptions_type ~lvl t))

and assumptions_type ?(lvl=0) = function
  | TypeConstructor (_, args) -> assumptions_arguments ~lvl args

and assumptions_arguments ~lvl args =
  let rec fold asmp = function
    | [] -> asmp
    | arg :: args -> Assumption.union (assumptions_argument ~lvl arg) (fold asmp args)
  in
  fold Assumption.empty args

and assumptions_eq_type ?(lvl=0) (EqType (asmp, t1, t2)) =
  Assumption.union
    (assumptions_assumptions ~lvl asmp)
    (Assumption.union (assumptions_type ~lvl t1) (assumptions_type ~lvl t2))

and assumptions_eq_term ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  Assumption.union
    (Assumption.union (assumptions_assumptions ~lvl asmp) (assumptions_type ~lvl t))
    (Assumption.union (assumptions_term ~lvl e1) (assumptions_term ~lvl e2))

and assumptions_argument ?(lvl=0) = function
  | ArgIsType abstr -> assumptions_abstraction assumptions_type ~lvl abstr
  | ArgIsTerm abstr -> assumptions_abstraction assumptions_term ~lvl abstr
  | ArgEqType abstr -> assumptions_abstraction assumptions_eq_type ~lvl abstr
  | ArgEqTerm abstr -> assumptions_abstraction assumptions_eq_term ~lvl abstr

and assumptions_assumptions ?(lvl=0) asmp = Assumption.at_level ~lvl asmp

and assumptions_abstraction
  : 'a . (?lvl:bound -> 'a -> assumption) ->
        ?lvl:bound -> 'a abstraction -> assumption
 = fun asmp_v ?(lvl=0) -> function
  | NotAbstract v -> asmp_v ~lvl v
  | Abstract (x, u, abstr) ->
     Assumption.union
       (assumptions_type ~lvl u)
       (assumptions_abstraction asmp_v ~lvl:(lvl+1) abstr)

let assumptions_arguments = assumptions_arguments ~lvl:0

let context_u assumptions_u t =
  let asmp = assumptions_u t in
  let free, bound = Assumption.unpack asmp in
  assert (Assumption.BoundSet.is_empty bound) ;
  let free = Name.AtomMap.bindings free in
  List.map (fun (atom_name, atom_type) -> {atom_name; atom_type}) free

let context_abstraction assumptions_u =
  context_u (assumptions_abstraction ?lvl:None assumptions_u)

(* Helper functions *)

let fresh_atom x t =
  let x = Name.fresh x in
  { atom_name = x; atom_type = t }

let mk_atom a = TermAtom a

let mk_bound k = TermBound k

let mk_type_constructor c args = TypeConstructor (c, args)

let mk_term_constructor c args = TermConstructor (c, args)

let mk_term_convert e asmp t =
  match e with
  | TermConvert _ -> assert false
  | _ -> TermConvert (e, asmp, t)

let mk_arg_is_type t = ArgIsType t
let mk_arg_is_term e = ArgIsTerm e
let mk_arg_eq_type s = ArgEqType s
let mk_arg_eq_term s = ArgEqTerm s

let mk_eq_type asmp t1 t2 = EqType (asmp, t1, t2)

let mk_eq_term asmp e1 e2 t = EqTerm (asmp, e1, e2, t)

let mk_not_abstract e = NotAbstract e

let mk_abstract x t abstr = Abstract (x, t, abstr)

(** Shifting of bound variables *)
let rec shift_term ~lvl k = function

  | TermAtom _ as e ->
     e (* no bound variables in atoms *)

  | TermBound j as e ->
     if j < lvl then
       e
     else
       TermBound (j + k)

  | TermConstructor (c, args) ->
     let args = shift_args ~lvl k args
     in TermConstructor (c, args)

  | TermConvert (e, asmp, t) ->
     let e = shift_term ~lvl k e
     and asmp = Assumption.shift ~lvl k asmp
     and t = shift_type ~lvl k t
     in TermConvert (e, asmp, t)

and shift_type ~lvl k (TypeConstructor (c, args)) =
     let args = shift_args ~lvl k args
     in TypeConstructor (c, args)

and shift_eq_type ~lvl k (EqType (asmp, t1, t2)) =
  let asmp = Assumption.shift ~lvl k asmp
  and t1 = shift_type ~lvl k t1
  and t2 = shift_type ~lvl k t2
  in EqType (asmp, t1, t2)

and shift_eq_term ~lvl k (EqTerm (asmp, e1, e2, t)) =
  let asmp = Assumption.shift ~lvl k asmp
  and e1 = shift_term ~lvl k e1
  and e2 = shift_term ~lvl k e2
  and t = shift_type ~lvl k t
  in EqTerm (asmp, e1, e2, t)

and shift_args ~lvl k args =
  List.map (shift_arg ~lvl k) args

and shift_arg ~lvl k = function
   | ArgIsTerm abstr ->
      let abstr = shift_abstraction shift_term ~lvl k abstr in
      ArgIsTerm abstr

   | ArgIsType abstr ->
      let abstr = shift_abstraction shift_type ~lvl k abstr in
      ArgIsType abstr

   | ArgEqType abstr ->
      let abstr = shift_abstraction shift_eq_type ~lvl k abstr in
      ArgEqType abstr

   | ArgEqTerm abstr ->
      let abstr = shift_abstraction shift_eq_term ~lvl k abstr in
      ArgEqTerm abstr

and shift_abstraction
  : 'a . (lvl:bound -> int -> 'a -> 'a) ->
         lvl:bound -> int -> 'a abstraction -> 'a abstraction
  = fun shift_u ~lvl k -> function
  | NotAbstract u ->
     let u = shift_u ~lvl k u
     in NotAbstract u

  | Abstract (x, t, abstr) ->
     let t = shift_type ~lvl k t
     and abstr = shift_abstraction shift_u ~lvl:(lvl+1) k abstr
     in Abstract (x, t, abstr)


(** Instantiate *)

let rec instantiate_abstraction
  : 'a .(term -> ?lvl:bound -> 'a -> 'a) ->
        term -> ?lvl:bound -> 'a abstraction -> 'a abstraction
  = fun inst_v e0 ?(lvl=0) ->
  function
  | NotAbstract v ->
     let v = inst_v e0 ~lvl v in
     NotAbstract v

  | Abstract (x, u, abstr) ->
     let u = instantiate_type e0 ~lvl u
     and abstr = instantiate_abstraction inst_v e0 ~lvl:(lvl+1) abstr
     in
     Abstract (x, u, abstr)

and instantiate_term e0 ?(lvl=0) = function

    | TermAtom _ as e -> e (* there are no bound variables in an atom type *)

    | TermConstructor (c, args) ->
       let args = instantiate_arguments e0 ~lvl args in
       TermConstructor (c, args)

    | TermConvert (e, asmp, t) ->
       let e = instantiate_term e0 ~lvl e
       and asmp = instantiate_assumptions e0 ~lvl asmp
       and t = instantiate_type e0 ~lvl t in
       TermConvert (e, asmp, t)

    | TermBound k as e ->
       if k < lvl then
         e
       else begin
         (* We should only ever instantiate the highest occurring bound variable. *)
         assert (k = lvl) ;
         shift_term ~lvl:0 lvl e0
       end

and instantiate_type e0 ?(lvl=0) = function
  | TypeConstructor (c, args) ->
     let args = instantiate_arguments e0 ~lvl args in
     TypeConstructor (c, args)

and instantiate_arguments e0 ~lvl args =
  List.map (instantiate_argument e0 ~lvl) args

and instantiate_argument e0 ?(lvl=0) = function

    | ArgIsType t ->
       let t = instantiate_abstraction instantiate_type e0 ~lvl t in
       ArgIsType t

    | ArgIsTerm e ->
       let e = instantiate_abstraction instantiate_term e0 ~lvl e in
       ArgIsTerm e

    | ArgEqType asmp ->
       let asmp = instantiate_abstraction instantiate_eq_type e0 ~lvl asmp in
       ArgEqType asmp

    | ArgEqTerm asmp ->
       let asmp = instantiate_abstraction instantiate_eq_term e0 ~lvl asmp in
       ArgEqTerm asmp

and instantiate_eq_type e0 ?(lvl=0) (EqType (asmp, t1, t2)) =
  let asmp = instantiate_assumptions e0 ~lvl asmp
  and t1 = instantiate_type e0 ~lvl t1
  and t2 = instantiate_type e0 ~lvl t2 in
  EqType (asmp, t1, t2)

and instantiate_eq_term e0 ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  let asmp = instantiate_assumptions e0 ~lvl asmp
  and e1 = instantiate_term e0 ~lvl e1
  and e2 = instantiate_term e0 ~lvl e2
  and t = instantiate_type e0 ~lvl t in
  EqTerm (asmp, e1, e2, t)

and instantiate_assumptions e0 ?(lvl=0) asmp =
  let asmp0 = assumptions_term ~lvl e0 in
  Assumption.instantiate ~lvl asmp0 asmp

let rec fully_instantiate_type ?(lvl=0) es (TypeConstructor (c, args)) =
  let args = fully_instantiate_args ~lvl es args in
  TypeConstructor (c, args)

and fully_instantiate_term ?(lvl=0) es = function

  | TermAtom _ as e -> e (* there are no bound variables in an atom type *)

  | (TermBound k) as e ->
     if k < lvl then
       e
     else
       (* XXX can fail here, should we report an error or die? *)
       let e = List.nth es (k - lvl)
       in shift_term ~lvl:0 lvl e

  | TermConstructor (c, args) ->
     let args = fully_instantiate_args ~lvl es args in
     TermConstructor (c, args)

  | TermConvert (e, asmp, t) ->
     let e = fully_instantiate_term ~lvl es e
     and asmp = fully_instantiate_assumptions ~lvl es asmp
     and t = fully_instantiate_type ~lvl es t
     in TermConvert (e, asmp, t)

and fully_instantiate_eq_type ?(lvl=0) es (EqType (asmp, t1, t2)) =
  let asmp = fully_instantiate_assumptions ~lvl es asmp
  and t1 = fully_instantiate_type ~lvl es t1
  and t2 = fully_instantiate_type ~lvl es t2
  in EqType (asmp, t1, t2)

and fully_instantiate_eq_term ?(lvl=0) es (EqTerm (asmp, e1, e2, t)) =
  let asmp = fully_instantiate_assumptions ~lvl es asmp
  and e1 = fully_instantiate_term ~lvl es e1
  and e2 = fully_instantiate_term ~lvl es e2
  and t = fully_instantiate_type ~lvl es t
  in EqTerm (asmp, e1, e2, t)


and fully_instantiate_assumptions ~lvl es asmp =
  let asmps = List.map (assumptions_term ~lvl) es in
  Assumption.fully_instantiate asmps ~lvl asmp

and fully_instantiate_args ?(lvl=0) es args =
  List.map (fully_instantiate_arg ~lvl es) args

and fully_instantiate_arg ?(lvl=0) es = function
  | ArgIsType abstr ->
     let abstr = fully_instantiate_abstraction fully_instantiate_type ~lvl es abstr in
     ArgIsType abstr

  | ArgIsTerm abstr ->
     let abstr = fully_instantiate_abstraction fully_instantiate_term ~lvl es abstr in
     ArgIsTerm abstr

  | ArgEqType abstr ->
     let abstr = fully_instantiate_abstraction fully_instantiate_eq_type ~lvl es abstr in
     ArgEqType abstr

  | ArgEqTerm abstr ->
     let abstr = fully_instantiate_abstraction fully_instantiate_eq_term ~lvl es abstr in
     ArgEqTerm abstr

and fully_instantiate_abstraction
  : 'a . (?lvl:int -> term list -> 'a -> 'a) ->
         ?lvl:int -> term list -> 'a abstraction -> 'a abstraction
  = fun inst_u ?(lvl=0) es -> function

  | NotAbstract u ->
     let u = inst_u ~lvl es u in
     NotAbstract u

  | Abstract (x, t, abstr) ->
     let t = fully_instantiate_type ~lvl es t
     and abstr = fully_instantiate_abstraction inst_u ~lvl:(lvl+1) es abstr
     in Abstract (x, t, abstr)

(** Unabstract *)

let unabstract_type x t1 t2 =
  let a = fresh_atom x t1 in
  a, instantiate_type (mk_atom a) t2

let unabstract_term x t e =
  let a = fresh_atom x t in
  a, instantiate_term (mk_atom a) e

let unabstract_eq_type x t eq =
  let a = fresh_atom x t in
  a, instantiate_eq_type (mk_atom a) eq

let unabstract_eq_term x t eq =
  let a = fresh_atom x t in
  a, instantiate_eq_term (mk_atom a) eq

let unabstract_abstraction instantiate_u x t abstr =
  let a = fresh_atom x t in
  a, instantiate_abstraction instantiate_u (mk_atom a) abstr

(** Abstract *)

let rec abstract_term x ?(lvl=0) = function
  | (TermAtom {atom_name=y; atom_type=t}) as e ->
     begin match Name.eq_atom x y with
     | false -> ignore e ; failwith "(* XXX check that t does not depend on x, then give me e !!! *)"
     | true -> TermBound lvl
     end

  | TermBound k as e ->
     if k < lvl then
       e
     else
       assert false
       (* we should never get here because abstracting
          should always introduce a highest-level bound
          index. *)

  | TermConstructor (c, args) ->
     let args = abstract_arguments x ~lvl args in
     TermConstructor (c, args)

  | TermConvert (c, asmp, t) ->
     let asmp = Assumption.abstract x ~lvl asmp
     and t = abstract_type x ~lvl t in
     TermConvert (c, asmp, t)

and abstract_type x ?(lvl=0) = function
  | TypeConstructor (c, args) ->
     let args = abstract_arguments x ~lvl args in
     TypeConstructor (c, args)

and abstract_arguments x ?(lvl=0) args =
  List.map (abstract_argument x ~lvl) args

and abstract_argument x ?(lvl=0) = function

    | ArgIsType t -> ArgIsType (abstract_abstraction abstract_type x ~lvl t)

    | ArgIsTerm e -> ArgIsTerm (abstract_abstraction abstract_term x ~lvl e)

    | ArgEqType asmp ->
       let asmp = abstract_abstraction abstract_eq_type x ~lvl asmp in
       ArgEqType asmp

    | ArgEqTerm asmp ->
       let asmp = abstract_abstraction abstract_eq_term x ~lvl asmp in
       ArgEqTerm asmp

and abstract_assumptions x ?(lvl=0) asmp =
  Assumption.abstract x ~lvl asmp

and abstract_eq_type x ?(lvl=0) (EqType (asmp, t1, t2)) =
  let asmp = abstract_assumptions x ~lvl asmp
  and t1 = abstract_type x ~lvl t1
  and t2 = abstract_type x ~lvl t2
  in EqType (asmp, t1, t2)

and abstract_eq_term x ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  let asmp = abstract_assumptions x ~lvl asmp
  and e1 = abstract_term x ~lvl e1
  and e2 = abstract_term x ~lvl e2
  and t = abstract_type x ~lvl t
  in EqTerm (asmp, e1, e2, t)

and abstract_abstraction
  : 'a . (Name.atom -> ?lvl:int -> 'a -> 'a) ->
         Name.atom -> ?lvl:int -> 'a abstraction -> 'a abstraction
  = fun abstr_v x ?(lvl=0) ->
  function
  | NotAbstract v ->
     let v = abstr_v x ~lvl v in
     NotAbstract v

  | Abstract (y, u, abstr) ->
     let u = abstract_type x ~lvl u in
     let abstr = abstract_abstraction abstr_v x ~lvl:(lvl+1) abstr in
     Abstract (y, u, abstr)

(** Substitute *)
let substitute_term e0 x e =
  let e = abstract_term x e in
  instantiate_term e0 e

let substitute_type e0 x t =
  let t = abstract_type x t in
  instantiate_type e0 t

(* Does the bound variable [k] occur in an expression? Used only for printing. *)
let rec occurs_term k = function
  | TermAtom _ -> false
  | TermBound m -> k = m
  | TermConstructor (_, args) -> occurs_args k args
  | TermConvert (e, asmp, t) -> occurs_term k e || occurs_assumptions k asmp || occurs_type k t

and occurs_type k = function
  | TypeConstructor (_, args) -> occurs_args k args

and occurs_args k = function
  | [] -> false
  | arg :: args -> occurs_arg k arg || occurs_args k args

and occurs_arg k = function
  | ArgIsType t  -> occurs_abstraction occurs_type k t
  | ArgIsTerm e  -> occurs_abstraction occurs_term k e
  | ArgEqType abstr -> occurs_abstraction occurs_eq_type k abstr
  | ArgEqTerm abstr -> occurs_abstraction occurs_eq_term k abstr

and occurs_eq_type k (EqType (asmp, t1, t2)) =
  occurs_assumptions k asmp || occurs_type k t1 || occurs_type k t2

and occurs_eq_term k (EqTerm (asmp, e1, e2, t)) =
  occurs_assumptions k asmp || occurs_term k e1 || occurs_term k e2 || occurs_type k t

and occurs_abstraction
  : 'a . (bound -> 'a -> bool) -> bound -> 'a abstraction -> bool
  = fun occurs_v k ->
  function
  | NotAbstract v -> occurs_v k v
  | Abstract (_, u, abstr) ->
     occurs_type k u || occurs_abstraction occurs_v (k+1) abstr

and occurs_assumptions k asmp =
  Assumption.mem_bound k asmp

(****** Alpha equality ******)

let rec alpha_equal_term e1 e2 =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | TermAtom {atom_name=x;_}, TermAtom {atom_name=y;_} -> Name.eq_atom x y

    | TermBound i, TermBound j -> i = j

    | TermConstructor (c, args), TermConstructor (c', args') ->
       Name.eq_ident c c' && alpha_equal_args args args'

    | TermConvert (e1, _, _), TermConvert (e2, _, _) ->
       alpha_equal_term e1 e2

    | (TermAtom _ | TermBound _ | TermConstructor _  | TermConvert _), _ ->
      false
  end

and alpha_equal_type t1 t2 =
  match t1, t2 with
  | TypeConstructor (c, args), TypeConstructor (c', args') ->
     Name.eq_ident c c' && alpha_equal_args args args'

and alpha_equal_args args args' =
  match args, args' with

  | [], [] -> true

  | (ArgIsTerm e)::args, (ArgIsTerm e')::args' ->
     alpha_equal_abstraction alpha_equal_term e e' && alpha_equal_args args args'

  | (ArgIsType t)::args, (ArgIsType t')::args' ->
     alpha_equal_abstraction alpha_equal_type t t' && alpha_equal_args args args'

  | ArgEqType _ :: args, ArgEqType _ :: args' -> alpha_equal_args args args'

  | ArgEqTerm _ :: args, ArgEqTerm _ :: args' -> alpha_equal_args args args'

  | (ArgIsTerm _ | ArgIsType _ | ArgEqType _ | ArgEqTerm _)::_, _::_

  | (_::_), []

  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false

and alpha_equal_abstraction
  : 'a . ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool
  = fun equal_v e e' ->
  e == e' ||
  (* XXX try e = e' ? *)
  match e, e' with

  | Abstract (_, u, abstr), Abstract(_, u', abstr') ->
     alpha_equal_type u u' &&
     alpha_equal_abstraction equal_v abstr abstr'

  | NotAbstract v, NotAbstract v' -> equal_v v v'

  | (Abstract _ | NotAbstract _), _ -> false

(****** Printing routines *****)
type print_env =
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ; }

let add_forbidden x penv = { penv with forbidden = x :: penv.forbidden }

let rec print_abstraction
   : 'b . (bound -> 'b -> bool) ->
          (?max_level:Level.t -> penv:print_env -> 'b -> Format.formatter -> unit) ->
          ?max_level:Level.t ->
          penv:print_env ->
          'b abstraction ->
          Format.formatter -> unit
  = fun occurs_v print_v ?max_level ~penv abstr ppf ->
  let rec fold penv xus = function

    | NotAbstract v ->
       let xus = List.rev xus in
       Print.print ?max_level ppf ~at_level:Level.binder "@[<hov 2>%t@ %t@]"
              (Print.sequence (print_binder ~penv) "" xus)
              (print_v ~penv v)

    | Abstract (x, u, abstr) ->
       let x =
         (if occurs_abstraction occurs_v 0 abstr then
            Name.refresh penv.forbidden x
          else
            Name.anonymous ())
       in
       let penv = add_forbidden x penv in
       fold penv ((x,u) :: xus) abstr

  in

  fold penv [] abstr

and print_term ?max_level ~penv e ppf =
  match e with
  | TermAtom {atom_name=x; _} ->
     Name.print_atom ~printer:(penv.atoms) x ppf

  | TermBound k -> Name.print_debruijn penv.forbidden k ppf

  | TermConstructor (c, args) ->
     print_constructor ?max_level ~penv c args ppf

  | TermConvert (e, _, _) -> print_term ~penv ?max_level e ppf

and print_type ?max_level ~penv t ppf =
  match t with

  | TypeConstructor (c, args) ->
     print_constructor ?max_level ~penv c args ppf

and print_constructor ?max_level ~penv c args ppf =
  Format.pp_open_hovbox ppf 2 ;
  Print.print ~at_level:Level.app ?max_level ppf "%t@ %t"
    (Name.print_ident c)
    (Print.sequence (print_arg ~penv) "" args) ;
  Format.pp_close_box ppf ()

and print_arg ~penv arg ppf =
  match arg with
  | ArgIsTerm abstr -> print_abstraction occurs_term print_term ~penv abstr ppf
  | ArgIsType abstr -> print_abstraction occurs_type print_type ~penv abstr ppf
  | ArgEqType _ -> () (* XXX should we print something to indicate the argument is there? *)
  | ArgEqTerm _ -> ()

and print_binder ~penv (x,t) ppf =
  Print.print ppf "(%t@ :@ %t)"
    (Name.print_ident ~parentheses:true x)
    (print_type ~penv t)


(** Conversion to JSON *)

module Json =
struct

  let rec term e =
    match e with

      | TermAtom {atom_name=x; atom_type=t} -> Json.tag "TermAtom" [Name.Json.atom x; ty t]

      | TermBound b -> Json.tag "TermBound" [Json.Int b]

      | TermConstructor (c, lst) -> Json.tag "TermConstructor" (Name.Json.ident c :: args lst)

      | TermConvert (e, asmp, t) -> Json.tag "TermConvert" [term e; Assumption.Json.assumptions asmp; ty t]

  and ty = function
      | TypeConstructor (c, lst) -> Json.tag "TypeConstructor" (Name.Json.ident c :: args lst)

  and args lst =
    (List.map
       (function
        | ArgIsTerm abstr -> Json.tag "ArgIsTerm" (abstraction term [] abstr)
        | ArgIsType abstr -> Json.tag "ArgIsType" (abstraction ty [] abstr)
        | ArgEqType _ -> Json.tag "ArgIsType" []
        | ArgEqTerm _ -> Json.tag "ArgEqTerm" [])
       lst)

  and abstraction : 'a . ('a -> Json.t) -> (Name.ident * ty) list -> 'a abstraction -> Json.t list =
    fun json_u xts ->
    function
    | Abstract (x, t, abstr) ->
       abstraction json_u ((x,t) :: xts) abstr
    | NotAbstract u ->
       let xts = List.map (fun (x, t) -> Json.List [Name.Json.ident x; ty t])  (List.rev xts) in
       [Json.tuple xts ; json_u u]
end
