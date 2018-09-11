(** The abstract syntax of Andromedan type theory (TT). *)

type bound = int

(** An abstracted entity. Note that abstractions only ever appear as arguments
   to constructors. Thus we do not carry any type information for the abstracted
   variable, as it can be recovered from the constructor. *)
type ('a, 'b) abstraction =
  | Abstract of Name.ident * 'a * ('a,'b) abstraction
  | NotAbstract of 'b

type 'a argument_abstraction = (unit, 'a) abstraction

type term =
  | TermAtom of Name.atom * ty
  | TermBound of bound
  | TermConstructor of Name.constructor * argument list
  | TermConvert of term * assumption * ty

and ty =
  | TypeConstructor of Name.constructor * argument list

and eq_type = EqType of assumption

and eq_term = EqTerm of assumption

and assumption = ty Assumption.t

(** An argument of a term or a type constructor *)
and argument =
  | ArgIsTerm of term argument_abstraction
  | ArgIsType of ty argument_abstraction
  | ArgEqType of eq_type argument_abstraction
  | ArgEqTerm of eq_term argument_abstraction

(** Manipulation of assumptions. *)

(** The assumptions of a term [e] are the atoms and bound variables appearing in [e]. *)
let rec assumptions_term ~lvl = function

  | TermAtom (x, t) -> Assumption.add_free x t (assumptions_type ~lvl t)

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

and assumptions_type ~lvl = function
  | TypeConstructor (_, args) -> assumptions_arguments ~lvl args

and assumptions_arguments ~lvl args =
  let rec fold asmp = function
    | [] -> asmp
    | arg :: args -> Assumption.union (assumptions_argument ~lvl arg) (fold asmp args)
  in
  fold Assumption.empty args

and assumptions_eq_type ~lvl (EqType asmp) =
  Assumption.shift lvl asmp

and assumptions_eq_term ~lvl (EqTerm asmp) =
  Assumption.shift lvl asmp

and assumptions_argument ~lvl = function
  | ArgIsType abstr -> assumptions_abstraction assumptions_unit assumptions_type ~lvl abstr
  | ArgIsTerm abstr -> assumptions_abstraction assumptions_unit assumptions_term ~lvl abstr
  | ArgEqType asmp -> assumptions_abstraction assumptions_unit assumptions_eq_type ~lvl asmp
  | ArgEqTerm asmp -> assumptions_abstraction assumptions_unit assumptions_eq_term ~lvl asmp

and assumptions_unit ~lvl _ = Assumption.empty

and assumptions_abstraction
  : 'a 'b . (lvl:bound -> 'a -> assumption) ->
            (lvl:bound -> 'b -> assumption) ->
            lvl:bound -> ('a, 'b) abstraction -> assumption
 = fun asmp_u asmp_v ~lvl -> function
  | NotAbstract v -> asmp_v ~lvl v
  | Abstract (x, u, abstr) ->
     Assumption.union
       (asmp_u ~lvl u)
       (assumptions_abstraction asmp_u asmp_v ~lvl:(lvl+1) abstr)

(* Helper functions *)

let mk_atom x t = TermAtom (x, t)

let fresh_atom x t =
  let x = Name.fresh x in
  mk_atom x t

let mk_type_constructor c args = failwith "todo"

let mk_arg_is_type t = ArgIsType t
let mk_arg_is_term e = ArgIsTerm e
let mk_arg_eq_type s = ArgEqType s
let mk_arg_eq_term s = ArgEqTerm s

let mk_not_abstract e = NotAbstract e

let mk_abstract x t abstr = Abstract (x, t, abstr)

(** Instantiate *)

let rec instantiate_abstraction
  : 'a 'b . (term -> ?lvl:bound -> 'a -> 'a) ->
            (term -> ?lvl:bound -> 'b -> 'b) ->
            term -> ?lvl:bound -> ('a, 'b) abstraction -> ('a, 'b) abstraction
  = fun inst_u inst_v e0 ?(lvl=0) ->
  function
  | NotAbstract v ->
     let v = inst_v e0 ~lvl v in
     NotAbstract v

  | Abstract (x, u, abstr) ->
     let u = inst_u e0 ~lvl u
     and abstr = instantiate_abstraction inst_u inst_v e0 ~lvl:(lvl+1) abstr
     in
     Abstract (x, u, abstr)

let rec instantiate_term e0 ?(lvl=0) = function

    | TermConstructor (c, args) ->
       let args = instantiate_arguments e0 ~lvl args in
       TermConstructor (c, args)

    | TermConvert (e, asmp, t) ->
       let e = instantiate_term e0 ~lvl e
       and asmp = instantiate_assumptions e0 ~lvl asmp
       and t = instantiate_type e0 ~lvl t in
       TermConvert (e, asmp, t)

    | TermAtom _ as e -> e

    | TermBound k as e ->
       if k < lvl then
         e
       else
         if k = lvl then
           e0
         else
           TermBound (k - 1)

and instantiate_type e0 ?(lvl=0) = function
  | TypeConstructor (c, args) ->
     let args = instantiate_arguments e0 ~lvl args in
     TypeConstructor (c, args)

and instantiate_arguments e0 ~lvl args =
  List.map (instantiate_argument e0 ~lvl) args

and instantiate_argument e0 ?(lvl=0) = function

    | ArgIsType t ->
       let t = instantiate_abstraction instantiate_unit instantiate_type e0 ~lvl t in
       ArgIsType t

    | ArgIsTerm e ->
       let e = instantiate_abstraction instantiate_unit instantiate_term e0 ~lvl e in
       ArgIsTerm e

    | ArgEqType asmp ->
       let asmp = instantiate_abstraction instantiate_unit instantiate_eq_type e0 ~lvl asmp in
       ArgEqType asmp

    | ArgEqTerm asmp ->
       let asmp = instantiate_abstraction instantiate_unit instantiate_eq_term e0 ~lvl asmp in
       ArgEqTerm asmp

and instantiate_eq_type e0 ?(lvl=0) (EqType asmp) =
  let asmp = assumptions_term ~lvl e0 in
  EqType asmp

and instantiate_eq_term e0 ?(lvl=0) (EqTerm asmp) =
  let asmp = assumptions_term ~lvl e0 in
  EqTerm asmp

and instantiate_assumptions e0 ?(lvl=0) asmp =
  let asmp' = assumptions_term ~lvl e0 in
  Assumption.instantiate asmp' ~lvl asmp

and instantiate_unit _ ?(lvl=0) () = ()

(** Abstract *)

let rec abstract_term x ?(lvl=0) = function
  | (TermAtom (y, t)) as e ->
     begin match Name.eq_atom x y with
     | false -> e
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

    | ArgIsType t -> ArgIsType (abstract_abstraction abstract_unit abstract_type x ~lvl t)

    | ArgIsTerm e -> ArgIsTerm (abstract_abstraction abstract_unit abstract_term x ~lvl e)

    | ArgEqType asmp ->
       let asmp = abstract_abstraction abstract_unit abstract_eq_type x ~lvl asmp in
       ArgEqType asmp

    | ArgEqTerm asmp ->
       let asmp = abstract_abstraction abstract_unit abstract_eq_term x ~lvl asmp in
       ArgEqTerm asmp

and abstract_eq_type x ?(lvl=0) (EqType asmp) =
  let asmp = Assumption.abstract x ~lvl asmp in
  EqType asmp

and abstract_eq_term x ?(lvl=0) (EqTerm asmp) =
  let asmp = Assumption.abstract x ~lvl asmp in
  EqTerm asmp

and abstract_unit _ ?(lvl=0) () = ()

and abstract_abstraction
  : 'a 'b . (Name.atom -> ?lvl:int -> 'a -> 'a) ->
            (Name.atom -> ?lvl:int -> 'b -> 'b) ->
            Name.atom -> ?lvl:int -> ('a, 'b) abstraction -> ('a, 'b) abstraction
  = fun abstr_u abstr_v x ?(lvl=0) ->
  function
  | NotAbstract v ->
     let v = abstr_v x ~lvl v in
     NotAbstract v

  | Abstract (y, u, abstr) ->
     let u = abstr_u x ~lvl u in
     let abstr = abstract_abstraction abstr_u abstr_v x ~lvl:(lvl+1) abstr in
     Abstract (y, u, abstr)

(** Substitute *)
let substitute_term x e0 e =
  let e = abstract_term x e in
  instantiate_term e0 e

let substitute_type x e0 t =
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
  | ArgIsType t  -> occurs_abstraction occurs_unit occurs_type k t
  | ArgIsTerm e  -> occurs_abstraction occurs_unit occurs_term k e
  | ArgEqType abstr -> occurs_abstraction occurs_unit occurs_eq_type k abstr
  | ArgEqTerm abstr -> occurs_abstraction occurs_unit occurs_eq_term k abstr

and occurs_eq_type k (EqType asmp) = occurs_assumptions k asmp

and occurs_eq_term k (EqTerm asmp) = occurs_assumptions k asmp

and occurs_unit _ _ = false

and occurs_abstraction
  : 'a 'b . (bound -> 'a -> bool) ->
            (bound -> 'b -> bool) ->
            bound -> ('a, 'b) abstraction -> bool
  = fun occurs_u occurs_v k ->
  function
  | NotAbstract v -> occurs_v k v
  | Abstract (_, u, abstr) ->
     occurs_u k u || occurs_abstraction occurs_u occurs_v (k+1) abstr

and occurs_assumptions k asmp =
  Assumption.mem_bound k asmp

(****** Alpha equality ******)

let rec alpha_equal e1 e2 =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | TermAtom (x, _), TermAtom (y, _) -> Name.eq_atom x y

    | TermBound i, TermBound j -> i = j

    | TermConstructor (c, args), TermConstructor (c', args') ->
       Name.eq_ident c c' && alpha_equal_args args args'

    | TermConvert (e1, _, _), TermConvert (e2, _, _) ->
       alpha_equal e1 e2

    | (TermAtom _ | TermBound _ | TermConstructor _  | TermConvert _), _ ->
      false
  end

and alpha_equal_ty t1 t2 =
  match t1, t2 with
  | TypeConstructor (c, args), TypeConstructor (c', args') ->
     Name.eq_ident c c' && alpha_equal_args args args'

and alpha_equal_args args args' =
  match args, args' with

  | [], [] -> true

  | (ArgIsTerm e)::args, (ArgIsTerm e')::args' ->
     alpha_equal_abstraction alpha_equal_unit alpha_equal e e' && alpha_equal_args args args'

  | (ArgIsType t)::args, (ArgIsType t')::args' ->
     alpha_equal_abstraction alpha_equal_unit alpha_equal_ty t t' && alpha_equal_args args args'

  | ArgEqType _ :: args, ArgEqType _ :: args' -> alpha_equal_args args args'

  | ArgEqTerm _ :: args, ArgEqTerm _ :: args' -> alpha_equal_args args args'

  | (ArgIsTerm _ | ArgIsType _ | ArgEqType _ | ArgEqTerm _)::_, _::_

  | (_::_), []

  | [], (_::_) ->
     (* we should never get here, because that implies that a constructor
        was applied in two different ways, and somehow the nucleus was happy
        with that *)
     assert false

and alpha_equal_unit () () = true

and alpha_equal_abstraction
  : 'a 'b . ('a -> 'a -> bool) ->
            ('b -> 'b -> bool) ->
            ('a, 'b) abstraction -> ('a, 'b) abstraction -> bool
  = fun equal_u equal_v e e' ->
  e == e' ||
  match e, e' with

  | Abstract (_, u, abstr), Abstract(_, u', abstr') ->
     equal_u u u' &&
     alpha_equal_abstraction equal_u equal_v abstr abstr'

  | NotAbstract v, NotAbstract v' -> equal_v v v'

  | (Abstract _ | NotAbstract _), _ -> false

(****** Printing routines *****)
type print_env =
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ; }

let add_forbidden x penv = { penv with forbidden = x :: penv.forbidden }

(** [print_abstraction occurs_u print_xu occurs_v print_v ?max_level ~penv abstr
   ppf] prints an abstraction using formatter [ppf]. *)
let print_abstraction
   : 'a 'b . (bound -> 'a -> bool) ->
             (penv:print_env -> Name.ident * 'a -> Format.formatter -> unit) ->
             (bound -> 'b -> bool) ->
             (?max_level:Level.t -> penv:print_env -> 'b -> Format.formatter -> unit) ->
             ?max_level:Level.t ->
             penv:print_env ->
             ('a, 'b) abstraction ->
             Format.formatter -> unit
  = fun occurs_u print_xu occurs_v print_v ?max_level ~penv abstr ppf ->
  let rec fold penv xus = function

    | NotAbstract v ->
       let xus = List.rev xus in
       Print.print ?max_level ppf ~at_level:Level.binder "@[<hov 2>%t@ %t@]"
              (Print.sequence (print_xu ~penv) "" xus)
              (print_v ~penv v)

    | Abstract (x, u, abstr) ->
       let x =
         (if occurs_abstraction occurs_u occurs_v 0 abstr then
            Name.refresh penv.forbidden x
          else
            Name.anonymous ())
       in
       let penv = add_forbidden x penv in
       fold penv ((x,u) :: xus) abstr

  in

  fold penv [] abstr

let rec print_term ?max_level ~penv e ppf =
  match e with
  | TermAtom (x, _) ->
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
  | ArgIsTerm abstr -> print_argument_abstraction occurs_term print_term ~penv abstr ppf
  | ArgIsType abstr -> print_argument_abstraction occurs_type print_type ~penv abstr ppf
  | ArgEqType _ -> ()
  | ArgEqTerm _ -> ()

and print_argument_abstraction
  : 'a . (bound -> 'a -> bool) ->
         (?max_level:Level.t -> penv:print_env -> 'a -> Format.formatter -> unit) ->
         penv:print_env -> 'a argument_abstraction -> Format.formatter -> unit
  = fun occurs_v print_v ~penv abstr ppf ->
  print_abstraction
    occurs_unit
    (fun ~penv (x, ()) ppf -> Print.print ppf "%t" (Name.print_ident ~parentheses:true x))
    occurs_v
    print_v
    ~max_level:Level.app_right ~penv abstr ppf

(** Conversion to JSON *)

module Json =
struct

  let rec term e =
    match e with

      | TermAtom (x, t) -> Json.tag "TermAtom" [Name.Json.atom x; ty t]

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

  and abstraction : 'a . ('a -> Json.t) -> Name.ident list -> (unit, 'a) abstraction -> Json.t list =
    fun json_u xs ->
    function
    | Abstract (x, (), abstr) ->
       abstraction json_u (x::xs) abstr
    | NotAbstract u ->
       let xs = List.map Name.Json.ident (List.rev xs) in
       [Json.tuple xs ; json_u u]
end
