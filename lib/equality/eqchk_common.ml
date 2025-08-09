(** Types for pattern matching *)
module Patt =
struct

  type is_type_normal' =
    | TypeConstructor of Ident.t * argument list
    | TypeFreeMeta of Nonce.t * is_term' list

  and is_type' =
    | TypeAddMeta of int
    | TypeNormal of is_type_normal'

  and is_term_normal' =
    | TermConstructor of Ident.t * argument list
    | TermFreeMeta of Nonce.t * is_term' list
    | TermAtom of Nonce.t
    | TermBound of int

  and is_term' =
    | TermAddMeta of int
    | TermNormal of is_term_normal'

  and argument =
    | Arg_Abstract of Name.t * argument
    | Arg_NotAbstract of argument'

  and argument' =
    | ArgumentIsType of is_type'
    | ArgumentIsTerm of is_term'

  (** the exported types also record how many object and equality meta-variables we're capturing. *)
  type is_term = is_term' * int
  type is_type = is_type' * int

end

(** Sets of integers to indicate where the heads are. *)
module IntSet = Set.Make(struct
                          type t = int
                          let compare = Stdlib.compare
                        end)

(** Maps of atoms to deal with bound variables *)
let cmp_atom atm1 atm2 =
   Nonce.compare (Nucleus.atom_nonce atm1) (Nucleus.atom_nonce atm2)

module BoundMap =
  Map.Make
    (struct
      type t = Nucleus.is_atom
      let compare = cmp_atom
    end)

(** We index rules by the heads of expressions, which can be identifiers or meta-variables (nonces). *)
type symbol =
  | Ident of Ident.t
  | Nonce of Nonce.t

(** Reporting Equality Checker errors. *)
type invalid_rule =
  | WrongMetavariable of int * int
  | BoundMetavariableExpected of int * (Nucleus_types.is_term)
  | TermBoundaryExpected of Nucleus_types.boundary
  | TermBoundaryExpectedGotAbstraction of Nucleus_types.boundary_abstraction
  | TermBoundaryNotGiven
  | EquationLHSnotCorrect of Nucleus.eq_term * int
  | EquationRHSnotCorrect of Nucleus.eq_term * int
  | TypeOfEquationMismatch of Nucleus.eq_term * Nucleus_types.is_type * Nucleus_types.is_type
  | ObjectPremiseAfterEqualityPremise of Nucleus_types.meta
  | ObjectPremiseExpected of Nucleus_types.meta
  | EqualityPremiseExpected of Nucleus_types.meta
  | DerivationWrongForm of (Nucleus.derivation)
  | ObjectBoundaryExpected of Nucleus_types.boundary_abstraction
  | TypeEqualityConclusionExpected
  | TermEqualityConclusionExpected

type equality_fail =
  | NoCongruenceTypes of Nucleus.is_type * Nucleus.is_type
  | NoCongruenceTerms of Nucleus.is_term * Nucleus.is_term

type form_fail =
  | NewTypeMetaCheckingMode of int
  | NewTermMetaCheckingMode of int
  | MetaBoundTypeInPatt of int
  | MetaBoundTermInPatt of int
  | EqualityTypeArgumentInPatt of Nucleus_types.eq_type
  | EqualityTermArgumentInPatt of Nucleus_types.eq_term
  | CaptureMetasNotCorrectType of Nucleus_types.is_type
  | CaptureMetasNotCorrectTerm of Nucleus_types.is_term
  | NonLinearPattern of int
  | AbstractionInPattern of Nucleus_types.argument

type normalization_error =
  | EqualityTypeArguement of Nucleus.eq_type
  | EqualityTermArguement of Nucleus.eq_term
  | EqualityArgument of Nucleus.judgement_abstraction

type eqchk_error =
  | Invalid_rule of invalid_rule
  | Equality_fail of equality_fail
  | Form_fail of form_fail
  | Normalization_fail of normalization_error

exception EqchkError of eqchk_error

exception Fatal_error of string

let print_eqchk_error ~penv err ppf =
  match err with
  | Invalid_rule e ->
    begin
    match e with
    | WrongMetavariable (k,j) ->
      Format.fprintf ppf "expected a bound metavaribale %d, but got %d" k j
    | BoundMetavariableExpected (k, e) ->
      Format.fprintf ppf "expected a bound metavariable %d, but got %t"
      k (Nucleus_print.thesis_is_term ~penv e)
    | TermBoundaryExpected b ->
      Format.fprintf ppf "expected a term boundary, but got %t"
      (Nucleus_print.thesis_boundary ~penv ~print_head:(Nucleus_print.print_qqmark) b)
    | TermBoundaryExpectedGotAbstraction abstr ->
      Format.fprintf ppf "expected a term boundary, but got %t"
      (Nucleus_print.boundary_abstraction ~penv abstr)
    | TermBoundaryNotGiven ->
      Format.fprintf ppf "expected a term boundary, but got None"
    | EquationLHSnotCorrect (eq, k) ->
      Format.fprintf ppf "LHS of equation %t not a correct metavariable %d"
      Nucleus_print.(thesis_eq_term ~penv (Nucleus.expose_eq_term eq))
      k
    | EquationRHSnotCorrect (eq, k) ->
      Format.fprintf ppf "RHS of equation %t not a correct metavariable %d"
      Nucleus_print.(thesis_eq_term ~penv (Nucleus.expose_eq_term eq))
      k
    | TypeOfEquationMismatch (eq, t1, t2) ->
      Format.fprintf ppf
      "Type at equation %t should be equal to both types of metavariabels %t and %t"
      Nucleus_print.(thesis_eq_term ~penv (Nucleus.expose_eq_term eq))
      Nucleus_print.(thesis_is_type ~penv t1)
      Nucleus_print.(thesis_is_type ~penv t2)
    | ObjectPremiseAfterEqualityPremise p ->
      Format.fprintf ppf "Object premise %t appears after equality premise"
      Nucleus_print.(premise ~penv p)
    | ObjectPremiseExpected p ->
      Format.fprintf ppf "Equality premise %t appears where object premise expected"
      Nucleus_print.(premise ~penv p)
    | EqualityPremiseExpected p ->
      Format.fprintf ppf "Object premise %t appears where equality premise expected"
      Nucleus_print.(premise ~penv p)
    | DerivationWrongForm _drv ->
      Format.fprintf ppf "Derivation not in a required form"
    | ObjectBoundaryExpected (bdry) ->
      Format.fprintf ppf
      "Premise %t of a computation rule does not have an object boundary"
      Nucleus_print.(boundary_abstraction ~penv bdry)
    | TypeEqualityConclusionExpected ->
      Format.fprintf ppf "Conclusion not a type equality boundary"
    | TermEqualityConclusionExpected ->
      Format.fprintf ppf "Conclusion not a term equality boundary"
    end

  | Equality_fail (NoCongruenceTypes (ty1, ty2)) ->
    Format.fprintf ppf "Cannot find a congruence rule for types %t and %t"
    Nucleus_print.(thesis_is_type ~penv (Nucleus.expose_is_type ty1))
    Nucleus_print.(thesis_is_type ~penv (Nucleus.expose_is_type ty2))

  | Equality_fail (NoCongruenceTerms (e1, e2)) ->
    Format.fprintf ppf "Cannot find a congruence rule for terms %t and %t"
    Nucleus_print.(thesis_is_term ~penv (Nucleus.expose_is_term e1))
    Nucleus_print.(thesis_is_term ~penv (Nucleus.expose_is_term e2))

  | Form_fail er ->
    begin
      match er with
      | NewTypeMetaCheckingMode i ->
        Format.fprintf ppf
        "Cannot introduce a new type metavariable with index %d in checking mode" i
      | NewTermMetaCheckingMode i ->
        Format.fprintf ppf
        "Cannot introduce a new term metavariable with index %d in checking mode" i
      | MetaBoundTypeInPatt i ->
        Format.fprintf ppf
        "Cannot make a pattern from a bound type metavariable with index %d" i
      | MetaBoundTermInPatt i ->
        Format.fprintf ppf
        "Cannot make a pattern from a bound term metavariable with index %d" i
      | EqualityTypeArgumentInPatt eqty ->
        Format.fprintf ppf
        "Cannot form a pattern out of a type equality argument %t"
        Nucleus_print.(thesis_eq_type ~penv eqty)
      | EqualityTermArgumentInPatt eqtm ->
        Format.fprintf ppf
        "Cannot form a pattern out of a term equality argument %t"
        Nucleus_print.(thesis_eq_term ~penv eqtm)
      | CaptureMetasNotCorrectType ty ->
        Format.fprintf ppf
        "Pattern type %t does not capture correct metavariables"
        Nucleus_print.(thesis_is_type ~penv ty)
      | CaptureMetasNotCorrectTerm e ->
        Format.fprintf ppf
        "Pattern term %t does not capture correct metavariables"
        Nucleus_print.(thesis_is_term ~penv e)
      |  NonLinearPattern i ->
        Format.fprintf ppf
        "Pattern is not linear at metavariable with index %d" i
      | AbstractionInPattern abstr ->
        Format.fprintf ppf
        "Cannot form a pattern out an abstracted argument %t"
        Nucleus_print.(argument ~penv abstr)
    end

  | Normalization_fail er ->
    begin
      match er with
      | EqualityTypeArguement eqty ->
        Format.fprintf ppf
        "Cannot normalize type equality argument %t"
        Nucleus_print.(thesis_eq_type ~penv (Nucleus.expose_eq_type eqty))
      | EqualityTermArguement eqtm ->
        Format.fprintf ppf
        "Cannot normalize term equality argument %t"
        Nucleus_print.(thesis_eq_term ~penv (Nucleus.expose_eq_term eqtm))
      | EqualityArgument jdg_abstr ->
        Format.fprintf ppf
        "Cannot normalize equality argument %t"
        Nucleus_print.(judgement_abstraction ~penv (Nucleus.expose_judgement_abstraction jdg_abstr))
    end


(** A tag to indicate that a term or a type is normalized *)
type 'a normal = Normal of 'a

let print_symbol ~penv sym ppf =
  match sym with
  | Ident x -> Ident.print ~opens:penv.Nucleus.opens ~parentheses:false x ppf
  | Nonce n -> Nonce.print ~questionmark:false ~parentheses:false n ppf

let compare_symbol x y =
  match x, y with
  | Ident _, Nonce _ -> -1
  | Ident i, Ident j -> Ident.compare i j
  | Nonce n, Nonce m -> Nonce.compare n m
  | Nonce _, Ident _ -> 1

module SymbolMap = Map.Make(
                   struct
                     type t = symbol
                     let compare = compare_symbol
                   end)

(** Is an exposed premise an object premise? *)
let rec is_object_premise = function
  | Nucleus_types.(NotAbstract (BoundaryIsType _ | BoundaryIsTerm _)) -> true
  | Nucleus_types.(NotAbstract (BoundaryEqType _ | BoundaryEqTerm _)) -> false
  | Nucleus_types.Abstract (_, _, prem) -> is_object_premise prem

(** The head symbol of an exposed term. *)
let head_symbol_term e =
  let rec fold = function
    | Nucleus_types.TermBoundVar _ -> assert false
    | Nucleus_types.(TermAtom {atom_nonce=n; _}) -> Nonce n
    | Nucleus_types.TermConstructor (c, _) -> Ident c
    | Nucleus_types.(TermMeta (MetaFree {meta_nonce;_}, _)) -> Nonce meta_nonce
    | Nucleus_types.(TermMeta (MetaBound _, _)) -> raise (Fatal_error ("head symbol of a bound term metavariable does not exist"))
    | Nucleus_types.TermConvert (e, _, _) -> fold e
  in
  fold e


(** The head symbol of an exposed type. *)
let head_symbol_type = function
  | Nucleus_types.TypeConstructor (c, _) -> Ident c
  | Nucleus_types.(TypeMeta (MetaFree {meta_nonce=n;_}, _)) -> Nonce n
  | Nucleus_types.(TypeMeta (MetaBound _, _)) -> raise (Fatal_error ("head symbol of a bound type metavariable does not exist"))

(** Apply rap to a list of arguments *)
let rap_apply rap args =
  let rec fold rap args =
  match rap, args with
  | rap, [] -> rap
  | Nucleus.RapMore (_bdry, f), arg :: args -> fold (f arg) args
  | Nucleus.RapDone _, _::_ -> raise (Fatal_error ("Applying the rule to too many arguments"))
  in
  try
    fold rap args
  with
  | Nucleus.Error _err -> raise (Fatal_error ("Nucleus error"))

(** Apply rap to a list of arguments, return the judgement *)
let rap_fully_apply rap args =
  let rec fold rap args =
  match rap, args with
  | Nucleus.RapDone jdg, [] -> jdg
  | Nucleus.RapMore (_bdry, f), arg :: args ->
    ();
    let tmp = f (arg) in
    fold tmp args
  | Nucleus.RapDone _, _::_ -> raise (Fatal_error ("Applying the rule to too many arguments"))
  | Nucleus.RapMore _, [] -> raise (Fatal_error ("Applying the rule to too few arguments"))
  in
  try
    Some (fold rap args)
  with
  | Nucleus.Error _ -> None

(** Automagically compute the heads of a pattern *)

let arg_is_head abstr =
  let rec fold = function
    | Patt.Arg_Abstract (_, abstr) -> fold abstr
    | Patt.Arg_NotAbstract jdg ->
      begin
      match jdg with
        | Patt.(ArgumentIsType (TypeAddMeta _ )) -> false
        | Patt.(ArgumentIsType (TypeNormal _)) -> true
        | Patt.(ArgumentIsTerm (TermAddMeta _ )) -> false
        | Patt.(ArgumentIsTerm (TermNormal _)) -> true
      end
  in fold abstr

let term_is_head = function
  | Patt.TermAddMeta _ -> false
  | Patt.TermNormal _ -> true

let heads_args args =
  let rec fold hs i = function
    | [] -> hs
    | arg :: args ->
       if arg_is_head arg then
         fold (IntSet.add i hs) (i+1) args
       else
         fold hs (i+1) args
  in
  fold IntSet.empty 0 args

let heads_terms es =
  let rec fold hs i = function
    | [] -> hs
    | e :: es ->
       if term_is_head e then
         fold (IntSet.add i hs) (i+1) es
       else
         fold hs (i+1) es
  in
  fold IntSet.empty 0 es

let heads_term_normal = function
  | Patt.TermAtom _ -> IntSet.empty

  | Patt.TermConstructor (_, args) -> heads_args args

  | Patt.TermFreeMeta (_, es) -> heads_terms es

  | Patt.TermBound _v -> IntSet.empty

let heads_term = function
  | Patt.TermAddMeta _ -> IntSet.empty
  | Patt.TermNormal patt -> heads_term_normal patt

let heads_type_normal = function
  | Patt.TypeConstructor (_, args) -> heads_args args
  | Patt.TypeFreeMeta (_, es) -> heads_terms es

let heads_type = function
  | Patt.TypeAddMeta _ -> IntSet.empty
  | Patt.TypeNormal patt -> heads_type_normal patt
