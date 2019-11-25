(** Type-directed equality checking based on user-provided rules. *)

(** We support user-provided beta-rules and extensionality-rules (these are
  inter-derivable with η-rules, but have a more convenient form)

  A term extensionality rule has the form

      rule R P₁ ... Pᵢ (x : A) (y : A) Q₁ ... Qⱼ x ≡ y : A

  where:

  - the premises P₁ ... Pᵢ are type and term premises

  - the premises Q₁ ... Qⱼ are term equation premises

  - the head meta-variables of the premises P₁ ... Pᵢ appear in A,
    uninstantiated, so that the premises P₁ ... Pᵢ can be read off A.

  For example, the extensionality rule for functions is

      rule Π_ext (A type) ({x:A} B type) (f : Π A B) (g : Π A B)
                 ({x : A} app A B f x ≡ app A B g x as ξ)
                 f ≡ g : Π A B

  For example, the extensionality rule for the unit type is

      rule unit_ext (x : unit) (y : unit) x ≡ y : unit

  For example, the extensionality rule for dependent sums is

      rule Σ_ext (A type) ({x:A} B type) (p : Σ A B) (q : Σ A B)
                 (π₁ A B p ≡ π₁ A B q : A as ξ₁)
                 (π₂ A B p ≡ π₂ A B q : B{π₁ A B p} as ξ₂) p ≡ q
                 : Σ A B

  A term β-rule has the form

      rule R P₁ ... Pᵢ e₁ ≡ e₂ : A

  where:

  - the head meta-variable of each premise appears in e₁, uninstantiated
    (actually fully η-expanded), so that the premises can be read off e₁

  - e1 is an application of a symbol or a meta-variable (not a variable)

  For example, the β-rule for functions is:

     rule Π_β (A type) ({x:A} B type) (a : A) ({x:A} e : B{x})
              : app A B (λ A B e) a ≡ e{a} : B{a}

  For example, the β-rule for projections are:

     rule Σ_β₁ (A type) ({x : A} B type) (a : A) (b : B{a})
              : π₁ A B (pair A B a b) == a : A

  A type β-rule has the form

     rule R P₁ ... Pᵢ  A ≡ B

  where:

  - the premises P₁ ... Pᵢ are term and type premises (no equations)

  - the head meta-variable of each premise appears in A, uninstantiated, so that
    the premises can be read off e₁
*)

(** Types describing patterns that we can match against. These are simple and do not
    bother matching anything under an abstraction. *)

(** The type of beta rules. *)
type beta_rule

(** The type of extensionality rules. *)
type ext_rule

(** We index rules by the heads of expressions, which canb be
    identifiers or meta-variables (nonces). *)
type symbol =
  | Ident of Ident.t
  | Nonce of Nonce.t

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

type checker = {
   beta : beta_rule list SymbolMap.t ;
   ext : ext_rule list SymbolMap.t
  }

exception Invalid_rule

let empty_checker = {
    beta = SymbolMap.empty ;
    ext = SymbolMap.empty
  }

let add_beta checker drv =
  let sym, bt = make_beta_rule drv in
  { checker with beta = SymbolMap.add sym bt checker.beta }

let add_extensionality checker drv =
  let sym, bt = make_ext_rule drv in
  { checker with ext = SymbolMap.add sym bt checker.ext }

(** Datatypes witnessing that a type or a term is in weak head-normal form. *)

type whnf_type =
  |


let rec check_eqtype
