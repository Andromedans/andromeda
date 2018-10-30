(** The datatypes for describing the user-definable rules of type theory. *)

type meta = int  (* meta-variables appearing in rules *)
type bound = TT.bound

type ty =
  | TypeConstructor of Name.constructor * argument list
  | TypeMeta of meta * term list

and term =
  | TermBound of bound
  | TermConstructor of Name.constructor * argument list
  | TermMeta of meta * term list

and eq_type = EqType of assumption * ty * ty

and eq_term = EqTerm of assumption * term * term * ty

and argument =
  | ArgIsType of ty abstraction
  | ArgIsTerm of term abstraction
  | ArgEqType of eq_type abstraction
  | ArgEqTerm of eq_term abstraction

and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.ident * ty * 'a abstraction

and assumption = ()

type premise =
  | PremiseIsType of Name.ident * unit abstraction
  | PremiseIsTerm of Name.ident * ty abstraction
  | PremiseEqType of (ty * ty) abstraction
  | PremiseEqTerm of (term * term * ty) abstraction

type is_type_rule = premise list
type is_term_rule = premise list * ty
type eq_type_rule = premise list * (ty * ty)
type eq_term_rule = premise list * (term * term * ty)

(** Examples of rules that can be formulated using the above.

   The head of the conclusion (the parts in square brackets) is not really
   there because it is fully prescribed by the premises and the judgement
   class; we just specify it here for readability.


      Input:
      ⊢ A type    x:A ⊢ B type
      ————————————————————————
      ⊢ [Π A B] type

      Processed to schema:
      ⊢ A type    {x : MV_ty 0} ⊢ B type
      ——————————————————————————————————
      ⊢ [Π A B] type

      Instance:
      Γ₁ ⊢ A₁ type    Γ₂ | {y:A₂} ⊢ B₁ type
      ————————————————————————————————————— {Γ₁,Γ₂}↑Δ, A₁ =α= A₂
      Δ ⊢ Π A B type


      Input:
      ⊢ A type    x:A ⊢ B type   y:A ⊢ s : B{y}
      —————————————————————————————————————————
      ⊢ [λ A B s] : Π A B

      Processed to schema:
      ⊢ A type    {x : MV_ty 0} ⊢ B type   {y : MV_ty 1} ⊢ s : (MV_ty 0){y}
      —————————————————————————————————————————————————————————————————————
      ⊢ [λ A B s] : Π (MV_ty 2) (MV_ty 1)

      Instance:
      Γ₁ ⊢ A₁ type    Γ₂ | {x:A₂} ⊢ B₁ type   Γ₃ | {y:A₃} ⊢ s : B₂
      ————————————————————————————————————————————————————————————
      check: {Γ₁,Γ₂,Γ₃}↑Δ, A₁ =α= A₂ =α= A₃, B₁ =α= B₂
      Δ ⊢ λ A₁ B₁ s : Π A₁ B₁

      example: [A := nat, B := nat, s := Bound 0]
         gives   [λ nat nat (Bound 0) : Π nat ({0:nat} nat)]


      Input:
      ⊢ A type   ⊢ u : A   ⊢ v : A
      ————————————————————————————
      ⊢ [Id A u v]  type

      Processed to Schema:
      ⊢ A type   ⊢ u : MV 0   ⊢ v : MV 1
      ——————————————————————————————————
      ⊢ [Id A u v]  type

      Instance:
      Γ₁ ⊢ A₁ type   Γ₂ ⊢ u : A₂   Γ₃ ⊢ v : A₃
      ———————————————————————————————————————— {Γ₁, Γ₂, Γ₃} ↑ Δ, Α₁ =α= A₂, A₁ =α= A₃
      Δ ⊢ Id A₁ u v  type


      Input:
      ⊢ A type    ⊢ u : A     x : A, p : Id A u x ⊢ C type
      ⊢ w : C{u, refl A u}    ⊢ v : A     ⊢ p : Id A u v
      ————————————————————————————————————————————————————
      ⊢ [J A u C w v p] : C{v, p}

      Schema:
      ⊢ A type    ⊢ u : MV 0     {x : A, p : Id (MV 1) (MV 0) (Bound 0)} ⊢ C type
      ⊢ w : C{u, refl A u}       ⊢ v : A     ⊢ p : Id A u v
      ————————————————————————————————————————————————————————————————————————————
      ⊢ [J A u C w v p] : C{v, p}

      Instance:
      ⊢ A₁ type    ⊢ u₁ : A₂     x : A₃, h : Id A u x ⊢ C type    ⊢ w : C{u, refl A u}
      ⊢ v : A     ⊢ p : Id A u v
      ————————————————————————————————————————————————————————————————————————————————
      ⊢ [J A u C w v p] : C{v, p}


*)
