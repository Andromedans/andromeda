(** Type-directed equality checker. *)

(** A term extensionality rule has the form

    rule R P₁ ... Pᵢ (x : A) (y : A) Q₁ ... Qⱼ  x ≡ y : A

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

       rule unit_ext (x : unit) (y : unit)  x ≡ y : unit

    For example, the extensionality rule for dependent sums is

       rule Σ_ext (A type) ({x:A} B type) (p : Σ A B) (q : Σ A B)
               (π₁ A B p ≡ π₁ A B q : A as ξ₁) (π₂ A B p ≡ π₂ A B q : B{π₁ A B p} as ξ₂)
               p ≡ q : Σ A B
*)
