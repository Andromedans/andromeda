# A generic equality checker

We support user-provided β-rules and extensionality-rules (these are inter-derivable with η-rules, but have a more convenient form).

### Extensionality rules

A term extensionality rule has the form

    derive R P₁ ... Pᵢ A (x : A) (y : A) Q₁ ... Qⱼ -> x ≡ y : A

where:

* the premises `P₁ ... Pᵢ` are type and term premises
* the premises `Q₁ ... Qⱼ` are equation premises
* the head meta-variables of the premises `P₁ ... Pᵢ` appear in `A` (fully η-expanded), so that the premises `P₁ ... Pᵢ` can be read off `A`.

For example, the extensionality rule for functions is

    derive (A type) ({x:A} B type)
           (f : Π A B) (g : Π A B)
           ({x : A} app A B f x ≡ app A B g x as ξ)
           ->
           f ≡ g : Π A B

For example, the extensionality rule for the unit type is

    derive (x : unit) (y : unit) -> x ≡ y : unit

For example, the extensionality rule for dependent sums is

    derive (A type) ({x:A} B type)
           (p : Σ A B) (q : Σ A B)
           (π₁ A B p ≡ π₁ A B q : A as ξ₁)
           (π₂ A B p ≡ π₂ A B q : B{π₁ A B p} as ξ₂)
           ->
           p ≡ q : Σ A B


### Computation rules

A term β-rule has the form

    derive R P₁ ... Pᵢ -> e₁ ≡ e₂ : A

where:

* the head meta-variable of each premise appears in `e₁` (fully η-expanded), so that the premises can be read off `e₁`
* `e₁` is not a bound variable

For example, the β-rule for functions is:

    derive (A type) ({x:A} B type) (a : A) ({x:A} e : B{x})
            ->
            app A B (λ A B e) a ≡ e{a} : B{a}

For example, the β-rule for projections are:

    derive (A type) ({x : A} B type) (a : A) (b : B{a})
           ->
           π₁ A B (pair A B a b) == a : A

A type β-rule has the form

    derive R P₁ ... Pᵢ -> A ≡ B

where:

* the premises `P₁ ... Pᵢ` are term and type premises (no equations)
* the head meta-variable of each premise appears in `A`, uninstantiated, so that
  the premises can be read off `A`

