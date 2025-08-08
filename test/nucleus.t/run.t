  $ andromeda --prelude prelude.m31 --stdlib stdlib abstraction_congruence.m31
  val d :> derivation = derive (A type) (u : A) (v : A) (u ≡ v : A by ξ) ({_
    : A} B type) → B {u} ≡ B {v}
  Rule T is postulated.
  Rule a is postulated.
  Rule b is postulated.
  Rule S is postulated.
  - :> derivation = derive (a ≡ b : T by ζ) → S a a ≡ S b b
  $ andromeda --prelude prelude.m31 --stdlib stdlib alpha_equality.m31
  Rule A is postulated.
  Rule P is postulated.
  Rule a is postulated.
  Rule u is postulated.
  Rule B is postulated.
  Rule ξ is postulated.
  Rule ζ is postulated.
  val a' :> judgement = ⊢ a : B
  val Q :> judgement = ⊢ P a type
  val u' :> judgement = ⊢ u : P a
  $ andromeda --prelude prelude.m31 --stdlib stdlib boundary.m31
  Rule A is postulated.
  Rule B is postulated.
  Rule a is postulated.
  Rule b is postulated.
  - :> boundary = ⊢ ⁇ type
  - :> boundary = ⊢ {_ : A} {_ : A} ⁇ type
  - :> boundary = ⊢ ⁇ : A
  - :> boundary = ⊢ {_ : A} {_ : A} ⁇ : A
  - :> boundary = ⊢ A ≡ B by ⁇
  - :> boundary = ⊢ {_ : A} {_ : A} A ≡ B by ⁇
  - :> boundary = ⊢ a ≡ b : A by ⁇
  - :> boundary = ⊢ {x : A} a ≡ x : A by ⁇
  Rule ξ is postulated.
  - :> judgement = ⊢ a : B
  Rule P is postulated.
  Rule ζ is postulated.
  - :> judgement = ⊢ {z : A} P z ≡ P z
  $ andromeda --prelude prelude.m31 --stdlib stdlib congruence_derive.m31
  Rule reflexivity is postulated.
  Rule symmetry is postulated.
  Rule transitivity is postulated.
  Rule magic is postulated.
  val eq :> derivation = derive (A type) ({_ : A} B type) ({a : A} b₁ : B
    {a}) ({a : A} b₂ : B {a}) ({a : A} b₁ {a} ≡ b₂ {a} : B {a} by ξ)
    (a₁ : A) (a₂ : A) (a₁ ≡ a₂ : A by α) → b₁ {a₁} ≡ b₂
    {a₂} : B {a₁}
  Rule nat is postulated.
  Rule plus is postulated.
  Rule comm is postulated.
  Rule Vec is postulated.
  Rule u is postulated.
  Rule j is postulated.
  Rule k is postulated.
  - :> judgement = ⊢ u nat (plus j k) ≡ u nat (plus k j) : Vec nat (plus j
    k)
  $ andromeda --prelude prelude.m31 --stdlib stdlib congruence_products.m31
  Rule eq_term_refl is postulated.
  Rule eq_type_refl is postulated.
  Rule Π is postulated.
  Rule λ is postulated.
  Rule app is postulated.
  Rule A is postulated.
  Rule a is postulated.
  Rule B is postulated.
  Rule f is postulated.
  Rule g is postulated.
  - :> judgement = ⊢ Π A ({x} B x) ≡ Π A ({x} B x)
  - :> judgement = ⊢ app A ({x} B x) g a ≡ app A ({x} B x) g a : B a
  - :> judgement = ⊢ λ A ({x} B x) ({x} f x) ≡ λ A ({x} B x) ({x} f x) :
    Π A ({x} B x)
  $ andromeda --prelude prelude.m31 --stdlib stdlib congruence_rule.m31
  Rule A is postulated.
  Rule B is postulated.
  Rule b₁ is postulated.
  Rule b₂ is postulated.
  Rule ξ is postulated.
  Rule a₁ is postulated.
  Rule a₂ is postulated.
  Rule α is postulated.
  Rule symmetry is postulated.
  Rule transitivity is postulated.
  val p :> judgement = ⊢ b₁ a₁ ≡ b₂ a₁ : B a₁
  val q :> judgement = ⊢ b₂ a₁ ≡ b₂ a₂ : B a₁
  val r :> judgement = ⊢ B a₂ ≡ B a₁
  val s :> judgement = ⊢ b₁ a₁ ≡ b₂ a₂ : B a₁
  $ andromeda --prelude prelude.m31 --stdlib stdlib congruence.m31
  Rule A is postulated.
  Rule B is postulated.
  Rule Π is postulated.
  Rule a is postulated.
  Rule b is postulated.
  - :> judgement = ⊢ a ≡ a : A
  Rule isPropA is postulated.
  - :> judgement = ⊢ B a a ≡ B a b
  val congrB :> judgement → judgement → judgement = <function>
  - :> judgement = ⊢ Π A ({x} B x x) ≡ Π A ({_} B a a)
  Rule A' is postulated.
  Rule α is postulated.
  Rule α' is postulated.
  val isPropA' :> judgement → judgement → judgement = <function>
  - :> judgement = ⊢ {x' : A'} {y' : A'} x' ≡ y' : A'
  Rule B' is postulated.
  Rule β is postulated.
  - :> judgement = ⊢ Π A ({x} B x x) ≡ Π A' ({y} B' y y)
  $ andromeda --prelude prelude.m31 --stdlib stdlib context.m31
  Rule A is postulated.
  Rule a is postulated.
  Rule f is postulated.
  Rule B is postulated.
  - :> list judgement = []
  val b :> judgement = b₀ : A ⊢ b₀ : A
  - :> list judgement = (b₀ : A ⊢ b₀ : A) :: []
  - :> list judgement = (b₀ : A ⊢ b₀ : A) :: []
  - :> list judgement = (b₀ : A ⊢ b₀ : A) :: []
  val u :> judgement = b₀ : A, u₁ : B a b₀ ⊢ u₁ : B a b₀
  - :> list judgement = (b₀ : A ⊢ b₀ : A) :: (b₀ : A, u₁ : B a
    b₀ ⊢ u₁ : B a b₀) :: []
  $ andromeda --prelude prelude.m31 --stdlib stdlib convert_in_rule.m31
  Rule A is postulated.
  Rule B is postulated.
  Rule ξ is postulated.
  val d :> derivation = derive (x : A) → x : B
  Rule a is postulated.
  - :> judgement * judgement = ((⊢ a : B), (⊢ B type))
  Rule P is postulated.
  Rule e is postulated.
  - :> judgement * judgement = ((⊢ e a : P a), (⊢ B type))
  Rule b is postulated.
  Rule f is postulated.
  - :> judgement * judgement = ((⊢ B type), (⊢ B type))
  - :> judgement = ⊢ B type
  $ andromeda --prelude prelude.m31 --stdlib stdlib convert_nested.m31
  Rule A is postulated.
  Rule B is postulated.
  Rule C is postulated.
  Rule c is postulated.
  Rule ζ is postulated.
  Rule ξ is postulated.
  val test1 :> judgement = ⊢ c : B
  val test2 :> judgement = ⊢ c : B
  $ andromeda --prelude prelude.m31 --stdlib stdlib convert.m31
  Rule A is postulated.
  Rule B is postulated.
  Rule ξ is postulated.
  Rule a is postulated.
  Rule b is postulated.
  - :> judgement = ⊢ a : B
  - :> judgement = ⊢ B type
  Rule P is postulated.
  Rule ζ is postulated.
  - :> judgement = ⊢ P b ≡ P a
  Rule z is postulated.
  val e :> judgement = ⊢ {u : P z} u : P a
  - :> judgement * judgement * judgement * judgement =
    ((u₀ : P z ⊢ u₀ : P z), (⊢ P z type), (u₀ : P z ⊢ u₀ : P a),
     (⊢ P a type))
  $ andromeda --prelude prelude.m31 --stdlib stdlib derive.m31
  Rule A is postulated.
  Rule a is postulated.
  Rule B is postulated.
  Rule s is postulated.
  val d :> derivation = derive (x : A) → B x x type
  - :> judgement = ⊢ B a a type
  - :> judgement = ⊢ {z : A} B z z type
  val d' :> derivation = derive (x : A) → B a x type
  - :> judgement = ⊢ B a a type
  Rule refl is postulated.
  val e :> derivation = derive (x : A) → s x ≡ s x : B x x
  - :> judgement = ⊢ {a₀ : A} s a₀ ≡ s a₀ : B a₀ a₀
  val f :> derivation = derive (a : A) (b : A) → B a b type
  - :> judgement = ⊢ {u : A} {v : A} B u v type
  $ andromeda --prelude prelude.m31 --stdlib stdlib order_of_arguments.m31
  Rule A is postulated.
  Rule B is postulated.
  Rule a is postulated.
  Rule b is postulated.
  Rule P is postulated.
  Rule p is postulated.
  Rule Q is postulated.
  - :> judgement = ⊢ P a b type
  - :> judgement = ⊢ p : P a b
  - :> judgement = ⊢ Q p a b type
  $ andromeda --prelude prelude.m31 --stdlib stdlib premise_with_general_boundary.m31
  Rule prod is postulated.
  Rule Pi is postulated.
  - :> derivation = derive (X type) ({_ : X} Y type) → Pi X ({x₀} Y {x₀})
    type
  Rule Cow is postulated.
  - :> derivation = derive (A type) ({_ : A} B type) (C : prod (Pi A ({x} B
    {x})) A) → Cow A ({x} B {x}) C type
  $ andromeda --prelude prelude.m31 --stdlib stdlib print_assumptions.m31
  val r :> ref (ML.option _α) = ref ML.None
  val j :> judgement = ?A₀ type, {_ : ?A₀} ?B₁ type, {x : ?A₀} {_ :
    ?B₁ {x}} ?f₂ : ?A₀, a₃ : ?A₀, b₄ : ?B₁ {a₃} ⊢ ?f₂
    {a₃} {b₄} : ?A₀
  $ andromeda --prelude prelude.m31 --stdlib stdlib rewrite.m31
  Rule A is postulated.
  Rule B is postulated.
  Rule A' is postulated.
  Rule A_eq_A' is postulated.
  Rule A'_eq_A is postulated.
  Rule a is postulated.
  Rule a' is postulated.
  Rule a_eq_a' is postulated.
  - :> judgement * judgement = ((⊢ B a ≡ B a'), (⊢ B a' type))
  val D :> judgement = {_ : A} ?D₀ type ⊢ {x₀ : A} ?D₀ {x₀} type
  - :> judgement * judgement =
    (({_ : A} ?D₀ type ⊢ ?D₀ {a} ≡ ?D₀ {a'}), ({_ : A}
     ?D₀ type ⊢ ?D₀ {a'} type))
  Rule C is postulated.
  - :> judgement * judgement = ((⊢ C A a ≡ C A' a' : A), (⊢ C A' a' : A))
  val E :> judgement = {_ : A} {_ : A} ?E₁ : A ⊢ {x₀ : A} {x₁ : A}
    ?E₁ {x₀} {x₁} : A
  Rule refl_A is postulated.
  - :> judgement * judgement =
    (({_ : A} {_ : A} ?E₁ : A ⊢ ?E₁ {a} {a'} ≡ ?E₁ {a'} {a'} : A),
     ({_ : A} {_ : A} ?E₁ : A ⊢ ?E₁ {a'} {a'} : A))
  Rule Π is postulated.
  Rule B' is postulated.
  Rule β is postulated.
  - :> judgement * judgement =
    ((⊢ Π A ({x₀} B x₀) ≡ Π A' ({x} B' x)), (⊢ Π A' ({x} B' x)
     type))
  Rule F is postulated.
  val fa :> judgement * judgement =
    ((⊢ F A ({_} a) ≡ F A' ({_} a') : A), (⊢ F A' ({_} a') : A))
  - :> judgement = ⊢ {_ : A'} a' : A
  Rule refl_tm is postulated.
  val der :> derivation = derive (M type) (N type) ({_ : M} {_ : N} op : M) (m
    : M) (m' : M) (m' ≡ m : M by ξ) (n : N) → op {m'} {n} ≡ op {m} {n} :
    M
  $ andromeda --prelude prelude.m31 --stdlib stdlib rule_as_derivation.m31
  Rule bull is postulated.
  - :> judgement = ⊢ bull type
  Rule tail is postulated.
  - :> judgement = ⊢ tail : bull
  Rule eq is postulated.
  - :> judgement = ⊢ tail ≡ tail : bull
  Rule Id is postulated.
  - :> derivation = derive (A type) (a : A) (b : A) → Id A a b type
  Rule Pi is postulated.
  - :> derivation = derive (A type) ({_ : A} B type) → Pi A ({x} B {x}) type
  Rule cow is postulated.
  - :> derivation = derive (A type) (a : A) ({x : A} a ≡ x : A by ξ) → cow
    A a ({x} a ≡ x : A) type
  Rule reflect is postulated.
  - :> derivation = derive (A type) (a : A) (b : A) (p : Id A a b) → a ≡ b
    : A
  $ andromeda --prelude prelude.m31 --stdlib stdlib rules.m31
  Rule A is postulated.
  - :> judgement = ⊢ A type
  Rule a is postulated.
  - :> judgement = ⊢ a : A
  Rule B is postulated.
  - :> derivation = derive (X type) → B X type
  Rule P is postulated.
  - :> derivation = derive (U type) ({_ : U} V type) → P U ({x} V {x}) type
  Rule f is postulated.
  - :> derivation = derive (x : A) (y : B A) → f x y : A
  Rule Ety is postulated.
  - :> derivation = derive (X type) (Y type) → B X ≡ B Y
  Rule ETm is postulated.
  - :> derivation = derive (A type) (x : A) (y : A) (x ≡ y : A by ξ) → y
    ≡ x : A
  Rule C is postulated.
  - :> judgement = ⊢ C type
  Rule D is postulated.
  - :> derivation = derive (a : A) → D a type
  Rule c is postulated.
  - :> derivation = derive (u : A) (v : B A) → c u v : D (f u v)
