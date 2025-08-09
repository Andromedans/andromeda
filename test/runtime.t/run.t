  $ andromeda abstract_atoms.m31
  Rule A is postulated.
  - :> judgement = ⊢ {x : A} x : A
  - :> boundary = ⊢ {_ : A} ⁇ : A
  val abstr_jdg :> judgement = ⊢ {z : A} z : A
  val a :> judgement = z₀ : A ⊢ z₀ : A
  val abstr1 :> judgement = ⊢ {z : A} z : A
  val abstr_bdry :> boundary = ⊢ {_ : A} {_ : A} ⁇ : A
  val atom :> judgement = x₁ : A ⊢ x₁ : A
  val bdry :> boundary = ⊢ {_ : A} ⁇ : A
  val abstr2 :> boundary = ⊢ {_ : A} {_ : A} ⁇ : A
  $ andromeda compare.m31
  Processing module C
  external compare : mlforall α, α → α → ML.order = "compare"
  - :> ML.order = ML.less
  - :> ML.order = ML.less
  - :> ML.order = ML.greater
  - :> ML.order = ML.less
  - :> ML.order = ML.greater
  - :> ML.order = ML.greater
  - :> mlstring = "a"
  - :> mlstring = "b"
  - :> mlstring = "c"
  $ andromeda derivation.m31
  val cow :> mlforall α β, (α → β) → α → β = <function>
  val chicken :> derivation → judgement → judgement → judgement =
    <function>
  Rule A is postulated.
  Rule a is postulated.
  Rule B is postulated.
  Rule s is postulated.
  val d :> derivation = derive (x : A) (y : A) → s x x y : B x x y
  - :> judgement = ⊢ s a a a : B a a a
  val e :> derivation = derive ({_ : A} {_ : A} T type) (a : A) → T {a} {a}
    type
  - :> judgement → judgement → judgement = <function>
  - :> judgement = ⊢ B a a a type
  - :> judgement = ⊢ B a a a type
  $ andromeda equation_by.m31
  Rule A is postulated.
  Rule a is postulated.
  - :> judgement = ⊢ A ≡ A
  - :> judgement = ⊢ a ≡ a : A
  - :> derivation = derive ({_ : A} f : A) (x : A) (y : A) (x ≡ y : A by ξ)
    → f {x} ≡ f {y} : A
  $ andromeda exception.m31
  Exception Cow is declared.
  Exception Horn is declared.
  Exception Tail is declared.
  val f :> exn → exn = <function>
  - :> exn = Cow "horn"
  - :> exn = Cow "horn"
  - :> exn = Cow "tail"
  - :> mlstring * mlstring = ("foo", "bar")
  - :> mlstring * mlstring = ("horn", "")
  - :> mlstring * mlstring = ("tail", "")
  - :> mlstring = "horn"
  $ andromeda fresh.m31
  Rule A is postulated.
  Rule B is postulated.
  val a :> judgement = a₀ : A ⊢ a₀ : A
  val b :> judgement = x₁ : A ⊢ x₁ : A
  val c :> judgement = a₀ : A, x₁ : A, b₂ : B a₀ x₁ ⊢ b₂ : B a₀
    x₁
  val d :> judgement = x₁ : A, α₃ : A, x₄ : B x₁ α₃ ⊢ x₄ : B
    x₁ α₃
  val e :> judgement = ( ++₅ ) : A ⊢ ( ++₅ ) : A
  $ andromeda fun_pattern.m31
  val f :> mlforall α β γ, α * β → γ → β * α = <function>
  val g :> list mlstring → mlunit = <function>
  - :> _α → ML.bool * mlstring = <function>
  - :> ML.bool * mlstring = (ML.false, "foo")
  - :> mlunit = ()
  val h :> _β * _γ → _δ → _δ * _β * _γ
  - :> list _ε * mlstring * ML.bool = ([], "foo", ML.false)
  $ andromeda handler_exception.m31
  Exception Cow is declared.
  Operation moo is declared.
  - :> mlstring * mlstring = ("correct", "moo")
  $ andromeda handler.m31
  Operation auto is declared.
  Rule A is postulated.
  Rule a is postulated.
  Rule B is postulated.
  - :> judgement = ⊢ a : A
  - :> judgement = ⊢ B type
  $ andromeda holes.m31
  File "holes.m31", line 1, characters 1-25:
  Type error: ( ? ) is already declared as an operation
  [1]
  $ andromeda list_pattern.m31
  val x :> mlstring = "x"
  val y :> mlstring = "y"
  val z :> mlstring = "z"
  val x' :> mlstring = "x"
  val y' :> mlstring = "y"
  val z' :> mlstring = "z"
  val x'' :> mlstring = "x"
  val y'' :> mlstring = "y"
  val z'' :> mlstring = "z"
  val lst'' :> list mlstring = []
  val x''' :> mlstring = "x"
  val lst''' :> list mlstring = "y" :: "z" :: []
  $ andromeda nullary_rule.m31
  Rule A is postulated.
  Rule a is postulated.
  val d :> derivation = derive → A type
  - :> derivation = derive → A type
  - :> judgement = ⊢ A type
  Rule B is postulated.
  - :> derivation = derive (x : A) (y : A) → B x y type
  - :> derivation = derive → B a a type
  - :> judgement = ⊢ B a a type
  $ andromeda parallel_let.m31
  val cow :> mlstring * mlstring = ("y", "x")
  val x :> mlstring = "x"
  val y :> mlstring = "y"
  val a :> mlstring = "a"
  val b :> mlstring = "b"
  val c :> mlstring = "c"
  val y' :> mlstring = "y"
  val a' :> mlstring = "a"
  val c' :> mlstring = "c"
  val x'' :> mlstring = "x"
  val a'' :> mlstring = "a"
  val b'' :> mlstring = "b"
  val c'' :> mlstring = "c"
  $ andromeda patterns.m31
  - :> mlstring = "bar"
  - :> mlstring = "foo"
  - :> mlstring * mlstring * mlstring = ("baz", "foo", "bar")
  - :> mlstring = "right"
  - :> mlstring * mlstring * mlstring = ("baz", "foo", "bar")
  - :> list mlstring * mlstring * mlstring * list mlstring * mlstring =
    ("foo" :: "bar" :: [], "baz", "foo", "bar" :: [], "baz")
  - :> mlstring = "foo"
  Rule A is postulated.
  Rule a is postulated.
  Rule P is postulated.
  val test_judgement :> judgement → list judgement * mlstring = <function>
  - :> list judgement * mlstring =
    ((⊢ a : A) :: (⊢ A type) :: [], "isterm")
  - :> list judgement * mlstring = ((⊢ A type) :: [], "istype")
  - :> list judgement * mlstring = ((⊢ P a type) :: [], "istype")
  Rule B is postulated.
  Rule ξ is postulated.
  - :> list judgement * mlstring =
    ((⊢ A type) :: (⊢ B type) :: [], "eqtype")
  Rule b is postulated.
  Rule ζ is postulated.
  - :> list judgement * mlstring =
    ((⊢ a : A) :: (⊢ b : A) :: (⊢ A type) :: [], "eqterm")
  - :> list judgement * mlstring =
    ((⊢ a : B) :: (⊢ b : B) :: (⊢ B type) :: [], "eqterm")
  - :> list judgement * mlstring =
    ((⊢ a : B) :: (⊢ B type) :: [], "isterm")
  - :> list judgement * mlstring =
    ((z₀ : A ⊢ z₀ : A) :: (⊢ A type) :: (z₀ : A ⊢ P z₀ type) ::
     [], "abstraction")
  val test_boundary :> boundary → list judgement * list boundary * mlstring =
    <function>
  - :> list judgement * list boundary * mlstring = ([], [], "istype boundary")
  - :> list judgement * list boundary * mlstring =
    ((⊢ A type) :: [], [], "isterm boundary")
  - :> list judgement * list boundary * mlstring =
    ((⊢ P a type) :: [], [], "isterm boundary")
  - :> list judgement * list boundary * mlstring =
    ((⊢ A type) :: (⊢ P a type) :: [], (⊢ A ≡ P a by ⁇) :: [],
     "eqtype boundary")
  - :> list judgement * list boundary * mlstring =
    ((⊢ a : A) :: (⊢ b : A) :: (⊢ A type) :: [], [], "eqterm boundary")
  - :> list judgement * list boundary * mlstring =
    ((⊢ a : B) :: (⊢ b : B) :: (⊢ B type) :: [], [], "eqterm boundary")
  - :> list judgement * list boundary * mlstring =
    ((z₁ : A ⊢ z₁ : A) :: (⊢ A type) :: [], (z₁ : A ⊢ ⁇ : P z₁)
     :: [], "abstraction boundary")
  Rule θ is postulated.
  - :> list judgement * list boundary * mlstring =
    ((z₂ : B ⊢ z₂ : B) :: (⊢ B type) :: [], (z₂ : B ⊢ ⁇ : P z₂)
     :: [], "abstraction boundary")
  $ andromeda top_handler.m31
  Operation auto is declared.
  Rule A is postulated.
  Rule a is postulated.
  Rule B is postulated.
  Rule b is postulated.
  Rule prod is postulated.
  Rule pair is postulated.
  Exception Auto_cannot_infer is declared.
  - :> judgement = ⊢ a : A
  - :> judgement = ⊢ pair A B a b : prod A B
  - :> judgement = ⊢ pair (prod A B) A (pair A B a b) a : prod (prod A B) A
  File "top_handler.m31", line 25, characters 1-4:
  Runtime error: uncaught exception Auto_cannot_infer
  [1]
  $ andromeda when_guard.m31
  - :> mlstring = "a"
  - :> mlstring = "yes"
  - :> mlstring = "no"
