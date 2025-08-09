  $ andromeda eqchk_exceptions.m31
  Processing module eq
  ML type eq.checker declared.
  external empty_checker : eq.checker = "Eqchk.empty_checker"
  external add_type_computation : eq.checker → derivation →
    eq.checker = "Eqchk.add_type_computation"
  external add_term_computation : eq.checker → derivation →
    eq.checker = "Eqchk.add_term_computation"
  external add : eq.checker → derivation → eq.checker = "Eqchk.add"
  external normalize_type : ML.bool → eq.checker → judgement →
    judgement * judgement = "Eqchk.normalize_type"
  external normalize_term : ML.bool → eq.checker → judgement →
    judgement * judgement = "Eqchk.normalize_term"
  external add_extensionality : eq.checker → derivation →
    eq.checker = "Eqchk.add_extensionality"
  external prove_eqtype_abstraction : eq.checker → boundary →
    judgement = "Eqchk.prove_eq_type_abstraction"
  external prove_eqterm_abstraction : eq.checker → boundary →
    judgement = "Eqchk.prove_eq_term_abstraction"
  val ch :> ref eq.checker = ref <checker>
  val add_rule :> derivation → mlunit = <function>
  Exception eq.Coerce_fail is declared.
  Exception eq.Not_equality_boundary is declared.
  Exception eq.Not_object_judgement is declared.
  val equalize_type :> judgement → judgement → judgement = <function>
  val coerce_abstraction :> judgement → boundary → judgement = <function>
  val normalize :> judgement → judgement * judgement = <function>
  val compute :> judgement → judgement * judgement = <function>
  val prove :> boundary → judgement = <function>
  val add_locally :> mlforall α, derivation → (mlunit → α) → α =
    <function>
  Rule U is postulated.
  "passed test non-object boundaries"
  val jdg1 :> judgement = ⊢ U type
  Rule U' is postulated.
  Rule x_eq_y_U is postulated.
  "passed test extensionality LHS"
  val nothing1 :> mlunit = ()
  Rule x_eq_y_U1 is postulated.
  "passed test extensionality RHS"
  val nothing2 :> mlunit = ()
  Rule x_eq_y_U2 is postulated.
  File "eqchk_exceptions.m31", line 36 character 5 - line 41 character 7:
  Runtime error: uncaught exception ML.EqualityCheckerException
    "LHS of equation [3] ≡ [2] :
  U not a correct metavariable 1"
  [1]
  $ andromeda equality-checker.m31
  Processing module eq
  ML type eq.checker declared.
  external empty_checker : eq.checker = "Eqchk.empty_checker"
  external add_type_computation : eq.checker → derivation →
    eq.checker = "Eqchk.add_type_computation"
  external add_term_computation : eq.checker → derivation →
    eq.checker = "Eqchk.add_term_computation"
  external add : eq.checker → derivation → eq.checker = "Eqchk.add"
  external normalize_type : ML.bool → eq.checker → judgement →
    judgement * judgement = "Eqchk.normalize_type"
  external normalize_term : ML.bool → eq.checker → judgement →
    judgement * judgement = "Eqchk.normalize_term"
  external add_extensionality : eq.checker → derivation →
    eq.checker = "Eqchk.add_extensionality"
  external prove_eqtype_abstraction : eq.checker → boundary →
    judgement = "Eqchk.prove_eq_type_abstraction"
  external prove_eqterm_abstraction : eq.checker → boundary →
    judgement = "Eqchk.prove_eq_term_abstraction"
  val ch :> ref eq.checker = ref <checker>
  val add_rule :> derivation → mlunit = <function>
  Exception eq.Coerce_fail is declared.
  Exception eq.Not_equality_boundary is declared.
  Exception eq.Not_object_judgement is declared.
  val equalize_type :> judgement → judgement → judgement = <function>
  val coerce_abstraction :> judgement → boundary → judgement = <function>
  val normalize :> judgement → judgement * judgement = <function>
  val compute :> judgement → judgement * judgement = <function>
  val prove :> boundary → judgement = <function>
  val add_locally :> mlforall α, derivation → (mlunit → α) → α =
    <function>
  Rule unit is postulated.
  Rule tt is postulated.
  Rule unit_ext is postulated.
  Extensionality rule for unit: derive (x : unit) (y : unit) → x ≡ y :
  unit
  - :> mlunit = ()
  Rule × is postulated.
  Rule pair is postulated.
  Rule fst is postulated.
  Rule snd is postulated.
  Rule sym_ty is postulated.
  Rule β_fst is postulated.
  Rule β_snd is postulated.
  Rule prod_ext is postulated.
  Term computation rule for fst (heads at [2]):
    derive (A type) (A' type) (B type) (B' type) (A' ≡ A by ξ) (B' ≡
    B by ζ) (x : A') (y : B') → fst A B (pair A' B' x y) ≡ x : A
  
  - :> mlunit = ()
  Term computation rule for snd (heads at [2]):
    derive (A type) (A' type) (B type) (B' type) (A' ≡ A by ξ) (B' ≡
    B by ζ) (x : A') (y : B') → snd A B (pair A' B' x y) ≡ y : B
  
  - :> mlunit = ()
  Extensionality rule for ×: derive (A type) (B type) (u : ( × ) A B) (v :
  ( × ) A B) (fst A B u ≡ fst A B v : A by ξ) (snd A B u ≡ snd A B v :
  B by ζ) → u ≡ v : ( × ) A
  B
  - :> mlunit = ()
  Rule U is postulated.
  Rule V is postulated.
  Rule p is postulated.
  Rule u is postulated.
  Rule v is postulated.
  - :> judgement * judgement =
    ((⊢ fst U V (pair U V u v) ≡ u : U), (⊢ u : U))
  - :> judgement * judgement =
    ((⊢ snd U V (pair U V u v) ≡ v : V), (⊢ v : V))
  - :> judgement = ⊢ p ≡ pair U V (fst U V p) (snd U V p) : ( × ) U V
  Rule P is postulated.
  Rule P_eq_prodUV is postulated.
  Type computation rule for P (heads at []):
    derive → P ≡ ( × ) U V
  - :> mlunit = ()
  Rule p' is postulated.
  - :> judgement = ⊢ p' ≡ pair U V (fst U V p') (snd U V p') : P
  Rule unuseful is postulated.
  Type computation rule for × (heads at []):
    derive (A type) (B type) → ( × ) A B ≡ U
  - :> judgement * judgement = ((⊢ ( × ) U V ≡ U), (⊢ U type))
  - :> judgement * judgement =
    ((⊢ ( × ) U V ≡ ( × ) U V), (⊢ ( × ) U V type))
  Rule ℕ is postulated.
  Rule z is postulated.
  Rule s is postulated.
  Rule ℕ_ind is postulated.
  Rule ℕ_β_z is postulated.
  Rule ℕ_β_s is postulated.
  Term computation rule for ℕ_ind (heads at [3]):
    derive ({_ : ℕ} C type) (base : C {z}) ({n : ℕ} {_ : C {n}} step : C {s
    n}) (k : ℕ) → ℕ_ind ({x} C {x}) base ({c_n n} step {n} {c_n}) (s k)
    ≡ step {k} {ℕ_ind ({x} C {x}) base ({c_n n} step {n} {c_n}) k} : C {s
    k}
  
  - :> mlunit = ()
  Term computation rule for ℕ_ind (heads at [3]):
    derive ({_ : ℕ} C type) (base : C {z}) ({n : ℕ} {_ : C {n}} step : C {s
    n}) → ℕ_ind ({x} C {x}) base ({c_n n} step {n} {c_n}) z ≡ base : C
    {z}
  
  - :> mlunit = ()
  val plus :> derivation = derive (n : ℕ) (m : ℕ) → ℕ_ind ({_} ℕ) n
    ({c_n _} s c_n) m : ℕ
  val foo :> judgement = ⊢ ℕ_ind ({_} ℕ) z ({c_n _} s c_n) (s z) : ℕ
  - :> judgement * judgement =
    ((⊢ ℕ_ind ({_} ℕ) z ({c_n _} s c_n) (s z) ≡ s (ℕ_ind ({_} ℕ) z
     ({c_n _} s c_n) z) : ℕ), (⊢ s (ℕ_ind ({_} ℕ) z ({c_n _} s c_n) z)
     : ℕ))
  - :> judgement * judgement =
    ((⊢ ℕ_ind ({_} ℕ) z ({c_n _} s c_n) (s z) ≡ s z : ℕ), (⊢ s z :
     ℕ))
  - :> judgement * judgement =
    ((⊢ ℕ_ind ({_} ℕ) z ({_ c_n} s c_n) z ≡ z : ℕ), (⊢ z : ℕ))
  - :> judgement * judgement =
    ((⊢ s (ℕ_ind ({_} ℕ) z ({_ c_n} s c_n) z) ≡ s (ℕ_ind ({_} ℕ) z
     ({_ c_n} s c_n) z) : ℕ), (⊢ s (ℕ_ind ({_} ℕ) z ({_ c_n} s c_n) z)
     : ℕ))
  - :> judgement = ⊢ ℕ_ind ({_} ℕ) (s z) ({c_n _} s c_n) (s z) ≡ s (s
    z) : ℕ
  Type computation rule for B₀ (heads at [0]):
    derive → ?B₀ {?a₁} ≡ ?A₂
  Rule weird is postulated.
  Term computation rule for op₃ (heads at [1]):
    derive (y : ?A₄) → ?op₃ {y} {?e₅} ≡ y : ?A₄
  
  Term computation rule for e'₆ (heads at []):
    derive → ?e'₆ ≡ ?e₅ : ?B₇
  
  val d :> derivation = derive (A type) (B type) ({_ : A} {_ : B} op : A) (e :
    B) ({a : A} op {a} {e} ≡ a : A by ξ) (e' : B) (e' ≡ e : B by η) (x :
    A) → op {x} {e'} ≡ x : A
  $ andromeda normalization_boundaries.m31
  Processing module eq
  ML type eq.checker declared.
  external empty_checker : eq.checker = "Eqchk.empty_checker"
  external add_type_computation : eq.checker → derivation →
    eq.checker = "Eqchk.add_type_computation"
  external add_term_computation : eq.checker → derivation →
    eq.checker = "Eqchk.add_term_computation"
  external add : eq.checker → derivation → eq.checker = "Eqchk.add"
  external normalize_type : ML.bool → eq.checker → judgement →
    judgement * judgement = "Eqchk.normalize_type"
  external normalize_term : ML.bool → eq.checker → judgement →
    judgement * judgement = "Eqchk.normalize_term"
  external add_extensionality : eq.checker → derivation →
    eq.checker = "Eqchk.add_extensionality"
  external prove_eqtype_abstraction : eq.checker → boundary →
    judgement = "Eqchk.prove_eq_type_abstraction"
  external prove_eqterm_abstraction : eq.checker → boundary →
    judgement = "Eqchk.prove_eq_term_abstraction"
  val ch :> ref eq.checker = ref <checker>
  val add_rule :> derivation → mlunit = <function>
  Exception eq.Coerce_fail is declared.
  Exception eq.Not_equality_boundary is declared.
  Exception eq.Not_object_judgement is declared.
  val equalize_type :> judgement → judgement → judgement = <function>
  val coerce_abstraction :> judgement → boundary → judgement = <function>
  val normalize :> judgement → judgement * judgement = <function>
  val compute :> judgement → judgement * judgement = <function>
  val prove :> boundary → judgement = <function>
  val add_locally :> mlforall α, derivation → (mlunit → α) → α =
    <function>
  Rule A is postulated.
  Rule A' is postulated.
  Rule A_eq_A' is postulated.
  Type computation rule for A (heads at []):
    derive → A ≡ A'
  - :> mlunit = ()
  Rule B is postulated.
  Rule Π is postulated.
  Rule C is postulated.
  Rule D is postulated.
  Rule S is postulated.
  val s :> judgement = ⊢ {x : A} {y : B x} S x y ({z} D A x y z) type
  Rule a is postulated.
  Rule b is postulated.
  - :> judgement * judgement =
    ((⊢ S a b ({z} D A a b z) ≡ S a b ({z} D A' a b z)), (⊢ S a b ({z} D
     A' a b z) type))
  Rule B' is postulated.
  Rule B_eq_B' is postulated.
  Type computation rule for B (heads at []):
    derive (x : A) → B x ≡ B' x
  - :> mlunit = ()
  - :> judgement * judgement =
    ((⊢ Π A ({x₀} B x₀) ≡ Π A' ({x₀} B' x₀)), (⊢ Π A' ({x₀}
     B' x₀) type))
  - :> judgement * judgement =
    ((⊢ S a b ({z} D A a b z) ≡ S a b ({z} D A' a b z)), (⊢ S a b ({z} D
     A' a b z) type))
  - :> judgement * judgement =
    ((⊢ S a b ({z} D (B a) a b z) ≡ S a b ({z} D (B' a) a b z)), (⊢ S a b
     ({z} D (B' a) a b z) type))
  Rule T is postulated.
  val t :> judgement = ⊢ T A ({x} B x) a b (S a b ({z} D A a b z)) type
  - :> judgement * judgement =
    ((⊢ T A ({x} B x) a b (S a b ({z} D A a b z)) ≡ T A' ({x} B' x) a b (S
     a b ({z} D A' a b z))), (⊢ T A' ({x} B' x) a b (S a b ({z} D A' a b z))
     type))
  Rule Prod3 is postulated.
  Rule × is postulated.
  Rule ϕ is postulated.
  Rule p is postulated.
  val φ :> judgement = ⊢ ϕ A p type
  - :> judgement * judgement = ((⊢ ϕ A p ≡ ϕ A' p), (⊢ ϕ A' p type))
  Rule ψ is postulated.
  Rule u is postulated.
  val ϑ :> judgement = ⊢ ψ A ({x} u x) type
  - :> judgement * judgement =
    ((⊢ ψ A ({x} u x) ≡ ψ A' ({x} u x)), (⊢ ψ A' ({x} u x) type))
  val M1 :> judgement = ?M₀ type ⊢ ?M₀ type
  Rule experiment is postulated.
  Type computation rule for M₀ (heads at []):
    derive → ?M₀ ≡ A
  - :> mlunit = ()
  Rule triple is postulated.
  Rule fst is postulated.
  Rule snd is postulated.
  val δ :> judgement = ?M₀ type ⊢ ψ ?M₀ ({p₀} triple ?M₀ A A' (fst
    ?M₀ A p₀) (snd ?M₀ A p₀) (snd ?M₀ A p₀)) type
  - :> judgement * judgement =
    ((?M₀ type ⊢ ψ ?M₀ ({p₀} triple ?M₀ A A' (fst ?M₀ A p₀) (snd
     ?M₀ A p₀) (snd ?M₀ A p₀)) ≡ ψ A' ({p₀} triple A' A' A' (fst
     A' A' p₀) (snd A' A' p₀) (snd A' A' p₀))), (?M₀ type ⊢ ψ A'
     ({p₀} triple A' A' A' (fst A' A' p₀) (snd A' A' p₀) (snd A' A'
     p₀)) type))
  $ andromeda strong.m31
  Processing module eq
  ML type eq.checker declared.
  external empty_checker : eq.checker = "Eqchk.empty_checker"
  external add_type_computation : eq.checker → derivation →
    eq.checker = "Eqchk.add_type_computation"
  external add_term_computation : eq.checker → derivation →
    eq.checker = "Eqchk.add_term_computation"
  external add : eq.checker → derivation → eq.checker = "Eqchk.add"
  external normalize_type : ML.bool → eq.checker → judgement →
    judgement * judgement = "Eqchk.normalize_type"
  external normalize_term : ML.bool → eq.checker → judgement →
    judgement * judgement = "Eqchk.normalize_term"
  external add_extensionality : eq.checker → derivation →
    eq.checker = "Eqchk.add_extensionality"
  external prove_eqtype_abstraction : eq.checker → boundary →
    judgement = "Eqchk.prove_eq_type_abstraction"
  external prove_eqterm_abstraction : eq.checker → boundary →
    judgement = "Eqchk.prove_eq_term_abstraction"
  val ch :> ref eq.checker = ref <checker>
  val add_rule :> derivation → mlunit = <function>
  Exception eq.Coerce_fail is declared.
  Exception eq.Not_equality_boundary is declared.
  Exception eq.Not_object_judgement is declared.
  val equalize_type :> judgement → judgement → judgement = <function>
  val coerce_abstraction :> judgement → boundary → judgement = <function>
  val normalize :> judgement → judgement * judgement = <function>
  val compute :> judgement → judgement * judgement = <function>
  val prove :> boundary → judgement = <function>
  val add_locally :> mlforall α, derivation → (mlunit → α) → α =
    <function>
  Rule N is postulated.
  Rule z is postulated.
  Rule s is postulated.
  Rule plus is postulated.
  Rule plus_z is postulated.
  Rule plus_s is postulated.
  Rule times is postulated.
  Rule times_z is postulated.
  Rule times_s is postulated.
  Term computation rule for plus (heads at [1]):
    derive (m : N) → plus m z ≡ m : N
  
  - :> mlunit = ()
  Term computation rule for plus (heads at [1]):
    derive (m : N) (n : N) → plus m (s n) ≡ s (plus m n) : N
  
  - :> mlunit = ()
  Term computation rule for times (heads at [1]):
    derive (m : N) → times m z ≡ z : N
  
  - :> mlunit = ()
  Term computation rule for times (heads at [1]):
    derive (m : N) (n : N) → times m (s n) ≡ plus (times m n) m : N
  
  - :> mlunit = ()
  val one :> judgement = ⊢ s z : N
  val two :> judgement = ⊢ s (s z) : N
  val three :> judgement = ⊢ s (s (s z)) : N
  val four :> judgement = ⊢ s (s (s (s z))) : N
  val five :> judgement = ⊢ plus (s (s z)) (s (s (s z))) : N
  val six :> judgement = ⊢ plus (s (s (s z))) (s (s (s z))) : N
  - :> judgement = ⊢ plus (s (s (s z))) (s (s (s z))) ≡ plus (s (s z)) (s
    (s (s (s z)))) : N
  - :> judgement * judgement =
    ((⊢ plus (s z) (s z) ≡ s (plus (s z) z) : N), (⊢ s (plus (s z) z) :
     N))
  - :> judgement * judgement =
    ((⊢ plus (s (s (s z))) (s (s (s z))) ≡ s (plus (s (s (s z))) (s (s z)))
     : N), (⊢ s (plus (s (s (s z))) (s (s z))) : N))
  - :> judgement * judgement =
    ((⊢ plus (s (s (s z))) (s (s (s z))) ≡ s (s (s (s (s (s z))))) : N),
     (⊢ s (s (s (s (s (s z))))) : N))
  - :> judgement * judgement =
    ((⊢ plus (plus (s (s z)) (s (s (s z)))) (plus (s (s (s z))) (s (s (s
     z)))) ≡ s (plus (plus (s (s z)) (s (s (s z)))) (plus (s (s (s z))) (s (s
     z)))) : N), (⊢ s (plus (plus (s (s z)) (s (s (s z)))) (plus (s (s (s
     z))) (s (s z)))) : N))
  - :> judgement = ⊢ plus (plus (s (s z)) (s (s (s z)))) (plus (s (s (s z)))
    (s (s (s z)))) ≡ s (s (s (s (s (s (s (s (s (s (s z)))))))))) : N
  - :> judgement * judgement =
    ((⊢ plus (plus (s (s z)) (s (s (s z)))) (plus (s (s (s z))) (s (s (s
     z)))) ≡ s (s (s (s (s (s (s (s (s (s (s z)))))))))) : N), (⊢ s (s (s
     (s (s (s (s (s (s (s (s z)))))))))) : N))
  - :> judgement * judgement =
    ((⊢ times (s (s z)) (times (plus (s (s (s z))) (s (s (s z)))) (plus (s (s
     (s z))) (s (s (s z))))) ≡ s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s
     (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s
     (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s
     (s (s (s (s (s (s
     z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :
     N), (⊢ s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s
     (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s
     (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s
     z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :
     N))
  - :> judgement = ⊢ times (plus (s (s z)) (s (s (s z)))) (plus (s (s (s z)))
    (s (s (s z)))) ≡ plus (plus (s (s z)) (s (s (s z)))) (times (plus (s (s
    z)) (s (s (s z)))) (plus (s (s z)) (s (s (s z))))) : N
