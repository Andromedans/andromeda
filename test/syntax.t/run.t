  $ andromeda --prelude prelude.m31 --stdlib stdlib bad_numeral.m31
  File "bad_numeral.m31", line 1, characters 11-29:
  Parsing error: bad numeral 4611686018427387904
  [1]
  $ andromeda --prelude prelude.m31 --stdlib stdlib malformed-unicode.m31
  File "malformed-unicode.m31", line 1, characters 7-7:
  Parsing error: malformed UTF8
  [1]
  $ andromeda --prelude prelude.m31 --stdlib stdlib subscripts.m31
  Rule A is postulated.
  Rule f is postulated.
  - :> judgement = ⊢ {a₀ : A} {a : A} f a₀ a : A
  Rule a is postulated.
  - :> judgement = ⊢ {a₀ : A} {a₁ : A} f a₀ a₁ : A
  Rule a₁ is postulated.
  - :> judgement = ⊢ {a₀ : A} {a₂ : A} f a₀ a₂ : A
  Rule a₂ is postulated.
  Rule a₃ is postulated.
  - :> judgement = ⊢ {a₀ : A} {a₄ : A} f a₀ a₄ : A
  - :> judgement = ⊢ {a₀ : A} {a₄ : A} {a₅ : A} f (f a₀ a₄) a₅ :
    A
  - :> judgement = ⊢ {a₀ : A} {a4 : A} {a₄ : A} f (f a₀ a4) a₄ : A
  Rule a₄ is postulated.
  Rule a₅ is postulated.
  Rule a₆ is postulated.
  Rule a₇ is postulated.
  Rule a₈ is postulated.
  Rule a₉ is postulated.
  - :> judgement = ⊢ {a₀ : A} {a₁₀ : A} f a₀ a₁₀ : A
  Rule a₁₀ is postulated.
  - :> judgement = ⊢ {a₀ : A} {a₁₁ : A} f a₀ a₁₁ : A
  Rule a₁1 is postulated.
  - :> judgement = ⊢ {a₀ : A} {a₁₁ : A} f (f a₁1 a₀) a₁₁ : A
  - :> judgement = ⊢ {a₀ : A} {a₁₁ : A} f (f a₁1 a₀) a₁₁ : A
  Rule a₁₁ is postulated.
  - :> judgement = ⊢ {a₀ : A} {a₁₂ : A} f (f a₁1 a₀) a₁₂ : A
  - :> judgement = ⊢ {a₀ : A} {a₁₂ : A} f (f a₁₂ a₀) a₁₂ : A
  $ andromeda --prelude prelude.m31 --stdlib stdlib unclosed_comment.m31
  File "unclosed_comment.m31", line 1 character 1 - line 2 character 0:
  Parsing error: input ended inside unclosed comment
  [1]
