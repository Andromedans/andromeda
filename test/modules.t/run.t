  $ andromeda module_include.m31
  Processing module A
  val x :> ref mlstring = ref "A.x"
  Processing module B
  - :> mlstring = "A.x"
  - :> mlstring = "A.x"
  - :> mlunit = ()
  - :> mlstring = "B.x"
  - :> mlstring = "B.x"
  $ andromeda module_open_not_exported.m31
  File "module_open_not_exported.m31", line 11, characters 1-3:
  Type error: unknown name B.x
  [1]
  $ andromeda module_open_print.m31
  Processing module A
  Rule A.X is postulated.
  ML type A.cow declared.
  - :> judgement = ⊢ A.X type
  - :> A.cow = A.Cow
  - :> judgement = ⊢ X type
  - :> A.cow = Cow
  $ andromeda module_open.m31
  Processing module A
  val x :> mlstring = "A.x"
  Processing module B
  val y :> mlstring = "A.x"
