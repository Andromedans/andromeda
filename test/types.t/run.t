  $ andromeda --prelude prelude.m31 --stdlib stdlib abstract_type.m31
  ML type cow declared.
  ML type pretty declared.
  val f :> pretty cow → pretty cow = <function>
  - :> list (pretty cow → pretty cow) = <function> :: <function> :: []
  $ andromeda --prelude prelude.m31 --stdlib stdlib local_let_rec.m31
  $ andromeda --prelude prelude.m31 --stdlib stdlib modules.m31
  ML type cow declared.
  Processing module A
  ML type A.cow declared.
  val x :> A.cow = A.Cow "A.x"
  Processing module B
  ML type B.cow declared.
  val x :> B.cow = B.Cow "A.y"
  val x :> cow = Cow "x"
  val u :> cow * A.cow * B.cow = (Cow "x", A.Cow "A.x", B.Cow "A.y")
  val v :> cow * A.cow * B.cow = (Bull, A.Bull, B.Bull)
  $ andromeda --prelude prelude.m31 --stdlib stdlib typedefs.m31
  ML type test_empty declared.
  ML type test_unit1 declared.
  ML type test_unit2 declared.
  ML type test_unit3 declared.
  ML type fruit declared.
  ML type part declared.
  ML types rodent, insect declared.
