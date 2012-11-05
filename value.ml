type variable = Syntax.variable

type universe = int

type value =
  | VNeutral of neutral
  | VUniverse of universe
  | VPi of vabstraction
  | VLambda of vabstraction

and neutral =
  | VVar of variable
  | VApp of neutral * value

and vabstraction = value * variable * (value -> value)
