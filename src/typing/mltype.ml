type bound_info =
  | BoundVal
  | BoundConst of Name.constant
  | BoundData of Name.data * int
  | BoundOp of Name.operation * int
  | BoundSig of Name.signature
  | BoundDyn of Store.Dyn.key

type ctx = (Name.ident * bound_info) list

