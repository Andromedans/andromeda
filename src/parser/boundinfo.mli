type scoping =
  | Lexical
  | Dynamic

type t =
  | BoundVal of scoping
  | BoundConst of Name.constant
  | BoundData of Name.data * int
  | BoundOp of Name.operation * int
  | BoundSig of Name.signature

type ctx = (Name.ident * t) list
