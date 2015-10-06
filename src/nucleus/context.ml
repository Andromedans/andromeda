type t = unit

let empty = ()

let join ctx1 ctx2 = (), []

let abstract1 ctx x = ()

let abstract ctx xs = List.fold_left abstract1 ctx xs
