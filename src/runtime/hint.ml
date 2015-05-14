type beta = Pattern.t * Tt.term

type eta = unit

let mk_beta (Tt.Ty t) = Error.impossible "Hint.mk_beta"

let mk_eta (Tt.Ty t) = ()

let match_beta h t = None

let match_eta h e1 e2 t = None
