type beta = Pattern.t * Tt.term

type eta = unit

let mk_beta (Tt.Ty t) = Error.impossible "Hint.mk_beta"

let mk_eta (Tt.Ty t) = ()
