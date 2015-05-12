type beta_hint = unit

type eta_hint = unit

let mk_beta (Tt.Ty t) = ()

let mk_eta (Tt.Ty t) = ()

let match_beta h t = None

let match_eta h e1 e2 t = None
