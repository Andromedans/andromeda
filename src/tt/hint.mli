(* Beta hints are iterated products around an equality between a spine (the
   redex) and a term (the reduct). *)

type beta = Pattern.t * Tt.term'
type eta = unit
