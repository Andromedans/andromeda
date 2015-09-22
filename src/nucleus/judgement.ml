type term = Tt.term * Tt.ty

type ty = Tt.ty

let mk_term e t = (e, t)

let mk_ty t = t

let print_term xs (e,t) ppf =
  Print.print ~at_level:0 ppf "@[<hov 2>%t@\n    : %t@]"
              (Tt.print_term ~max_level:999 xs e)
              (Tt.print_ty ~max_level:999 xs t)

let print_ty xs t ppf =
  Print.print ~at_level:0 ppf "@[<hov 2>%t@\n    type@]"
              (Tt.print_ty ~max_level:999 xs t)
