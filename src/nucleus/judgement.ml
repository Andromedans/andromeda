type term = Tt.term * Tt.ty

type ty = Tt.ty

let mk_term ctx e t = (ctx, e, t)

let mk_ty ctx t = (ctx, t)

let print_term xs (ctx, e,t) ppf =
  Print.print ~at_level:0 ppf "SHOULD PRINT CONTEXT@[<hov 2>%t@\n    : %t@]"
              (Tt.print_term ~max_level:999 xs e)
              (Tt.print_ty ~max_level:999 xs t)

let print_ty xs (ctx, t) ppf =
  Print.print ~at_level:0 ppf "SHOULD PRINT CONEXT @[<hov 2>%t@\n    type@]"
              (Tt.print_ty ~max_level:999 xs t)
