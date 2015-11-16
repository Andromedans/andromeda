type term = Context.t * Tt.term * Tt.ty

type ty = Context.t * Tt.ty

type equal_ty = Context.t * Tt.ty * Tt.ty

let typeof (ctx, _, t) = (ctx, t)

let mk_term ctx e t = (ctx, e, t)

let mk_ty ctx t = (ctx, t)

let ty_ty = (Context.empty, Tt.typ)

let print_term ?max_level xs (ctx, e,t) ppf =
  Print.print ?max_level ~at_level:100 ppf
              "%t@[<hov 2>%s %t@ : %t@]"
              (Context.print ctx)
              (Print.char_vdash ())
              (Tt.print_term ~max_level:999 xs e)
              (Tt.print_ty ~max_level:999 xs t)

let print_ty ?max_level xs (ctx, t) ppf =
  Print.print ?max_level ~at_level:0 ppf
              "%t@[<hov 2>%s %t@ type@]"
              (Context.print ctx)
              (Print.char_vdash ())
              (Tt.print_ty ~max_level:999 xs t)
