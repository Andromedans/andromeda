type term = Context.t * Tt.term * Tt.ty

type ty = Context.t * Tt.ty

type equal_ty = Context.t * Tt.ty * Tt.ty

let typeof (ctx, _, t) = (ctx, t)

let mk_term ctx e t = (ctx, e, t)

let mk_ty ctx t = (ctx, t)

let ty_ty = (Context.empty, Tt.typ)

let assume ~loc x (ctx, t) =
  let y, ctx = Context.cone ctx x t in
  mk_term ctx (Tt.mk_atom ~loc y) t

let print_term xs (ctx, e,t) ppf =
  Format.fprintf ppf "%t@[<hov 2>%s %t@\n    : %t@]"
              (Context.print ctx)
              (Print.char_vdash ())
              (Tt.print_term ~max_level:999 xs e)
              (Tt.print_ty ~max_level:999 xs t)

let print_ty xs (ctx, t) ppf =
  Print.print ~at_level:0 ppf "%t@[<hov 2>%s %t@\n    type@]"
              (Context.print ctx)
              (Print.char_vdash ())
              (Tt.print_ty ~max_level:999 xs t)
