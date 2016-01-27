type term = Term of Context.t * Tt.term * Tt.ty

type ty = Ty of Context.t * Tt.ty

let typeof (Term (ctx, _, t)) = Ty (ctx, t)

let term_of_ty (Ty (ctx,Tt.Ty ({Tt.loc=loc;_} as t))) = Term (ctx,t,Tt.mk_type_ty ~loc)

let mk_term ctx e t = Term (ctx, e, t)

let mk_ty ctx t = Ty (ctx, t)

let ty_ty = Ty (Context.empty, Tt.typ)

let print_term ?max_level xs (Term (ctx, e,t)) ppf =
  Print.print ?max_level ~at_level:100 ppf
              "%t@[<hov 2>%s %t@ : %t@]"
              (Context.print ctx)
              (Print.char_vdash ())
              (Tt.print_term ~max_level:999 xs e)
              (Tt.print_ty ~max_level:999 xs t)

let print_ty ?max_level xs (Ty (ctx, t)) ppf =
  Print.print ?max_level ~at_level:0 ppf
              "%t@[<hov 2>%s %t@ type@]"
              (Context.print ctx)
              (Print.char_vdash ())
              (Tt.print_ty ~max_level:999 xs t)
