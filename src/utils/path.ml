type t =
  | Ident of Ident.t
  | Dot of Ident.t * Name.t

let mk_direct i = Ident i

let mk_module mdl n = Dot (mdl, n)

let equal p q =
  match p, q with
  | Ident x, Ident y -> Ident.equal x y
  | Dot (p1, n1), Dot (p2, n2) -> Ident.equal p1 p2 && Name.equal n1 n2
  | Ident _, Dot _ | Dot _, Ident _ -> false

let print p ppf =
  match p with
  | Ident x -> Ident.print x ppf
  | Dot (mdl, n) -> Format.fprintf ppf "%t.%t" (Ident.print mdl) (Name.print n)
