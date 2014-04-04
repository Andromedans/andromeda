(** Core typing routines. *)

let rec is_type ctx = function

  | Syntax.Universe _ -> ()

  | Syntax.El (alpha, e) -> chk_term ctx (Syntax.Universe alpha)

  | Syntax.Unit -> ()

  | Syntax.Prod (x, t, u) ->
    


and syn_term ctx = function

  (* SYN-VAR *)
  | Syntax.Var x ->
    begin match Context.lookup_var x ctx with
      | None -> Error.typing "Unknown identifier %t" (Print.var ctx x)
      | Some t -> t
    end

  (* SYN-ASCRIBE *)
  | Syntax.Ascribe (e, t) ->
    chk_term ctx e t ; t

  (* SYN-HINT *)
  | Syntax.Hint (e1, e2) ->
    let (u, e3, e4) = syn_id ctx e1 in
    let ctx = Context.hint_extend e3 e4 u ctx in
      syn_term ctx e2

  (* SYN-ABS *)
  | Syntax.Lambda (x, t, e) ->
    let ctx = Context.var_extend x t ctx in
    let u = syn_term ctx e in
      Syntax.Prod (x, t, u)

  (* SYN-APP *)
  | Syntax.App (e1, e2) ->
    let (x, t, u) = syn_prod ctx e1 in
      chk_term ctx e2 t ;
      Syntax.subst x e2 u

  (* SYN-UNIT *)
  | Syntax.UnitTerm -> Syntax.Unit

      
and chk_term ctx e t =
  match e with
  
  (* CHK-HINT *)
  | Syntax.Hint (e1, e2) ->
    let (u, e3, e4) = syn_id ctx e1 in
    let ctx = Context.hint_extend e3 e4 u ctx in
      chk_term ctx e2

  (* CHK-SYN *)
  | e ->
    let u = syn_term ctx e in
      eq_type ctx u t


and eq_type ctx t u =
  failwith "Not implemented"


and eq_term ctx e1 e2 t =
  failwith "Not implemented"
