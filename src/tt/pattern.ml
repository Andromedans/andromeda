(** Pattern matching support for hints. *)

let occurs_abstraction occurs_u occurs_v test lvl (xus, v) =
  let rec fold lvl = function
    | [] -> occurs_v test lvl v
    | (_,u) :: xus -> occurs_u test lvl u || fold (lvl+1) xus
  in
    fold lvl xus

(* Does a bound variable satisfying [test] occur in an expression? *)
let rec occurs test lvl (e',_) =
  match e' with
  | Tt.Type -> false
  | Tt.Name _ -> false
  | Tt.Bound m -> (m >= lvl) && test (m - lvl)
  | Tt.Lambda a -> occurs_abstraction occurs_ty occurs_term_ty test lvl a
  | Tt.Spine (e, a) ->
    occurs test lvl e ||
    occurs_abstraction occurs_term_ty occurs_ty test lvl a
  | Tt.Prod a ->
    occurs_abstraction occurs_ty occurs_ty test lvl a
  | Tt.Eq (t, e1, e2) ->
    occurs_ty test lvl t || occurs test lvl e1 || occurs test lvl e2
  | Tt.Refl (t, e) ->
    occurs_ty test lvl t || occurs test lvl e

and occurs_ty test lvl (Tt.Ty t) = occurs test lvl t

and occurs_term_ty test lvl (e, t) =
  occurs test lvl e || occurs_ty test lvl t


(** Indicate that a pattern match failed. *)
exception NoMatch

let comb_abstraction comb_u comb_v lvl solution us v =
  let rec fold lvl solution = function
    | [] -> comb_v lvl solution v
    | (_,u)::us ->
      let solution = comb_u lvl solution u in
        fold (lvl+1) solution us
  in
  fold lvl solution us

(** [comb lvl solution pe e] matches pattern [pe] against expression [e], using bound variables
  as pattern variables to match against. Arguments:

    - [lvl] is the shift level for de Bruijn indices, i.e., in how many binders we are at the moment.
      Thus we're actually matching against indices larger than or equal to [lvl], and when matching
      against [k], on the outside this is known as index [k - lvl].

    - [solution] is the solution build to far; a mapping from de Bruijn indices to expressions

    Note that we can have several matches for one bound variable, i.e., there is no assumption of
    linearity. It is the responsibility of the caller to worry about completeness and consistency
    of the solution found.

   The function returns the match found, or raises [NoMatch] if there is a mismatch. *)
let rec comb lvl solution pe e =
  match pe, e with

  | Tt.Type, Tt.Type -> solution

  | Tt.Name x, Tt.Name y ->
    if Name.eq x y then solution else raise NoMatch

  | Tt.Bound k, e ->
    if k >= lvl then
    begin
      (* Must check that [e] does not contain bound variables below [lvl]. *)
      (* XXX should we actually shift [e] as it's leaving level [lvl]? *)
      (* XXX what if [e] contains bound variables above [lvl]? *)
      if occurs (fun i => i < lvl) 0 e
      then raise NoMatch
      else (k - lvl, e) :: solution
    end
    else begin
      match e with
      | Tt.Bound m -> if k = m then solution else raise NoMatch
      | _ -> raise NoMatch
    end

  | Tt.Lambda (xpts, pe), Tt.Lambda (xts, e) ->
    comb_abstraction comb_ty comb lvl solution xpts pe xts e

  | Tt.Spine (pe, pets), Tt.Spine (e, ets)  ->
    let solution = comb lvl solution pe e in
      comb_abstraction comb_ty comb_term_ty lvl solution pe pets e ets

  | Tt.Prod (xpts, pt), Tt.Prod (xts, t) ->
    comb_abstraction comb_ty comb_ty lvl solution xpts pt xts t

  | Tt.Eq (pt, p1, p2), Tt.Eq (t, e1, e2) ->
    let solution = comb_ty lvl solution pt t in
    let solution = comb lvl solution p1 e2 in
    let solution = comb lvl solution p2 e2 in
      solution

  | Tt.Refl (pt, pe), Tt.Refl (t, e) ->
    let solution = comb_ty lvl solution pt t in
    let solution = comb lvl solution pe e in
      solution

  | (Tt.Type | Tt.Refl _ | Tt.Bound _ | Tt.Lambda _ |
     Tt.Spine _ | Tt.Prod _ | Tt.Eq _ | Tt.Refl _), _ ->
    raise NoMatch


and comb_ty lvl solution (Tt.Ty pt) (Tt.Ty t) =
  comb lvl solution pt t

and comb_term_ty lvl solution (pe, pt) (e, t) =
  let solution = comb lvl solution pe e in
  let solution = comb_ty lvl solution pt t in
    solution

(** The exported versions of functions. *)

let combine p e = comb 0 [] p e

let combine_ty pt t = comb_ty 0 [] pt t


