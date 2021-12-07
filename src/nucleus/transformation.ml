open Nucleus_types

exception Not_transformation
exception Not_specified

module MetaMap =
  Map.Make
    (struct
      type t = meta
      let compare =
        fun { meta_nonce=nonce1 ; _ } {meta_nonce = nonce2 ; _} -> Nonce.compare nonce1 nonce2
    end)

module AtomMap =
  Map.Make
    (struct
      type t = is_atom
      let compare =
        fun { atom_nonce=nonce1 ; _ } {atom_nonce = nonce2 ; _} -> Nonce.compare nonce1 nonce2
    end)

let empty : derivation Ident.map = Ident.empty

let rec check_eq_bdry_arities bdry_abstr1 bdry_abstr2 =
  match bdry_abstr1, bdry_abstr2 with
    | Abstract _, NotAbstract _
    | NotAbstract _, Abstract _ -> false
    | Abstract (_, _, bdry1), Abstract (_, _, bdry2) -> check_eq_bdry_arities bdry1 bdry2
    | NotAbstract bdry1, NotAbstract bdry2 ->
      begin
      match bdry1, bdry2 with
      | BoundaryIsType _, BoundaryIsType _
      | BoundaryIsTerm _, BoundaryIsTerm _
      | BoundaryEqType _, BoundaryEqType _
      | BoundaryEqTerm _, BoundaryEqTerm _ -> true
      | BoundaryIsType _, BoundaryIsTerm _
      | BoundaryIsType _, BoundaryEqType _
      | BoundaryIsType _, BoundaryEqTerm _
      | BoundaryIsTerm _, BoundaryIsType _
      | BoundaryIsTerm _, BoundaryEqType _
      | BoundaryIsTerm _, BoundaryEqTerm _
      | BoundaryEqType _, BoundaryIsType _
      | BoundaryEqType _, BoundaryIsTerm _
      | BoundaryEqType _, BoundaryEqTerm _
      | BoundaryEqTerm _, BoundaryIsType _
      | BoundaryEqTerm _, BoundaryIsTerm _
      | BoundaryEqTerm _, BoundaryEqType _ -> false
      end

let add_rule sgn c der (transf : derivation Ident.map) =
  (* Check that the constructor is not already specified*)
  assert (not (Ident.mem c sgn)) ;
  (* Check that the arities of boundaries in the rule for c match the arities the premises of derivation der *)
  let rule = Signature.lookup_rule c sgn in
  (* recursively check both rules *)
  let rec fold r d =
    match r, d with
    | Premise _, Conclusion _
    | Conclusion _, Premise _ -> false
    | Premise (pr, r'), Premise (pd, d') ->
      begin
        match pr, pd with
        | {meta_boundary = bdryr;_}, {meta_boundary = bdryd;_} ->
          if check_eq_bdry_arities bdryr bdryd
          then fold r' d'
          else false
      end
    | Conclusion bdryr, Conclusion jdgd ->
      begin
        match bdryr, jdgd with
        | BoundaryIsType _, JudgementIsType _
        | BoundaryIsTerm _, JudgementIsTerm _
        | BoundaryEqType _, JudgementEqType _
        | BoundaryEqTerm _, JudgementEqTerm _ -> true
        | BoundaryIsType _, JudgementIsTerm _
        | BoundaryIsType _, JudgementEqType _
        | BoundaryIsType _, JudgementEqTerm _
        | BoundaryIsTerm _, JudgementIsType _
        | BoundaryIsTerm _, JudgementEqType _
        | BoundaryIsTerm _, JudgementEqTerm _
        | BoundaryEqType _, JudgementIsType _
        | BoundaryEqType _, JudgementIsTerm _
        | BoundaryEqType _, JudgementEqTerm _
        | BoundaryEqTerm _, JudgementIsType _
        | BoundaryEqTerm _, JudgementIsTerm _
        | BoundaryEqTerm _, JudgementEqType _ -> false
      end
  in
  if fold rule der then Ident.add c der transf else raise Not_transformation

let rec act_judgement_abstraction sgn (transf : derivation Ident.map) jdg_abstr =
  let _metas, _atoms, jdg_abstr' = act_judgement_abstraction' sgn transf MetaMap.empty AtomMap.empty jdg_abstr in
  jdg_abstr'

and act_boundary_abstraction sgn (transf : derivation Ident.map) bdry_abstr =
  let _metas, _atoms, bdry_abstr' =  act_boundary_abstraction' sgn transf MetaMap.empty AtomMap.empty bdry_abstr in
  bdry_abstr'

and act_judgement_abstraction' sgn transf metas atoms = function
  | NotAbstract jdg ->
    let metas', atoms', jdg' = act_judgement sgn transf metas atoms jdg in
    metas', atoms', NotAbstract jdg'
  | Abstract (x, t, j_abstr) ->
    let metas1, atoms1, t' = act_is_type sgn transf metas atoms t in
    let metas2, atoms2, j_abstr' = act_judgement_abstraction' sgn transf metas1 atoms1 j_abstr in
    metas2, atoms2, Abstract (x, t', j_abstr')

and act_boundary_abstraction' sgn transf metas atoms = function
  | NotAbstract bdry ->
    let metas', atoms', bdry' = act_boundary sgn transf metas atoms bdry in
    metas', atoms', NotAbstract bdry'
  | Abstract (x, t, b_abstr) ->
    let metas1, atoms1, t' = act_is_type sgn transf metas atoms t in
    let metas2, atoms2, b_abstr' = act_boundary_abstraction' sgn transf metas1 atoms1 b_abstr in
    metas2, atoms2, Abstract (x, t', b_abstr')

and act_judgement sgn transf metas atoms = function
  | JudgementIsType t ->
    let metas', atoms', t' = act_is_type sgn transf metas atoms t in
    metas', atoms', JudgementIsType t'
  | JudgementIsTerm e ->
    let metas', atoms', e' = act_is_term sgn transf metas atoms e in
    metas', atoms', JudgementIsTerm e'
  | JudgementEqType eq ->
    let metas', atoms', eq' = act_eq_type sgn transf metas atoms eq in
    metas', atoms', JudgementEqType eq'
  | JudgementEqTerm eq ->
    let metas', atoms', eq' = act_eq_term sgn transf metas atoms eq in
    metas', atoms', JudgementEqTerm eq'

and act_boundary sgn transf metas atoms = function
  | BoundaryIsType () -> metas, atoms, BoundaryIsType ()
  | BoundaryIsTerm t ->
    let metas', atoms', t' = act_is_type sgn transf metas atoms t in
    metas', atoms', BoundaryIsTerm t'
  | BoundaryEqType (t1, t2) ->
    let metas1, atoms1, t1' = act_is_type sgn transf metas atoms t1 in
    let metas2, atoms2, t2' = act_is_type sgn transf metas1 atoms1 t2 in
    metas2, atoms2, BoundaryEqType(t1', t2')
  | BoundaryEqTerm (e1, e2, t) ->
    let metas1, atoms1, e1' = act_is_term sgn transf metas atoms e1 in
    let metas2, atoms2, e2' = act_is_term sgn transf metas1 atoms1 e2 in
    let metas3, atoms3, t' = act_is_type sgn transf metas2 atoms2 t in
    metas3, atoms3, BoundaryEqTerm(e1', e2', t')

and act_is_type sgn transf metas atoms = function
  | TypeMeta (m, es) ->
    let metas', atoms', meta = act_meta_any sgn transf metas atoms m in
    let metas'', atoms'', es' = act_is_terms sgn transf metas' atoms' [] es in
    metas'', atoms'', TypeMeta (meta, es')
  | TypeConstructor (c, args) ->
    let rule = Ident.find_opt c transf in
    begin
      match rule with
      | None -> raise Not_specified
      | Some rl ->
        (* let rl_rap = Form.form_derivation_rap sgn rl in
        let metas', atoms', args' = act_arguments sgn transf metas atoms args in
        let rec fold *)
        failwith "todo"
    end

and act_is_term sgn transf metas atoms = function
  | TermBoundVar k -> metas, atoms, TermBoundVar k
  | TermAtom a ->
      let metas', atoms', a' = act_atom sgn transf metas atoms a in
      metas', atoms', TermAtom a
  | TermMeta (m, es) ->
    let metas', atoms', meta = act_meta_any sgn transf metas atoms m in
    let metas'', atoms'', es' = act_is_terms sgn transf metas' atoms' [] es in
    metas'', atoms'', TermMeta (meta, es')
  | TermConstructor (c, args) -> failwith "todo"
  | TermConvert (e, asm, t) ->
    let metas1, atoms1, e' = act_is_term sgn transf metas atoms e in
    let metas2, atoms2, asm' = act_assumption sgn transf metas1 atoms1 asm in
    let metas3, atoms3, t' = act_is_type sgn transf metas2 atoms2 t in
    metas3, atoms3, TermConvert (e', asm', t')

and act_is_terms sgn transf metas atoms acc = function
  | [] -> metas, atoms, List.rev acc
  | e :: es ->
      let metas', atoms', e' = act_is_term sgn transf metas atoms e in
      act_is_terms sgn transf metas' atoms' (e' :: acc) es


(* We need to keep track of which metavariables are mappped to which translations *)
and act_meta_any sgn transf metas atoms = function
  | MetaBound k -> metas, atoms, MetaBound k
  | MetaFree m ->
    let metas', atoms', m' = act_meta sgn transf metas atoms m in
      metas', atoms', MetaFree m'

and act_meta sgn transf metas atoms = function
  | {meta_nonce; meta_boundary} as m ->
    begin
      match MetaMap.find_opt m metas with
      | None ->
        let metas', atoms', bdry' = act_boundary_abstraction' sgn transf metas atoms meta_boundary in
        let m' = Mk.free_meta (Nonce.name meta_nonce) bdry' in
        (MetaMap.add m m' metas'), atoms', m'
      | Some meta -> metas, atoms, meta
    end

(* We need to keep track of which atoms are mappped to which translations *)
and act_atom sgn transf metas atoms = function
  | {atom_nonce; atom_type} as atom ->
    begin
      match AtomMap.find_opt atom atoms with
      | None ->
        let metas', atoms', ty = act_is_type sgn transf metas atoms atom_type in
        let a = Mk.fresh_atom (Nonce.name atom_nonce) ty in
        metas', (AtomMap.add atom a atoms'), a
      | Some a -> metas, atoms, a
    end

and act_assumption sgn transf metas atoms = function
  | {free_var; free_meta; bound_var; bound_meta} ->
    let fold_metas nonce bdry (mets, atms, acc) =
      begin
        (* Check if meta has already been processed in the assumption set *)
        match Nonce.map_find_opt nonce acc with
        | Some _ -> mets, atms, acc
        | None ->
          begin
            let m = {meta_nonce=nonce ; meta_boundary=bdry} in
            (* Check if meta m has already been translated *)
            match MetaMap.find_opt m mets with
            | Some {meta_nonce=nonce' ; meta_boundary=bdry'} ->
              mets, atms, (Nonce.map_add nonce' bdry' acc)
            | None ->
              let mets', atms', {meta_nonce=nonce' ; meta_boundary = bdry'} = act_meta sgn transf mets atms m in
              mets', atms', (Nonce.map_add nonce' bdry' acc)
          end
      end in
    let fold_free_vars nonce atm_type (mets, atms, acc) =
      begin
        (* Check if atom a has already been processed in the assumption set *)
        match Nonce.map_find_opt nonce acc with
        | Some _ -> mets, atms, acc
        | None ->
          begin
            let a = {atom_nonce=nonce ; atom_type=atm_type} in
            (* Check if atom a has already been translated *)
            match AtomMap.find_opt a atms with
            | Some {atom_nonce=nonce' ; atom_type=t'} ->
              mets, atms, (Nonce.map_add nonce' t' acc)
            | None ->
              let mets', atms', {atom_nonce=nonce' ; atom_type = t'} = act_atom sgn transf mets atms a in
              mets', atms', (Nonce.map_add nonce' t' acc)
          end
      end in
    let metas1, atoms1, free_var' = Nonce.map_fold fold_free_vars free_var (metas, atoms, Nonce.map_empty) in
    let metas2, atoms2, free_meta' = Nonce.map_fold fold_metas free_meta (metas1, atoms1, Nonce.map_empty) in
    metas2, atoms2, {free_var = free_var' ; free_meta = free_meta' ; bound_var ; bound_meta}

and act_eq_type sgn transf metas atoms = function
  | EqType (asm, t1, t2) ->
    let metas1, atoms1, asm' = act_assumption sgn transf metas atoms asm in
    let metas2, atoms2, t1' = act_is_type sgn transf metas1 atoms1 t1 in
    let metas3, atoms3, t2' = act_is_type sgn transf metas2 atoms2 t2 in
    metas3, atoms3, EqType(asm', t1', t2')

and act_eq_term sgn transf metas atoms = function
  | EqTerm (asm, e1, e2, t) ->
    let metas1, atoms1, asm' = act_assumption sgn transf metas atoms asm in
    let metas2, atoms2, e1' = act_is_term sgn transf metas1 atoms1 e1 in
    let metas3, atoms3, e2' = act_is_term sgn transf metas2 atoms2 e2 in
    let metas4, atoms4, t' = act_is_type sgn transf metas3 atoms3 t in
    metas4, atoms4, EqTerm(asm', e1', e2', t')
