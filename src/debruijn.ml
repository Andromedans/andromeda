

let rec abstract xs e =
  let rec abstract shift ((e',loc) as e) =
    begin match e' with
        
      | Name y ->
          begin match Common.index_of shift y xs with
          | None -> e
          | Some n -> Bound n, loc
          end
          
      | Bound _ -> e
      
      | Lambda abs ->
        let abs = abstract_abstraction abstract_ty abstract_term_ty shift abs
        in Lambda abs, loc

      | Spine (e, abs) ->
        let e = abstract shift e
        and abs = abstract_abstraction abstract_term_ty abstract_ty shift abs
        in Spine (e, abs), loc

      | Type -> e

      | Prod abs ->
        let abs = abstract_abstraction abstract_ty abstract_ty shift abs in
        in Prod abs, loc

      | Eq (t, e1, e2) ->
        let t = abstract_ty shift x t
        and e1 = abstract shift x e1
        and e2 = abstract shift x e2
        in Eq (t, e1, e2), loc

      | Refl (t, e) ->
        let t = abstract_ty shift x t
        and e = abstract shift x e
        in Refl (t, e), loc
    end
      
  and abstract_ty shift ((Ty t), loc) =
    let t = abstract shift t
    in Ty t, loc
  
  and abstract_term_ty shift (e, t) =
    let e = abstract shift e
    and t = abstract_ty shift t
    in (e, t)
    
  in
  let e = abstract 0 e
  in
  Abs (, e)

let abstract_ty = abstract
