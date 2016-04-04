type meta = int
type param = int

type ty =
  | Jdg
  | String
  | Meta of meta
  | Param of param
  | Tuple of ty list
  | Arrow of ty * ty
  | Handler of ty * ty
  | App of Syntax.level * ty list
  | Ref of ty

type ty_def = 
type ty_schema = 


module Ctx = struct

  type t = { defs : ty_def list ;
             vars : (Name.ident * ty_schema) list ;
             ops  : (Name.operation * ty_schema) list ;
           }
  let empty : t = ()

end

let rec comp ctx subst unsolved ({Location.thing=c; loc} : Syntax.comp) =
  match c with
  | Syntax.Type  -> failwith "TODO"
  | Syntax.Bound _ -> failwith "TODO"
  | Syntax.Function (_,_) -> failwith "TODO"
  | Syntax.Handler _ -> failwith "TODO"
  | Syntax.Constructor (_,_) -> failwith "TODO"
  | Syntax.Tuple _ -> failwith "TODO"
  | Syntax.Operation (_,_) -> failwith "TODO"
  | Syntax.With (_,_) -> failwith "TODO"
  | Syntax.Let (_,_) -> failwith "TODO"
  | Syntax.LetRec (_,_) -> failwith "TODO"
  | Syntax.Now (_,_,_) -> failwith "TODO"
  | Syntax.Lookup _ -> failwith "TODO"
  | Syntax.Update (_,_) -> failwith "TODO"
  | Syntax.Ref _ -> failwith "TODO"
  | Syntax.Sequence (_,_) -> failwith "TODO"
  | Syntax.Assume (_,_) -> failwith "TODO"
  | Syntax.Where (_,_,_) -> failwith "TODO"
  | Syntax.Match (_,_) -> failwith "TODO"
  | Syntax.Ascribe (_,_) -> failwith "TODO"
  | Syntax.External _ -> failwith "TODO"
  | Syntax.Constant _ -> failwith "TODO"
  | Syntax.Lambda (_,_,_) -> failwith "TODO"
  | Syntax.Apply (_,_) -> failwith "TODO"
  | Syntax.Prod (_,_,_) -> failwith "TODO"
  | Syntax.Eq (_,_) -> failwith "TODO"
  | Syntax.Refl _ -> failwith "TODO"
  | Syntax.Yield _ -> failwith "TODO"
  | Syntax.Hypotheses  -> failwith "TODO"
  | Syntax.Congruence (_,_) -> failwith "TODO"
  | Syntax.Extensionality (_,_) -> failwith "TODO"
  | Syntax.Reduction _ -> failwith "TODO"
  | Syntax.String _ -> failwith "TODO"
  | Syntax.Occurs (_,_) -> failwith "TODO"
  | Syntax.Context _ -> failwith "TODO"

let rec toplevel ctx ({Location.thing=c; loc} : Syntax.toplevel) =
  match c with
  | Syntax.DefMLType _ -> failwith "TODO"
  | Syntax.DefMLTypeRec tydefs -> def_ml_type_rec ctx tydefs
  | Syntax.DeclOperation (_,_) -> failwith "TODO"
  | Syntax.DeclConstants (_,_) -> failwith "TODO"
  | Syntax.TopHandle _ -> failwith "TODO"
  | Syntax.TopLet _ -> failwith "TODO"
  | Syntax.TopLetRec _ -> failwith "TODO"
  | Syntax.TopDynamic (_,_) -> failwith "TODO"
  | Syntax.TopNow (_,_) -> failwith "TODO"
  | Syntax.TopDo _ -> failwith "TODO"
  | Syntax.TopFail _ -> failwith "TODO"
  | Syntax.Verbosity _ -> ctx
  | Syntax.Included cs ->
     List.fold_left
       (fun (f, cs) ctx -> List.fold_left toplevel ctx cs) ctx cs
