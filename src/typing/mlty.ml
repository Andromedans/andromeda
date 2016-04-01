
module Ctx = struct

  type t = unit
  let empty : t = ()

end

let toplevel ctx ({Location.thing=c; loc} : Syntax.toplevel) =
  ()
  (* match c with *)
  (* | Syntax.DefMLType _ -> failwith "TODO" *)
  (* | Syntax.DefMLTypeRec _ -> failwith "TODO" *)
  (* | Syntax.DeclOperation (_,_) -> failwith "TODO" *)
  (* | Syntax.DeclConstants (_,_) -> failwith "TODO" *)
  (* | Syntax.TopHandle _ -> failwith "TODO" *)
  (* | Syntax.TopLet _ -> failwith "TODO" *)
  (* | Syntax.TopLetRec _ -> failwith "TODO" *)
  (* | Syntax.TopDynamic (_,_) -> failwith "TODO" *)
  (* | Syntax.TopNow (_,_) -> failwith "TODO" *)
  (* | Syntax.TopDo _ -> failwith "TODO" *)
  (* | Syntax.TopFail _ -> failwith "TODO" *)
  (* | Syntax.Verbosity _ -> failwith "TODO" *)
  (* | Syntax.Included _ -> failwith "TODO" *)
