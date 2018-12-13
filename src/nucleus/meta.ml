open Jdg_typedefs

let name m = m.meta_name

let type_of_term {meta_type;_} args =
  Instantiate_meta.fully_apply_abstraction_no_typechecks
    (TT_instantiate.type_fully ?lvl:None) meta_type args
