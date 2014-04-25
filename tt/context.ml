(** Typing Contexts for Brazil *)

module Ctx = ContextFn.Make(struct
                              type term = Syntax.term
                              let shift = Syntax.shift
                              let print = Print.term
                            end)

