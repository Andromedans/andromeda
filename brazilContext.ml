(** Typing Contexts for Brazil *)

module Ctx = ContextFn.Make(struct
                              type term = BrazilSyntax.term
                              let shift = BrazilSyntax.shift
                              let print = BrazilPrint.term
                            end)

