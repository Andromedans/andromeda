---
title: Andromeda code
navigation: code
layout: page
---

## About the code

### The structure of source code

The source code can be found in `src`, in the following folders:

* `andromeda.ml` - main program
* `config.ml` - runtime configuration parameters
* `syntax.mli` - abstract syntax of the meta-language (desugared form)
* folder `parser`:
   * `desugar.ml` - desugar the `Input` syntax to `Syntax` syntax.
   * `input.mli` - abstract syntax of the meta-language (sugared form)
   * `lexer.ml` - the lexical structure of the meta-language
   * `parser.mly` - the meta-language parser
* folder `utils`:
   * `error.ml` - errors, warning, and other messages
   * `location.ml` - source-code location datatype
   * `name.ml` - manipulation of names
   * `print.ml` - general printing routines
   * `store.ml` - implementation of mutable storage
* folder `nucleus`:
   * `assumption.ml` - tracking of dependency of terms on free variables
   * `context.ml` - contexts as directed graphs
   * `equal.ml` - judgmental equality
   * `eval.ml` - evaluation of meta-language computations
   * `external.ml` - interface to OCaml functions
   * `jdg.ml` - type-theoretic judgements
   * `matching.ml` - meta-language pattern matching
   * `simplify.ml` - simplification of terms (currently not used)
   * `toplevel.ml` - evaluation of top-level meta-language commands
   * `tt.ml` - type theory syntax
   * `value.ml` - meta-language run-time values, operations, and handlers

### Main evaluation loop

1. An expression is parsed using the lexer `parser/lexer.ml` and the parser `parser/parser.mly`.
   The result is a list of `Input.toplevel` commands or a single command.
2. `parser/desugar.ml` converts the parsed `Input` entity to the corresponding `Syntax` entity.
   Desugaring discerns names into bound variables (represented as de Bruijn indices),
   constants, signatures, data constructors, operations and dynamic variables.
3. `nucleus/eval.ml` evaluates `Syntax.comp` computations inside `Syntax.toplevel` commands to `Value.comp`,
   which are functions from a runtime environment to either a final value or an operation.
   The possible values are:
      * a `Value.Term` term judgement of the form `Γ ⊢ e : A`, see `Jdg.term`
      * a function closure `Value.Closure`
      * a handler `Value.Handler`
      * a data constructor `Value.Tag`
      * a `Value.List` of values
      * a `Value.Tuple` of values
      * a mutable `Value.Ref`
      * a `Value.String`
      * an identifier `Value.Ident`
4. `nucleus/toplevel.ml` evaluates `Syntax.toplevel` commands to `Value.toplevel` functions modifying the runtime environment.

