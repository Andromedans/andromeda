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
   * `eval.ml` - the main nucleus evaluation loop
   * `external.ml` - interface to OCaml functions
   * `jdg.ml` - type-theoretic judgements
   * `matching.ml` - meta-language pattern matching
   * `simplify.ml` - simplification of terms (currently not used)
   * `tt.ml` - type theory syntax
   * `value.ml` - meta-language run-time values, operations, and handlers

### Main evaluation loop

1. An expression is parsed using the lexer `parser/lexer.ml` and the parser `parser/parser.mly`.
   The result is a value of type `Input.comp` (a computation) or  a `Input.toplevel` directive.
2. `parser/desugar.ml` converts the parsed `Input` entity to the corresponding `Syntax` entity.
   Desugaring discerns names into bound variables (represented as de Bruijn indices),
   constants, data constructors, and operations. It also looks up labels in signature definitions.
3. `nucleus/eval.ml` evaluates `Syntax` to a `Value.result` which is either a final value
   or an operation. The possible values are:
       * a `Value.Term` term judgement of the form `Γ ⊢ e : A`, see `Jdg.term`
       * a function closure `Value.Closure`
       * a handler `Value.Handler`
       * a data constructor `Value.Tag`
       * a `Value.List` of values
       * a `Value.Tuple` of values
       * a mutable `Value.Ref`
       * a `Value.String`
       * an identifier `Value.Ident`

