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
   * `level.ml` - precedence levels for concrete syntax
   * `location.ml` - source-code location datatype
   * `name.ml` - manipulation of names
   * `print.ml` - general printing routines
   * `store.ml` - implementation of mutable storage
* folder `nucleus`:
   * `assumption.ml` - tracking of dependency of terms on free variables
   * `jdg.ml` - type-theoretic judgements and contexts
   * `TT.ml` - type theory syntax
* folder `runtime`:
   * `equal.ml` - judgmental equality
   * `eval.ml` - evaluation of meta-language computations
   * `external.ml` - interface to OCaml functions
   * `matching.ml` - meta-language pattern matching
   * `predefined.ml` - pre-defined types and values
   * `runtime.ml` - meta-language run-time values, operations, and handlers
   * `toplevel.ml` - toplevel computations
* folder `typing`: AML typing (under construction)

### Main evaluation loop

1. An expression is parsed using the lexer `parser/lexer.ml` and the parser `parser/parser.mly`.
   The result is a top-level computation of type `Input.toplevel`.
2. `parser/desugar.ml` converts the parsed `Input` entity to the corresponding `Syntax` entity.
   Desugaring discerns names into bound variables (represented as de Bruijn indices),
   constants, data constructors, and operations.
3. `typing/mlty.ml` infers the ML-types (under construction)
4. `runtime/eval.ml` evaluates `Syntax.toplevel` to a `Runtime.toplevel`. In the course of
   a top-level evaluation there are subordinate evaluation procedures, the most interesting of
   which takes a computation `Syntax.comp` to a `Runtime.result` which is either a `Runtime.value`
   or an operation.
