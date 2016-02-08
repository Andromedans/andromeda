---
title: Andromeda code
navigation: code
layout: page
---

## About the code

### The structure of source code

The source code can be found in `src`, in the following folders:

* `parser` - input syntax, lexer, parser, and the desugaring phase which computes de Bruijn indices
   and separates expressions and computations
* `runtime` - context manipulation, runtime values and the main evaluation loop
* `tt` - abstract syntax, weak-head normal forms, equality checks
* `utils` - error messages, file locations, pretty printing, manipulation of variable names
* `andromeda.ml` - main program
* `config.ml` - configuration
* `syntax.mli` - desugared input syntax

The basic steps in the evaluation of input are:

1. An expression is parsed using the lexer `parser/lexer.mll` and the parser `parser/parser.mly`.
   The result is a value of type `Input.term` or `Input.ty` or `Input.toplevel`. The user input
   has no separation of computations (effectful) and expressions (pure).
2. `Desugar` converts the parsed entity to the corresponding intermediate representation of
   type `Syntax.expr`, `Syntax.comp` or `Syntax.toplevel`. Desugaring replaces named bound variables
   with de Bruijn indices and separates computations from expressions.
3. `Eval` evaluates the syntactic expression to a result of type `Value.result`. The result is a
   pair [(e,t)] of a value [e] and its type [t]. Evaluation is done in a context [ctx] of type
   [Context.t] which consists of: free variables with their types, bound variables mapped to their
   values, and equality hints.

The correctness guarantee for the evaluator is this: if a computation [c] evaluates to a value [(e,t)]
in context [ctx] then the judgement [ctx |- e : t] is derivable.

