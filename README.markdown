## Andromeda

### About the project

Andromeda is an experimental implementation of dependent type theory with a reflection rule.
For theoretical background see:

* Andrej Bauer: "How to implemenent type theory with a reflection rule"
  ([slides](http://www.qmac.ox.ac.uk/events/Talk%20slides/Bauer-HoTT-Oxford.pdf) and
   [video](https://www.youtube.com/watch?v=IlfQjWqrK6I))

The reflection rule allows us to do many things, such as add new computation
rules for new type formers, and hopefully also provide support for Vladimir
Voevodsky's [Homotopy Type System](http://ncatlab.org/homotopytypetheory/show/Homotopy+Type+System)
which has *two* kinds of equality, one of which has a reflection rule.


### Compilation

To build Andromeda, you need [Ocaml 4.0](http://ocaml.org) or later (and quite possibly it
works with earlier versions too) and the [menhir](http://gallium.inria.fr/~fpottier/menhir/)
parser generator. We recommend using the [Opam](http://opam.ocamlpro.com) package manager
for OCaml for installation of OCaml and menhir.

If you also install the [ledit](http://opam.ocaml.org/packages/ledit/ledit.2.03/) or
[rlwrap](http://utopia.knoware.nl/~hlub/uck/rlwrap/#rlwrap) utility, the Andromeda toplevel
will use them to give you line editing capabilities.

### Building Andromeda

To build Andromeda type `make` at the command line. This will create the executable
`andromeda.byte`. You can run the tests in the `test` subfolder with `make test`.

The file `prelude.m31` contains basic definitions and is loaded when Andromeda is
started (unless the option `--no-prelude` is given).

#### Examples

We have put some examples in the `examples` subdirectory. An outdated and incomplete
description of the Andromedan type theory can be found in `doc/andromeda.tex`. We are
still changing Andromeda in every respect so it probably does not make sense to write
documentation at this point.

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

### History of the name Andromeda

Andromeda used to be called Brazil, as a consequence of discussions at the Institute for
Advanced Study where we talked about "sending proofs to a far away place where they will
check them independently". We thought of Brazil as a faraway place, but it later turned
out it was not quite far enough. We hope that nobody will claim that the Andromeda galaxy
is a nearby place.

### Travis Continuous Integration

The GitHub repository is linked to Travis CI. To find out the current build status is
displayed here:

  [![Build Status](https://api.travis-ci.org/andrejbauer/andromeda.png?branch=master)](https://travis-ci.org/andrejbauer/andromeda)

