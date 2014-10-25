## Andromeda

### About the project

Andromeda is an experimental implementation of dependent type theory which supports
*two* forms of identity types, as proposed by Vladimir Voevodsky in his [Homotopy Type System](http://ncatlab.org/homotopytypetheory/show/Homotopy+Type+System):

* a *strict* equality type `a == b` with an equality reflection rule
* an identity type `a = b` from Martin-Löf intensional type theory

The reflection rule allows the user to define new equality computation rules (which we call
*rewrite* rules), as well give the type checker general equality hints. This allows the
user to define types (such as the natural numbers, booleans, propositional truncation from
homotopy type theory, and others) *and* impose computation rules for them.


### Compilation

To build Andromeda, you need [Ocaml 4.0](http://ocaml.org) or later (and quite possibly it
works with earlier versions too) and the
[menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator. We recommend using
the [Opam](http://opam.ocamlpro.com) package manager for OCaml for installation of OCaml
and menhir.

If you also install the [ledit](http://opam.ocaml.org/packages/ledit/ledit.2.03/) or [rlwrap](http://utopia.knoware.nl/~hlub/uck/rlwrap/#rlwrap) utility, the Andromeda toplevel will use them
to give you line editing capabilities.

### Building Andromeda

To build Andromeda type `make` at the command line. This will create the executable
`andromeda.byte` and run some basic tests. You can then investigate the files in the
`examples` subdirectory. The file `prelude.m31` contains basic definitions and is loaded
when Andromeda is started (unless the option `--no-prelude` is given).

#### Building tt

The subdirectory `tt` contains a version of Andromeda enriched with effects and handlers.
This is even more experimental than Andromeda itself. We hope to merge the two, or maybe
have an independent checker and an assistant. It is too early to tell.

To build tt run `make tt.byte`. It may not compile, because we are currently working
mostly on Andromeda.

#### Examples

We have put some examples in the `examples` subdirectory. An outdated and incomplete
description of the Andromedan type theory can be found in `doc/andromeda.tex`. We are
still changing Andromeda in every respect so it probably does not make sense to write
documentation at this point.

### History of the name Andromeda

Andromeda used to be called Brazil, as a consequence of discussions at the Institute for
Advanced Study where we talked about "sending proofs to a far away place where they will
check them independently". We thought of Brazil as a faraway place, but it later turned
out it was not quite far enough. We hope that nobody will claim that the Andromeda galaxy
is a nearby place.

### Travis Continuous Integration

The GitHub repository is linked to Travis CI. To find out the current build status is displayed here: [![Build Status](https://api.travis-ci.org/andrejbauer/andromeda.png?branch=master)](https://travis-ci.org/andrejbauer/andromeda)
