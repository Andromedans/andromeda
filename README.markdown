## Andromeda

### About the project

Andromeda is an experimental implementation of dependent type theory with a reflection rule. For theoretical background see:

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
`andromeda.byte` and run some basic tests. You can then investigate the files in the
`examples` subdirectory. The file `prelude.m31` contains basic definitions and is loaded
when Andromeda is started (unless the option `--no-prelude` is given).

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

The GitHub repository is linked to Travis CI. To find out the current build status is
displayed here:

  [![Build Status](https://api.travis-ci.org/andrejbauer/andromeda.png?branch=master)](https://travis-ci.org/andrejbauer/andromeda)

