---
layout: page
title: How to install Andromeda
andromeda_version: 2
navigation: "install"
---

## Installation

### Installation with OPAM

The easiest way to install Andromeda is through the [Opam](http://opam.ocamlpro.com)
package manager for OCaml. You can install Opam on your system following
[these instructions](http://opam.ocaml.org/doc/Install.html). In case your operating
system does not provide OCaml version >= 4.07, you can install it with `opam switch
4.08.1`. Then simply add the Andromeda repo to opam, update and install Andromeda with
these commands:

    git clone https://github.com/Andromedans/andromeda
    cd andromeda
    opam update
    opam pin add andromeda .    # for installation (confirm twice with "y")
    opam upgrade                # to upgrade

### Building Andromeda

#### Prerequisites

To build Andromeda, you need [OCaml 4.07](http://ocaml.org) or later (and quite possibly
it works with earlier versions too), the
[menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator and the
[sedlex](https://www.lexifi.com/sedlex) unicode lexer. We recommend using
[Opam](http://opam.ocamlpro.com) for installation of OCaml and dependencies.

If you also install the [ledit](http://opam.ocaml.org/packages/ledit/ledit.2.03/) or
[rlwrap](http://utopia.knoware.nl/~hlub/uck/rlwrap/#rlwrap) utility, the Andromeda
toplevel will use them to give you line editing capabilities.

#### Compilation

Checkout the Andromeda repository

    git clone git@github.com:Andromedans/andromeda.git

or consider [forking it](https://github.com/Andromedans/andromeda#fork-destination-box) if
you indent do contribute to the project.

To build Andromeda type `make` at the command line. This will create the executable
`andromeda.native`. You can run the tests in the `test` subfolder with `make test`.

The file `prelude.m31` contains basic definitions and is loaded when Andromeda is
started (unless the option `--no-prelude` is given).
