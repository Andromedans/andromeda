---
layout: page
title: How to install Andromeda
navigation: "install"
---

Andromeda is implemented in [OCaml](https://ocaml.org) and relies on the [OPAM](https://opam.ocaml.org) package manager
for installation. Please make sure you have a recent working OCaml & OPAM.

Execute the following command to get and install Andromeda:

    opam pin add andromeda git+https://github.com/Andromedans/andromeda

### How to compile Andromeda

If you would like to compile Andromeda yourself, follow these instructions.

#### Prerequisites

You need [OCaml 4.12](https://ocaml.org) or later, and quite possibly it works with earlier versions,
and several OCaml packages, which you can install by running

    opam install dune dune-build-info dune-site menhir sedlex

If you also install the [ledit](http://opam.ocaml.org/packages/ledit/ledit.2.03/) or
[rlwrap](http://utopia.knoware.nl/~hlub/uck/rlwrap/#rlwrap) utility, the Andromeda
toplevel will use them to give you line editing capabilities.

#### Compilation

Checkout the Andromeda repository

    git clone git@github.com:Andromedans/andromeda.git

or consider [forking it](https://github.com/Andromedans/andromeda#fork-destination-box) if
you indent do experiment with it, or contribute to the project.

To build Andromeda, run the command

    dune build

in the `andromeda` folder. This will create the executable `./andromeda.exe`. You can also run tests with

    dune runtest

If you see no input, the tests passed.

#### Usage

You may run the compiled executable `andromeda.exe`. For basic usage and command-line options, run

    ./andromeda.exe --help

