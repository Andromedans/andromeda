A minimalist implementation of type theory in fewer than 500 lines of Ocaml code,
including comments. This version corresponds to the one described in the blog post
[How to implement dependent type theory I](http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/).

## The type theory

The dependent type theory `tt` has the following ingridients:

* The universes are `Type 0`, `Type 1`, `Type 2`, ...
* A dependent product is written as `forall x : T1, T2`
* A function is written as `fun x : T => e`
* Application is written as `e1 e2`

The hierarchy of universes is not commulative, i.e., even though `Type k` has type `Type
(k+1)`, `Type k` is *not* a subuniverse of `Type (k+1)`.

## Compilation

You need `ocamlbuild`, which is part of OCaml, the `menhir` parser generator, and `make`.
You can type

* `make` to make the `tt.native` executable.
* `make byte` to make the bytecode `tt.byte` executable.
* `make clean` to clean up.
* `make doc` to generate HTML documentation (see the generated `tt.docdir/index.html`).

## Usage

Type `Help.` in the interactive shell to see what the type system can do. Here is a sample
session:

    Type Ctrl-D to exit or "Help." for help.]
    # Parameter nat : Type 0.
    nat is assumed
    # Parameter z : nat.
    z is assumed
    # Parameter s : nat -> nat.
    s is assumed
    # Eval (fun f : nat -> nat => fun n : nat => f (f (f (f n)))) (fun n : nat => s (s (s n))) (s (s (s (s z)))).
        = s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s z)))))))))))))))
        : nat
    # Check (fun A : Type 0 => fun f : A -> Type 1 => fun a : A => f A).
    Typing error: type mismatch
    # Check (fun A : Type 0 => fun f : A -> Type 1 => fun a : A => f a).
    fun A : Type 0 => fun f : A -> Type 1 => fun a : A => f a
        : forall A : Type 0, (A -> Type 1) -> A -> Type 1


## Source code

The purpose of the implementation is to keep the source uncomplicated and short. The
essential bits of source code can be found in the following files. It should be possible
for you to just read the entire source code. You should start with the core

* `syntax.ml` -- abstract syntax
* `ctx.ml` -- contexts
* `infer.ml` -- type inference and normalization

and continue with the infrastructure

* `tt.ml` -- interactive top level
* `error.ml` -- error reporting
* `lexer.mll` and `parser.mly` -- concrete sytnax
* `beautify.ml` and `print.ml` -- pretty printing


## Inefficiency

The code is meant to be short and sweet, and close to how type theory is presented on
paper. Therefore, it is not suitable for a real implementation, as it will get horribly
inefficient as soon as you try anything complicated. But it should be useful for
experimentation.


## What experiments should I perform to learn more?

There are many things you can try, for example:

* basic types `unit`, `bool` and `nat`
* the eta rule for functions
* dependent sums
* de Bruijn indices
* cummulative universes, so that [A : Type k] implies [A : Type (k+1)]
* better type inference so that variables need not be explicitly typed
* flexible syntax, e.g., allow `fun x y : nat => ...` instead of `fun x : nat => fun y : nat => ...`
* prefix and infix operators
