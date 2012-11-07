A minimalist implementation of type theory with universes and dependent products. The
concrete syntax is as follows:

* The universes are `Type 0`, `Type 1`, `Type 2`, ...
* A dependent product is written as `forall x : T1, T2`
* A function is written as `fun x : T => e`
* Application is written as `e1 e2`

## Compilation

You need `ocamlbuild` and `make`. You can type

* `make` to make the `tt.native` executable.
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
