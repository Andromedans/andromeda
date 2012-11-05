A minimalist implementation of type theory with universes indexed by numerals and
dependent products. The concrete syntax is as follows:

* The universes are `Type 0`, `Type 1`, `Type 2`, ...
* A dependent product is written as `forall x : T1, T2`
* A function is written as `fun x : T => e`
* Application is written as `e1 e2`

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
essential bits of source code can be found in the following files:

* `syntax.ml` the abstract syntax of the type system
* `value.ml` auxiliary datatype used during normalization
* `eval.ml` type checking and normalization

The rest of the files are just logistics:

* `lexer.mll` lexical analysis of concrete syntax
* `parser.mly` parser which converts concrete syntax to abstract syntax
* `print.ml` pretty-printing of expressions
* `common.ml` commonly used functions
* `error.ml` printing of errors
* `tt.ml` toplevel interactive shell
