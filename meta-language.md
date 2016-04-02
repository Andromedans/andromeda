---
title: The Andromeda meta-language
navigation: meta-language
layout: page
use_math: true
---

Table of contents:

* [About the Andromeda meta-language](#about-the-andromeda-meta-language)
* [General-purpose programming](#general-purpose-programming)
   * [`let`-binding](#let-binding)
   * [Sequencing](#sequencing)
   * [Functions](#functions)
   * [Recursive functions](#recursive-functions)
   * [Datatypes](#datatypes)
   * [`match` statements and patterns](#match-statements-and-patterns)
   * [Operations and handlers](#operations-and-handlers)
   * [Mutable references](#mutable-references)
   * [Dynamic variables](#dynamic-variables)
* [Judgment computations](#judgment-computations)
   * [Infering and checking mode](#inferring-and-checking-mode)
   * [The universe](#the-universe)
   * [Constants](#constants)
   * [Assumptions](#assumptions)
   * [Substitution](#substitution)
   * [Product](#product)
   * [$λ$-abstraction](#abstraction)
   * [Application](#application)
   * [Equality type](#equality-type)
   * [Reflexivity](#reflexivity)
   * [Equality checking](#equality-checking)
   * [Type ascription](#type-ascription)
   * [Context and occurs check](#context-and-occurs-check)
   * [Hypotheses](#hypotheses)
   * [Externals](#externals)
* [Toplevel commands](#toplevel-commands)
   * [Toplevel let binding](#toplevel-let-binding)
   * [Toplevel dynamic variables](#toplevel-dynamic-variables)
   * [Declarations](#declarations)
   * [`Do` command](#do-command)
   * [`Fail` command](#fail-command)
   * [Toplevel handlers](#toplevel-handlers)
   * [Include](#include)
   * [Verbosity](#verbosity)
   * [Help](#help)
   * [Environment](#environment)
   * [Quit](#quit)

### About the Andromeda meta-language

Andromeda is a proof assistant designed as a programming language following the tradition
of Robin Milner's
[Logic for computable functions](http://i.stanford.edu/pub/cstr/reports/cs/tr/72/288/CS-TR-72-288.pdf)
(LCF). We call it the **Andromeda meta-language (AML)**.

Andromeda computes typing judgments of the form $\isterm{\G}{\e}{\T}$ ("Under
assumptions $\G$ term $\e$ has type $\T$"), but only the ones that are *derivable* in
[type theory with equality reflection](type-theory.html). This is known as *soundness* of
AML. *Completeness* of AML states that every derivable judgment is computed by some
program. Neither property has actually been proved yet, we are working on it.

AML is a functional call-by-value language with algebraic effects and handlers.
At present AML is dynamically typed. We are planning to put some types on it.

While Robin Milner's LCF and its HOL-style descendants compute judgments in *simple* type theory,
AML computes judgments in *dependent* type theory. This creates a significant overhead in the
complexity of the system and so while [John Harisson](http://www.cl.cam.ac.uk/~jrh13/) is
able to print the [HOL Light kernel](http://www.cl.cam.ac.uk/~jrh13/) on a T-shirt, it may
take a super-hero's cape to print the 4000 lines of
[Andromeda nucleus](https://en.wikipedia.org/wiki/Andromeda_Galaxy#Nucleus).

The constructs of the language are divided into **computations** which evaluate to values and may emit operations,
and **top-level commands** which have side effects (such as binding a variable to a value)
and must be self-contained with regards to operations.
An Andromeda program is a list of top-level commands, each containing some computations.

It is important to distinguish the expressions that are evaluated by AML from the
expressions of underlying type theory. We refer to AML expressions as **computations** to
emphasize that Andromeda *computes* their values and that the computations may have
*effects* (such as printing things on the screen).
We refer to the expressions of the type theory as **(type-theoretic) terms**.


### General-purpose programming

AML is a complete programming language which supports the following general-purpose
programming features:

* `let-`bindings of values
* first-class functions 
* (mutually) recursive definitions of functions
* datatypes (lists, tuples, and user-definable data constructors)
* `match` statements and pattern matching
* operations and handlers
* mutable references
* dynamic variables

Note: the `match` statement is part of the meta-language and is not available in the
underlying type theory (where we would have to postulate suitable eliminators instead). It
is a mechanism for analyzing terms and other values at the meta-level.

##### `let`-binding

A binding of the form

    let x = c₁ in c₂

computes `c₁` to a value `v`, binds `x` to `v`, and computes `c₂`. Thus, whenever `x` is
encountered in `c₂` it is replaced by `v`.
 
It is possible to bind several values simultaneously:

    let x₁ = c₁
    and x₂ = c₂
     ⋮
    and xᵢ = cᵢ in
      c

The bound names `x₁`, ..., `xᵢ` do *not* refer to each other, thus:

    # let x = "foo"
    x is defined.
    # let y = "bar"
    y is defined.
    # do let x = y and y = x in (x, y)
    ("bar", "foo")

##### Functions

A meta-level function is not to be confused with a $λ$-abstraction in the underlying type
theory. A meta-level function has the form

    fun x => c

Example:

    # do fun x => (x, x)
    <function>
    # do (fun x => (x, x)) "foo"
    ("foo", "foo")

An iterated function

    fun x₁ => fun x₂ => ... => fun xᵢ => c

may be written as

    fun x₁ x₂ ... xᵢ => c

A `let`-binding of the form

    let f x₁ ... xᵢ = c

is a shorthand for

    let f = (fun x₁ x₂ ... xᵢ => c)

A `let`-binding of the form

    let f x₁ ... xᵢ : t = c

is a shorthand for

    let f = (fun x₁ x₂ ... xᵢ => c : t)

where `c : t` is [type ascription](#type-ascription).

##### Sequencing

The sequencing construct

    c₁ ; c₂

computes `c₁`, discards the result, and computes `c₂`. It is equivalent to

    let _ = c₁ in c₂

except for warning when `c₁` evaluates to something other than the empty tuple `()`.

##### Recursive functions

Recursive functions can be defined:

    let rec f x₁ ... xᵢ = c₁ in
      c₂


is a local recursive function definition. Multiple mutually recursive functions may be
defined with

    let rec f₁ x₁ x₂ ... = c₁
        and f₂ y₁ y₂ ... = c₂
         ⋮
        and fⱼ z₁ z₂ ... = cⱼ

##### Datatypes

Apart from judgments AML also computes other values, such as functions, lists, tuples, and
elements of other datatypes. We describe the datatypes in this section.

###### Strings

A string is a sequence of characters delimited by quotes, e.g.

    "This string contains forty-two characters."

There are at present no facilities to manipulate strings in AML other than printing.

###### Tuples

A meta-level tuple is written as `(c₁, ..., cᵢ)`.

##### Type definitions

AML type system is currently under construction. It will support the usual datatype
defintions, such as inductive datatypes and records. At the moment there are predefined
lists and optional types.

###### Optional values

The value `None` indicates a lack of value and `Some v` indicates the presence of value `v`.

###### Lists

The empty list is written as `[]`. The list whose head is `c₁` and the tail is `c₂` is
written as `c₁ :: c₂`. The computation

    [c₁, c₂, ..., cᵢ]

is shorthand for

    c₁ :: (c₂ :: ... (cᵢ :: []))

At present, due to lack of meta-level types, lists are heterogeneous in the sense that
they may contain values of different shapes.

##### `match` statements and patterns

A `match` statement is also known as `case` in some languages and is simulated by
successive `if`-`else if`-...-`else if`-`else` in others. The general form is

    match c with
    | p₁ => c₁
    | p₂ => c₂
      ...
    | pᵢ => cᵢ
    end

The first bar `|` may be omitted.

First `c` is computed to a value `v` which is matched in order against the patterns `p₁`,
..., `pᵢ`. If the first matching pattern is `pⱼ`, by which we mean that it has the shape
described by the pattern `pⱼ`, then the corresponding `cⱼ` is computed. The pattern `pⱼ`
may bind variables in `cⱼ` to give `cⱼ` access to various parts of `v`.

If no pattern matches `v` then an error is reported.

Example:

    match ["foo","bar","baz"] with
    | [] => []
    | ?x :: (?y :: _) => (y, x)
    end

computes to `("bar", "foo")` because the second pattern matches the list and binds `x` to
`"foo"` and `y` to `"bar"`.

###### General patterns

The general patterns are:

   |---|---|
   | `_` | match any value |
   | `?x` | match any value and bind it to `x` |
   | `p as ?x` | match according to pattern `p` and also bind the value to `x` |
   | `x` | match a value if it equals the value of `x` |
   | `⊢ j` | match a judgment $\isterm{\G}{\e}{\T}$ according to the *judgment pattern `j`*, see below |
   | `⊢ j₁ : j₂` | match a judgement $\isterm{\G}{\e}{\T}$ with `j₁` and $\isterm{\G}{\T}{Type}$ with `j₂` |
   | `Tag p₁ ... pᵢ` | match a data tag |
   | `[]` | match the empty list |
   | `p₁ :: p₂` | match the head and the tail of a non-empty list |
   | `[p₁, ..., pᵢ]` | match the elements of the list |
   | `(p₁, ..., pᵢ)` | match the elements of a tuple |

Patterns need *not* be linear, i.e., a pattern variable `?x` may appear several times in
which case the corresponding values must be equal. Thus in AML we can compare two values
for equality with

    match (c₁, c₂) with
    | (?x, ?x) => "equal"
    | _ => "not equal"
    end

Note that a pattern may refer to `let`-bound values by their name:

    # let a = "foo"
    a is defined.
    # do match ("foo", "foo", "bar") with (a, ?y, ?z) => (y,z) end
    ("foo", "bar")

In the above `match` statement the pattern refers to `a` whose values is `"foo"`.

###### Judgment patterns

A judgment pattern matches a judgment $\isterm{\G}{\e}{\T}$ as follows:

   |---|---|
   | `_` | match any term |
   | `?x` | match any term and bind it to `x` |
   | `x` | match the value of `x` |
   | `Type` | match a [universe](#the-universe) |
   | `∏ (?x : j₁), j₂` | match a [product](#product) (see [matching under binders](#matching-under-binders)) |
   | `∏ (x : j₁), j₂` | match a product but not the bound variable |
   | `j₁ j₂` | match an [application](#application) |
   | `λ (?x : j₁), j₂` | match a [λ-abstraction](#abstraction) |
   | `λ (x : j₁), j₂` | match a λ-abstraction, but not the bound variable |
   | `λ ?x, j` | shorthand for `λ (?x : _), j` |
   | `j₁ ≡ j₂` | match an [equality type](#equality-type) |
   | `refl j` | match a [reflexivity term](#reflexivity) |
   | `_atom ?x` | match a [free variable](#assumptions) and bind its natural judgment to `x` |
   | `_constant ?x` | match a [constant](#constants) and bind its natural judgment to `x` |

###### Matching under binders

When matching a judgement $\isterm{\G}{∏ (x : A) B}{Type}$ with a pattern `∏ (y : j₁), j₂`,
a fresh variable $y₁$ is produced so that we may match $\isterm{\G, y₁ : A}{B}{Type}$ with `j₂`.

Patterns which match under a binder have two forms:
* one in which the binder variable is a pattern variable, such as `∏ (?y : j₁), j₂`.
  Then `?y` is a pattern variable which is bound to $\isterm{\G, y₁ : A}{y₁}{A}$.
* one in which the binder variable is not a pattern variable, such as `∏ (y : j₁), j₂`.
  Then `y` is bound to $\isterm{\G, y₁ : A}{y₁}{A}$ only in `j₂`.

#### Operations and handlers

The AML operations and handlers are similar to those of the
[Eff programming language](http://www.eff-lang.org). We first explain the syntax and give
several examples below.

##### Operations

A new operation is declared by

    operation op i

where `op` is the operation name and the numeral `i` is its arity, i.e., the number of
arguments it takes. An operation is then invoked with

    op c₁ .. cᵢ

One way to think of an operation is as a generalized resumable exception: when an
operation is invoked it "propagates" outward to the innermost handler that handles it. The
handler may then perform an arbitrary computation, and using `yield` it may also resume
the execution at the point at which the operation was invoked.

##### Handlers

We can think of a handler as a generalized exception handler, except that it handles one
or more operations, as well as values (computations which do not invoke an operation).

A handler has the form

    handler
    | op-case₁
    | op-case₂
    ...
    | op-caseᵢ
    | val-case
    ...
    | val-case
    | finally-clause
    ...
    | finally-clause
    end

where `op-case` are *operation cases*, `val-case` is the *value case* and `finally-clause`
is the *finally clause*.

###### The operation cases

An operation case has the form

    | op p₁ ... pᵢ => c

or the form

    | op p₁ ... pᵢ : p => c

The first form matches an invoked operation `op' v₁ ... vᵢ`
when `op` equals `op'` and each `vⱼ` matches the corresponding pattern `pⱼ`.
The second form matches an invoked operation `op' v₁ ... vᵢ`
when `op` equals `op'`, each `vⱼ` matches the corresponding `pⱼ`
*and* if the operation was invoked in [checking mode](#inferring-and-checking-mode) at type
`t`, `Some t` matches `p`, otherwise `None` matches `p`.

When an operation case matches the corresponding computation `c` is computed, with the
pattern variables appearing in the patterns bound to the corresponding values.

When an operation is invoked it has an associated *delimited continuation* which is the
execution point at which the operation was invoked. The computation `c` of the handler
case may *restart* the continuation with

    yield c'

This will compute `c'` to a value `v` which is then passed to the continuation. This will
have the effect of resuming computation at the point in which the operation was invoked.

###### The value cases

A value case has the form

    | val ?p => c

It is used when the handler handles a computation that did *not* invoke a computation but
rather computed to a value `v`. In this case the value cases are matched against the value
and the first one that matches is used.

If no value case is present in the handler, it is considered to be the trivial case `val ?x => x`.

If at least one value case is present,
but the handled computation evaluates to a value which is matched by none of them,
a runtime error will occur.

###### The `finally` case

A finally case has the form

    | finally ?p => c

It is used at the very end of handling, after the final value has been computed through
handling by operation and value cases. The first finally case that matches is used.

As with value cases, no finally case is equivalent to a trivial case,
and non-exhaustive matching results in a runtime error.

##### The handling construct

To actually handle a computation `c` with a handler `h` write

    with h handle c

The notation

    handle
     c
    with
    | handler-case₁
    ...
    | handler-caseᵢ
    end

is a shorthand for

    with
      handler
      | handler-case₁
      ...
      | handler-caseᵢ
      end
    handle
      c

Several handlers may be stacked on top of each other, for instance

    with h₁ handle
      ...
      with h₂ handle
        ...
        c
        ...

When a computation `c` invokes an operation, the operation is handled by the innermost
handler that has a matching case for that operation.

###### Example

To show what sort of thing you can do with a handler we implement a feature which allows
us to place arbitrary holes in terms. We will use constructs that we have not yet
described, in particular

    operation Hole 0

    let rec prodify xs t =
      match xs with
        | [] => t
        | (|- ?x : ?u) :: ?xs =>
            let t' = forall (y : u), (t where x = y) in
            prodify xs t'
      end

    let rec apply head es =
      match es with
        | [] => head
        | ?e :: ?es => (apply head es) e
      end

    let hole_filler =
      handler
        Hole : ?t =>
          let xs = hypotheses in
          let t' = prodify xs t in
          assume hole : t' in 
          yield (apply hole xs)
      end

First we declare a nullary operation `Hole`. Then we define two auxiliary functions that
compute iterated products and applications:

    # constant A B : Type
    Constant A is declared.
    Constant B is declared.
    # let a = assume a : A in a
    a is defined.
    # let b = assume b : B in b
    b is defined.
    # constant F : A -> B -> Type
    Constant F is declared.
    # do prodify [a, b] (F a b)
    ⊢ Π (y : B) (y0 : A), F y0 y : Type
    # do apply F [b, a]
    a₁₀ : A, b₁₁ : B ⊢ F a₁₀ b₁₁ : Type

Now we can use the `hole_filler` handler to temporarily assume existence of a term by writing `Hole` anywhere in a term:

    # constant A : Type
    Constant A is declared.
    # constant F : A → Type
    Constant F is declared.
    # constant G : ∏ (a : A), F a → Type
    Constant G is declared.
    # do with hole_filler handle λ (a : A), G a Hole
    hole₁₆ : Π (y : A), F y
    ⊢ λ (a : A), G a (hole₁₆ a) : A → Type

Andromeda evaluated `G a Hole` as follows: it first found out that `G` is a constant of
type `∏ (a : A), F a → Type`. Then it evaluated its second argument `a` in checking mode
at type `A` which evaluated to `a : A ⊢ a : A`. Then it evaluated the operation `Hole` in
checking mode at type `F a`. At this point the handler `hole_filler` handled the
operation. It created a new assumption `hole₁₆` of type `Π (y : A), F y`, applied it to
`a` and `yield`-ed it back. The result was then a λ-abstraction, as displayed.

Here is another, simpler example:

    # do with hole_filler handle λ (X : Type) (f : X → X), f Hole
    hole₂₂ : Π (y : Type), (y → y) → y 
    ⊢ λ (X : Type) (f : X → X), f (hole₂₂ X f)
      : Π (X : Type), (X → X) → X

In this case `hole_filler` created a new assumption `hole₂₂` of the displayed type.

#### Mutable references

Mutable references are as in Ocaml:
* a fresh reference is introduced by `ref c` where `c` evaluates to its initial value
* if `c` evaluates to a reference, its value can be accessed by `! c`
* if `c` evaluates to a reference, its value can be modified by `c := c'` where `c'` evaluates to the new value.

#### Dynamic variables

Dynamic variables can be declared only at the top-level, by

    dynamic x = c

where `c` evaluates to the initial value.
The current value is accessed with simply `x`.

Dynamic variables can be updated by the following construct:

    now x = c in c'

Here `x` will evaluate to the result of `c` when it is used in `c'`, including through
function application and operation handling

    let f _ = x in
    now x = v in f ()

and

    handle
      now x = v in getx
    with
      getx => yield x
    end

both evaluate to `v` regardless of the previous value of `x`.

##### `#include_once "<file>"`

Include the given file if it has not been included yet.

##### `verbosity <n>`

Set the verbosity level. The levels are:

- `0`: only success messages
- `1`: errors
- `2`: warnings
- `3`: debugging messages


### Judgment computations

There is no way in Andromeda to create a bare type-theoretic term $\e$, only a complete
typing judgment $\isterm{\G}{\e}{\T}$. Even those computations that *look* like terms
actually compute judgments. For instance, if `c₁` computes to

$$\isterm{\G}{\e_1}{\Prod{\x}{\T} \U}$$

and `c₂` computes to

$$\isterm{\D}{\e_2}{\T},$$

then the "application" `c₁ c₂` computes to

$$\isterm{\G \bowtie \D}{\app{\e_1}{\x}{\T}{\U}{\e_2}}{\subst{\U}{\x}{\e_2}}$$

where $\G \bowtie \D$ is the *join* of contexts $\G$ and $\D$, satisfying the property
that $\G \bowtie \D$ contains both $\G$ and $\D$ (the two contexts $\G$ and $\D$ may be
incompatible, in which case Andromeda reports an error).

Even though Andromeda always computes an entire judgment $\isterm{\G}{\e}{\T}$ it is
useful to think of it as just a term $\e$ with a known type $\T$ and assumptions $\G$
which Andromeda is kindly keeping track of.

##### Infering and checking mode

A judgment is computed in one of two modes, the **inferring** or the **checking** mode.

In the inferring mode the judgment that is being computed is unrestrained.

In checking mode there is a given type $\T$ (actually a judgment $\istype{\G}{\T}$) and
the judgment that is being computed must have the form $\isterm{\D}{\e}{\T}$. In other
words, the type is prescribed in advanced. For example, an application

    c₁ c₂

proceeds as follows:

1. Compute `c₁` in inferring mode to obtain a judgment $\isterm{\G}{\e}{\T}$.
2. Verify that $\T$ is equal to $\Prod{x}{\T_1}{\T_2}$, using `as_prod` if necessary (see [equality checking](#equality-checking)).
3. Compute `c₂` in checking mode at type $\T_1$.


#### The universe

The computation

    Type

computes the judgment $\istype{}{\Type}$ which is valid by [the rule `ty-type`](type-theory.html#ty-type). Example:

    # do Type
    ⊢ Type : Type

Having `Type` in `Type` is unsatisfactory because it renders the type theory inconsistent
in the sense that every type is inhabited. We consider this to be a temporary feature of
the system that simplifies development. In the future there will be a (user-definable)
universe mechanism.

#### Constants

At the toplevel a new constant `a` (axiom) of type `A` may be declared with

    constant a : A

Several constants of the same type may be declared with

    constant a₁ a₂ ... aᵢ : A

A primitive type `T` is declared with

    constant T : Type

#### Assumptions

If computation `c₁` computes to judgment $\istype{\G}{\T}$ then

    assume x : c₁ in c₂

binds `x` to $\isterm{\ctxextend{\G}{\x'}{\T}}{\x'}{\T}$,
then it evaluates `c₂`. The judgment is valid by
[rule `ctx-var`](type-theory.html#term-var) and
[rule `ctx-extend`](type-theory.html#ctx-extend). Example:

    # constant A : Type
    Constant A is declared.
    # constant B : A → Type
    Constant B is declared.
    # do assume a : A in B a
    a₁₁ : A ⊢ B a₁₁ : Type

The judgment that was generated is $\istype{a_{11} \colon
A}{\app{B}{x}{A}{\Type}{a_{11}}}$, but Andromeda is not showing the typing annotations.
Every time `assume` is evaluated it generates a fresh variable $\x'$ that has never been seen before:

    # do assume a : A in B a
    a₁₂ : A ⊢ B a₁₂ : Type
    # do assume x : A in B a
    a₁₃ : A ⊢ B a₁₃ : Type

If we make several assumptions but then use only some of them, the context will contain those that are actually needed:

    # constant A : Type
    Constant A is declared.
    # constant f : A → A → A
    Constant f is declared.
    # do assume a : A in (assume b : A in (assume c : A in f a c))
    a₁₄ : A, c₁₆ : A ⊢ f a₁₄ c₁₆ : A

#### Substitution

We can get rid of an assumption with a *substitution*

    c₁ where x = c₂

which replaces in `c₁` the assumption bound to `x` with the judgment that computed by
`c₂`, as follows:

    # constant A : Type
    Constant A is declared.
    # constant a : A
    Constant a is declared.
    # constant f : A → A
    Constant f is declared.
    # let x = (assume x : A in x)
    x is defined.
    # do x
    x₁₂ : A ⊢ x₁₂ : A
    # let b = f x
    b is defined.
    # do b
    x₁₂ : A ⊢ f x₁₂ : A
    # do b where x = a
    ⊢ f a : A

The idiom `let x = assume x : A in x` is a common one and it serves as a way of
introducing a new fresh variable of a given type. There is no reason to use `x` both in
`let` and in `assume`, we could write `let z = assume y : A in y` but then `z` would be
bound to something like `y₄₂` which is perhaps a bit counter-intuitive.

If we compute a term without first storing the assumed variables

    # let d = assume y : A in f y
    d is defined.
    # do d
    y₁₃ : A ⊢ f y₁₃ : A

then it is a bit harder to get our hands on `y₁₃`, but is still doable using `context`,
see below.

#### Product

A product is computed with

    ∏ (x : c₁), c₂

An iterated product may be computed with

    ∏ (x₁₁ ... x₁ⱼ : c₁) ... (xᵢ₁ .... xᵢⱼ : cᵢ), c

Instead of the character `∏` you may also use `Π`, `∀` or `forall`.

A non-dependent product is written as

    c₁ → c₂

The arrow `→` associates to the right so that `c₁ → c₂ → c₃` is equivalent to `c₁ → (c₂ →
c₃)`. Instead of `→` you can also write `->`.

#### λ-abstraction

A λ-abstraction is computed with

    λ (x : c₁), c₂

An iterated λ-abstraction is computed with

    λ (x₁₁ ... x₁ⱼ : c₁) ... (xᵢ₁ .... xᵢⱼ : cᵢ), c

In checking mode the types of the bound variables may be omitted, so we can write

    λ x₁ x₂ ... xᵢ, c

We can also mix bound variables with and without typing annotations.

Instead of the character `λ` you may use `lambda`.

#### Application

An application is computed with

    c₁ c₂

Application associates to the left so that `c₁ c₂ c₃` is the same as `(c₁ c₂) c₃`.

#### Equality type

The equality type is computed with

    c₁ ≡ c₂

Instead of the character `≡` you may use `==`.

#### Reflexivity

The reflexivity term is computed with

    refl c

#### Equality checking

TODO: describe how equality checking works by invocation of operations

##### Congruences

TODO: Describe `congruence`

##### Extensionality

TODO: Describe `extensionality`

##### Reduction

TODO: Describe `reduction`

##### Operations invoked by the nucleus

TODO: describe `equal`, `as_prod` and `as_eq`.


#### Type ascription

Type ascription

    c₁ : c₂

first computes `c₂`, which must evaluate to a type $\istype{\G}{\T}$. It then computes
`c₁` in checking mode at type $\T$ thereby guaranteeing that the result will be a judgment
of the form $\isterm{\D}{\e}{\T}$.

#### Context and occurs check

The computation

    context c

computes `c` to a judgment $\isterm{\G}{\e}{\T}$ and gives the list of all assumptions in
$\Gamma$. Example:

    # constant A : Type
    Constant A is declared.
    # constant f : A -> A -> Type
    Constant f is declared.
    # let b = assume x : A in assume y : A in f x y
    b is defined.
    # do context b
    [(y₁₃ : A ⊢ y₁₃ : A), (x₁₂ : A ⊢ x₁₂ : A)]

The computation

    occurs x c

computes `x` to a judgment $\isterm{\D}{\x}{A}$ and `c` to a judgment $\isterm{\G}{\e}{\T}$ such that $x$ is a variable.
It evaluates to `None` if $x$ does not occur in $\G$, and to
`Some U` if $x$ occurs in $\G$ as an assumption of type `U`.

    # constant A : Type
    Constant A is declared.
    # constant f : A -> A -> A
    Constant f is declared.
    # let x = assume x : A in x
    x is defined.
    # do occurs x (f x x)
    Some (⊢ A : Type)
    # do occurs x f
    None

#### Hypotheses

In AML computations happen *inside* products and λ-abstractions, i.e., under binders.
It is sometimes important to get the list of the binders.
This is done with

    hypotheses

Example:

    # constant A : Type
    Constant A is declared.
    # constant F : A → Type
    Constant F is declared.
    # do ∏ (a : A), F ((λ (x : A), (print hypotheses; x)) a)
    [(x₁₄ : A ⊢ x₁₄ : A), (a₁₃ : A ⊢ a₁₃ : A)]
    ⊢ Π (a : A), F ((λ (x : A), x) a) : Type

Here `hypotheses` returned the list `[(x₁₄ : A ⊢ x₁₄ : A), (a₁₃ : A ⊢ a₁₃ : A)]` which was printed, after which `⊢ Π (a : A), F ((λ (x : A), x) a) : Type` was computed as the result.

The handling of operations invoked under a binder is considered to be computed under that binder:

    # do handle ∏ (a : A), Hole with Hole => hypotheses end
    [(a₁₃ : A ⊢ a₁₃ : A)]

#### Externals

Externals provide a way to call certain Ocaml functions.
Each function has a name like `"print"` and is invoked with

    external "print"

The name `print` is bound to the external `"print"` in the standard library.

The available externals are:

   |---|---|
   | `"print"` | A function taking one value and printing it to the standard output |
   | `"time"` | TODO describe time |
   | `"config"` | A function allowing dynamic modification of some options |
   | `"exit"` | Exit Andromeda ML |

The `"config"` external can be invoked with the following options:

   |---|---|
   | `"ascii"` | Future printing only uses ASCII characters |
   | `"no-ascii"` | Future printing uses UTF-8 characters such as `∏` (default) |
   | `"debruijn"` | Print De Bruijn indices of bound variables in terms |
   | `"no-debruijn"` | Do not print De Bruijn indices of bound variables in terms (default) |
   | `"annotate"` | Print typing annotations (partially implemented) |
   | `"no-annotate"` | Do not print typing annotations (default) |
   | `"dependencies"` | Print dependency information in contexts and terms |
   | `"no-dependencies"` | Do not print dependency information |
    
The arguments to `external` and `external "config"` are case sensitive.


#### Toplevel commands

An andromeda program is a stream of top-level commands.

##### Toplevel let binding

The top-level can bind variables to values and define recursive functions like inside computations:

    let x = c
    and y = c'

and

    let rec f x = c
    and g y = c'

##### Toplevel dynamic variables

The top-level can create new dynamic variables

    dynamic x = c

and update them for the rest of the program

    now x = c

##### Declarations

The top-level can create new basic values:
* type theoretic constants as `constant a b : T`
* type theoretic signatures as `signature s = { foo as x : Type, bar : x }`
* operations of given arities as `operation hippy 0`
* data constructors of given arities as `data Some 1`

##### Do command

At the toplevel the `do c` construct computes `c`:

    do c

You *cannot* just write `c` because that would create ambiguities. For instance,

    let x = c₁
    c₂

could mean `let x = c₁ c₂` or

    let x = c₁
    do c₂

We could do without `do` if we requires that toplevel computations be terminated with `;;`
a la OCaml. We do not have a strong opinion about this particular syntactic detail.

##### Fail command

The construct

    fail c

is the "opposite" of `do c` in the sense that it will succeed *only if* `c` reports an
error. This is useful for testing AML.

If `c` has side effects they are cancelled:

    # let x = ref None
    x is defined.
    # fail x := Some (); None None
    The command failed with error:
    File "?", line 2, characters 20-23: Runtime error
      cannot apply a data tag
    # do !x
    None

##### Toplevel handlers

A global handler may be installed at the toplevel with

    handle
    | op-case₁
    | op-case₂
    ...
    | op-caseᵢ
    end

Top-level handlers may only be simple callbacks: the cases may not contain patterns
(to avoid confusion, as new cases replace old ones completely)
and for case `op ?x => c`, `yield` may not appear in `c`. Instead the result of `c` is passed to the continuation.

Thus a top-level operation case `op ?x => c` is equivalent to a general handler case `op ?x => yield c`.

##### Include

`#include "<file>"` includes the given file.

`#include_once "<file>"` includes the given file if it has not been included yet.

The path is relative to the current file.

##### Verbosity

`#verbosity <n>` sets the verbosity level. The levels are:

- `0`: only success messages
- `1`: errors
- `2`: warnings
- `3`: debugging messages

##### Help

`#help` prints the internal help.

##### Environment

`#environment` prints information about the runtime environment.

##### Quit

`#quit` ends evaluation.

