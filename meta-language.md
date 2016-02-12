---
title: The Andromeda meta-language
navigation: meta-language
layout: page
---

### About the Andromeda meta-language

Andromeda is in essence a programming languge following the tradition of Robin Milner's
[Logic for computable
functions](http://i.stanford.edu/pub/cstr/reports/cs/tr/72/288/CS-TR-72-288.pdf) (LCF)
programming. We call it the **Andromeda meta-language** or **Andromeda ML**. (Yes, the ML
family of programming languages originates from Robin Milner's LCF).

A basic feature of the language is that it allows us to compute typing judgements of the
form `Γ ⊢ e : A` – but only the ones that are *derivable* in the underlying
[type theory](type-theory.html). This is known as the *soundness* of ML. *Completeness* of
ML states that every derivable judgement may be computed in ML. Neither property has
actually been proved yet for Andromeda ML. We are working on it.

At present Andromeda ML is dynamically typed. We are planning to put some types on it.

While Robin Milner's LCF and its HOL-style descendants implement simple type theory,
Andromeda ML implements dependent type theory. This creates a significant overhead in the
complexity and so while [John Harisson](http://www.cl.cam.ac.uk/~jrh13/) is able to print
the [HOL Light kernel](http://www.cl.cam.ac.uk/~jrh13/) is able to print the
[HOL Light kernel]() on a T-shirt, it may take a superhero's cape to print the 4000 lines
of [Andromeda nucleus](https://en.wikipedia.org/wiki/Andromeda_Galaxy#Nucleus).

### The syntax of Andromeda ML

Here we shall describe the Andromeda ML informally.
