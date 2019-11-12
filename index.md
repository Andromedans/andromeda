---
title: Andromeda proof assistant
navigation: Andromeda 2
andromeda_version: 2
layout: page
---

### ICFP 2019 material

* [abstract, keynote slides (pdf), and demo file](http://math.andrej.com/2019/08/21/derivations-as-computations/)
* [some answers to *sli.do* questions](answers.html)

### Introduction

Information about the old Andromeda 1, an implementation of type theory with
equality reflection, is available [*here*](v1/index.html).

Andromeda 2 is currently under active development. Until better documentation
will be available, the best way to learn about Andromeda 2 is by consulting the
code examples found in
[theories subdirectory](https://github.com/Andromedans/andromeda/tree/master/theories)
and the [tests subdirectory](https://github.com/Andromedans/andromeda/tree/master/tests).

The design of Andromeda follows the tradition of
[LCF](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions)-style theorem provers:

* there is an abstract datatype of judgements,
* all constructions of judgements are done by a trusted *nucleus* and directly correspond
  to the application of inference rules of type theory,
* the user interacts with the nucleus by writing programs in a high-level, statically
  typed meta-language *Andromeda ML (AML)*.

The nucleus does not perform any normalization (it cannot as the underlying type theory
has no normal forms), unification, or perform proof search. These techniques can all be
implemented on top of the nucleus in AML, and therefore cannot compute underivable
judgments by design. Of course, they could fail or run forever because AML is a
general-purpose programming language.


### History of the name

Andromeda used to be called Brazil, as a consequence of discussions at the Institute for
Advanced Study where we talked about "sending proofs to a far away place where they will
check them independently". We thought of Brazil as a faraway place, but it later turned
out it was not quite far enough. Martin Escardó suggested the name Andromeda. We hope that
nobody will claim that our neighboring galaxy is a nearby place.

### Developers

* [Andrej Bauer](http://andrej.com/)
* [Gaëtan Gilbert](https://github.com/SkySkimmer)
* [Philipp G. Haselwarter](https://www.haselwarter.org/~philipp/)
* [Anja Petković](https://anjapetkovic.com/)
* [Matija Pretnar](http://matija.pretnar.info/)
* [Chris Stone](https://www.cs.hmc.edu/~stone/)


### Travis Continuous Integration

The GitHub repository is linked to Travis CI. The current build status:

[![Build Status](https://api.travis-ci.org/Andromedans/andromeda.png?branch=master)](https://travis-ci.org/Andromedans/andromeda)

### Support

This material is based upon work supported by the Air Force Office of Scientific Research,
Air Force Materiel Command, USAF under Award No. FA9550-14-1-0096. Any opinions, findings,
and conclusions or recommendations expressed in this publication are those of the
author(s) and do not necessarily reflect the views of the Air Force Office of Scientific
Research, Air Force Materiel Command, USAF.
