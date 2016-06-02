---
title: Andromeda proof assistant
navigation: about
layout: page
---

Andromeda is an implementation of dependent type theory with equality reflection. The type
theory is very expressive, as it allows one to postulate new judgmental equalities.

The design of Andromeda follows the tradition of
[LCF](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions)-style theorem provers:

* there is an abstract datatype of judgments,
* all constructions of judgments are done by a trusted *nucleus* and directly correspond
  to the inference rules of type theory (or derivations thereof),
* the user interacts with the nucleus by writing programs in a high-level, statically
  typed meta-language [*Andromeda ML (AML)*](meta-language.html).

The nucleus does not perform any normalization (it cannot as the underlying type theory
has no normal forms), unification, or perform proof search. These techniques can all be
implemented on top of the nucleus in AML, and therefore cannot compute underivable
judgments by design. Of course, they could fail or run forever because AML is a
general-purpose programming language.

Equality checking is delegated to the meta-level by a mechanism of operations and handlers
akin to those of the [Eff programming language](http://www.eff-lang.org). Whenever the
nucleus needs to check a non-trivial equation, it triggers an operation (question) which
propagates to the meta-level. There it is intercepted by a user-defined handler which
handles (answers) the equation by providing a witness for it.

### Theoretical background

Documents: see the
[documents folder](https://github.com/Andromedans/andromeda/tree/master/doc) in the GitHub
repository.



### History of the name

Andromeda used to be called Brazil, as a consequence of discussions at the Institute for
Advanced Study where we talked about "sending proofs to a far away place where they will
check them independently". We thought of Brazil as a faraway place, but it later turned
out it was not quite far enough. Martin Escardó suggested the name Andromeda. We hope that
nobody will claim that our neighboring galaxy is a nearby place.

### Developers

* [Andrej Bauer](http://andrej.com/)
* [Gaëtan Gilbert](https://github.com/SkySkimmer)
* [Philipp Haselwarter](https://www.haselwarter.org/~philipp/)
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
