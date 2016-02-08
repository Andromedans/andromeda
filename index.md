---
title: Andromeda proof assistant
navigation: about
layout: page
---

Andromeda is an implementation of dependent type theory with equality reflection. Thanks
to the equality reflection the type theory is very expressive, as it allows one to postulate
new judgmental equalities.

The design of Andromeda is much closer to
[HOL Light](http://www.cl.cam.ac.uk/~jrh13/hol-light/) than to [Coq](https://coq.inria.fr)
or [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php) in the sense that its nucleus
(galaxies do not have "kernels") is minimalistic: it does not perform any normalization
because the underlying type theory has no normal forms. Instead, equality checking is
delegated to the meta-language. The nucleus and the meta-language communicate through
operations and handlers akin to those of the
[Eff programming language](http://www.eff-lang.org). Andromeda is safe by design as the
meta-language can only create typing judgements by passing through the nucleus.

### Theoretical background

Documents: see the
[documents folder](https://github.com/Andromedans/andromeda/tree/master/doc) in the GitHub
repository.

Talks:

* Andrej Bauer: "How to implemenent type theory with a reflection rule"
  ([slides](http://www.qmac.ox.ac.uk/events/Talk%20slides/Bauer-HoTT-Oxford.pdf) and
   [video](https://www.youtube.com/watch?v=IlfQjWqrK6I))
* Andrej Bauer: ["The troublesome reflection rule"](http://math.andrej.com/2015/05/19/the-troublesome-reflection-rule-types-2015-slides/), TYPES 2015, invited talk.


### History of the name

Andromeda used to be called Brazil, as a consequence of discussions at the Institute for
Advanced Study where we talked about "sending proofs to a far away place where they will
check them independently". We thought of Brazil as a faraway place, but it later turned
out it was not quite far enough. We hope that nobody will claim that the Andromeda galaxy
is a nearby place.

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
