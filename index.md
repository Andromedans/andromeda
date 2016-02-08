---
title: Andromeda proof assistant
navigation: about
layout: page
---

Andromeda is an experimental implementation of dependent type theory with a reflection rule.
For theoretical background see:

* Andrej Bauer: "How to implemenent type theory with a reflection rule"
  ([slides](http://www.qmac.ox.ac.uk/events/Talk%20slides/Bauer-HoTT-Oxford.pdf) and
   [video](https://www.youtube.com/watch?v=IlfQjWqrK6I))

The reflection rule allows us to do many things, such as add new computation rules for new
type formers, and hopefully also provide support for Vladimir Voevodsky's
[Homotopy Type System](http://ncatlab.org/homotopytypetheory/show/Homotopy+Type+System)
which has *two* kinds of equality, one of which has a reflection rule.


### History of the name Andromeda

Andromeda used to be called Brazil, as a consequence of discussions at the Institute for
Advanced Study where we talked about "sending proofs to a far away place where they will
check them independently". We thought of Brazil as a faraway place, but it later turned
out it was not quite far enough. We hope that nobody will claim that the Andromeda galaxy
is a nearby place.

### Travis Continuous Integration

The GitHub repository is linked to Travis CI. To find out the current build status is
displayed here:

  [![Build Status](https://api.travis-ci.org/Andromedans/andromeda.png?branch=master)](https://travis-ci.org/Andromedans/andromeda)


