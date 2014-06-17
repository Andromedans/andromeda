[![Build Status](https://api.travis-ci.org/andrejbauer/tt.png?branch=master)](https://travis-ci.org/andrejbauer/tt)

A minimalist implementation of type theory in Ocaml. The repository holds
several branches which correspond to a series of blog posts about
dependent type theory on the [Mathematics and Computation](http://math.andrej.com/) blog.

The code is currently undergoing active development. We are modifying it so that it will
support Voevodsky's two-level type system HTS in which judgmental equalities are present
as types. We are using algebraic effects and handlers on top of type theory to mange the
judgmental equalities.
