---
title: Andromeda proof assistant
navigation: Q & A
andromeda_version: 2
layout: page
---

### Questions from the ICFP 2019 sli.do (2019-08-21)

Here are some answers to questions asked on sli.do that were not taken care of
during the Q&A session. Please ask more if these answers (or questions) do not
satisfy you.

##### Anonymous (9:33 AM):

> If the goal is expiermenting with theories, why impose so many restrictions (MLTT, Tarski, eg), rather than a purely syntactic DSL ala Redex or Turnstile.

A: We have meta-theorems such as presuppositionality, inversion, and
admissibility of substitution, and good programmatic support for the class of
type theories we picked.

##### Anonymous (9:57 AM):

> Will you support transport of terms between user-defined type theories?

A: This is the PhD subject of [Anja Petković](https://anjapetkovic.com), so yes,
exciting future work!

##### Anonymous (9:47 AM):

> Can I add guards to the inference rules? In what language do I express them?

A: Not yet. We have plans to add guards by attaching to a rule a piece of code
from the meta-language.

##### Anonymous (9:51 AM):

> Is it fair to say that Andromeda's nucleus is more like the kernel of HOL4/HOLlight than like Coq/Agda/Lean?

A: Yes, that's fair to say. One similarity in particular is that there is no
normalisation or unification in the nucleus.

##### Anonymous (9:17 AM):

> Not convinced by the "no commitment" criterion; I don't think it can be made technically precise. Can you capture more objectively what you want to rule out?

A: We do not want to restrict ourselves to working inside a particular logical
framework.

##### Anonymous (9:54 AM):

> How fast does an Andromeda implementation of a theory run vs a typical hand-rolled implementation?

A: We don't know. Certainly we are not trying to compete with say computation
in Coq. Rather, we are interested in type theories which don't come equipped
with a clear and efficient, or really any mode of computation.


##### Christian Graulund (9:55 AM):

> How user definable is the type theory? Can I have say Fitch-style contexts or a context split regions?

A: The main restrictions at the moment are the commitment to the four fixed
judgement forms, and intuitionistic contexts.

##### Anonymous (9:56 AM):

> You can parameterize on how to introduce equality. Can you also parameterize on how to destruct it, or is it fixed (by rewriting)?

A: There is no commitment as to how equality judgements are used. For example,
the user can implement rewriting along a judgemental equality `Γ,Δ ⊢ s == t : A` by using
congrunce rules to get to a sub-component of a judgement `Γ ⊢ J[s]` and replace
`s` by `t`. This mechanism is not baked into the system, but user programmable.


##### Jeremy Gibbons (9:44 AM):

> Slide 23: do "evaluate : source -> T judgement" functions compose? It's not much of a PL if not!

A: We are not aiming to do meta-programming for our flavour of ML. The
programs that compute judgements compose.

##### Anonymous (9:55 AM):

> "User land is untrusted" except for where the user defines their type theory, which is trusted?

A: Trust here simply means that a value of meta-language type `judgement`
indeed is derivable in the user-defined type theory. The methodology of using
an abstract type and an interface of smart constructors for this type was
pioneered by Milner et al., following suggestions by Hoare.

Users are certainly free to define type theories that are, say, logically
inconsistent. But the user code cannot break the abstraction provided by the
nucleus and the meta language, and thus need not to be trusted.

##### Anonymous (9:55 AM):

> Many type theories contain rule-defining rules, eg for new datatypes. Can these be supported?

A: Type theories such as the Calculus of Inductive Constructions have schemata
for rules. We do not currently support schemata. Other approaches, such as
using an inductive-recursive universe to represent codes for inductive types
can be readily formulated in Andromeda.

##### Anonymous (9:58 AM):

> Can one implement CIC in Andromeda?

A: No, because we do not support the schemata for inductive types (see previous
question). You can get [CC](https://github.com/Andromedans/andromeda/blob/master/theories/calculus_of_constructions.m31).
