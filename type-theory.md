---
title: Type theory with equality reflection
layout: page
navigation: type-theory
use_math: true
---

## Type theory with equality reflection

We give here the rules of type theory that is implemented in Andromeda. The rules are
simplified with respect to the implementation in the following ways:

1. In Andromeda each subexpression carries an explicit set of variables on which it
   depends. We call these *assumptions tags*. This is necessary to recover the
   strengthening rule (because of equality reflection it may happen that the
   well-formedness of a term relies on an assumption which is not recorded in the term).

2. The typing context is not a list but rather a directed graph whose vertices are the
   context entries and whose edges are dependencies between context entries (they edges
   are recoverable from the assumption tags).

3. The actual rules implemented by the nucleus perform a *context join*. This is best
   illustrated with an example. The introduction rule for equality types
   [`ty-eq`](#ty-eq) is here stated as

   $$
   \infer
   {\istype{\G}{\tyA} \qquad
    \isterm{\G}{\e_1}{\tyA} \qquad
    \isterm{\G}{\e_2}{\tyA}
   }
   {\istype{\G}{\JuEqual{\tyA}{\e_1}{\e_2}}}
   $$

   but is implemented as

   $$
   \infer
   {\istype{\G}{\tyA} \qquad
    \isterm{\D}{\e_1}{\tyA} \qquad
    \isterm{\Xi}{\e_2}{\tyA}
   }
   {\istype{(\G \bowtie \D \bowtie \Xi)}{\JuEqual{\tyA}{\e_1}{\e_2}}}
   $$

   where the *join* $\G \bowtie \D$ is computed as the union of (directed graphs
   representing) context $\G$ and $\D$. The join operation may fail if there is
   a variable appears in $\G$ and $\D$ with different types.

   TODO: Explain precisely how the context joins work and what properties
   they have.

Unlike in traditional type theory the terms are explicitly tagged with typing information.
For instance, a $\lambda$-abstraction is tagged with both the doman and the codomain.

### Syntax

Terms $\e$ and types $\tyA$, $\tyB$:

|---|---|
| $\Type$ | universe |
| $\Prod{x}{\tyA} \tyB$ | product |
| $\JuEqual{\tyA}{\e_1}{\e_2}$ | equality type |
| $\x$ | variable |
| $\lam{\x}{\tyA}{\tyB} \e$ | $\lambda$-abstraction |
| $\app{\e_1}{\x}{\tyA}{\tyB}{\e_2}$ | application |
| $\juRefl{\tyA} \e$ | reflexivity |

Contexts $\G$:

|---|---|
| $\ctxempty$ | empty context |
| $\ctxextend{\G}{\x}{\tyA}$ | context $\G$ extended with $\x : \tyA$ |

### Judgments

|---|---|
| $\isctx{\G}$          | $\G$ is a well formed context |
| $\isterm{\G}{\e}{\tyA}$ | $\e$ is a well formed term of type $\tyA$ in context $\G$ |
| $\eqterm{\G}{\e_1}{\e_2}{\tyA}$ | $e_1$ and $e_2$ are equal terms of type $\tyA$ in context |
| $\eqctx{\G}{\D}$      | $\G$ and $\D$ are equal contexts |

### Judgment: $\isctx{\G}$

###### `ctx-empty`

$$
  \infer
  { }
  {\isctx{\ctxempty}}
$$

###### `ctx-extend`

$$
  \infer
  {\isctx{\G} \qquad
   \istype{\G}{\tyA} \qquad
   x \not\in \mathsf{dom}(\G)
  }
  {\isctx{\ctxextend{\G}{\x}{\tyA}}}
$$

Here $\mathsf{dom}(\G)$ is the set of all variables that are declared in $\G$, i.e.:

$$
\mathsf{dom}(\ctxempty) = \emptyset
\qquad\text{and}\qquad
\mathsf{dom}(\ctxextend{\G}{\x}{\tyA}) = \mathsf{dom}(\G) \cup \{x\}.
$$

### Judgment: $\eqctx{\G}{\D}$

###### `eq-ctx-empty`

$$
  \infer
  { }
  {\eqctx{\ctxempty}{\ctxempty}}
$$

###### `eq-ctx-extend`

$$
  \infer
  {\begin{aligned}[t]
   &\eqctx{\G}{\D} \qquad
   x \not\in \mathsf{dom}(\G) \cup \mathsf{dom}(\D) \\
   &
   \istype{\G}{\tyA} \qquad
   \istype{\D}{\tyB}
   \end{aligned}}
  {\eqctx{\ctxextend{\G}{\x}{\tyA}}{\ctxextend{\D}{\x}{\tyB}}}
$$

###### `ctx-term-conv`

$$
  \infer
  {\eqctx{\G}{\D} \qquad
   \isterm{\G}{\e}{\tyA}}
  {\isterm{\D}{\e}{\tyA}}
$$

###### `ctx-eq-conv`

$$
  \infer
  {\eqctx{\G}{\D} \qquad
   \eqterm{\G}{\e_1}{\e_2}{\tyA}}
  {\eqterm{\D}{\e_1}{\e_2}{\tyA}}
$$

### Judgment: $\isterm{\G}{\e}{\tyA}$

#### General rules

###### `term-conv`

$$
  \infer
  {\isterm{\G}{\e}{\tyA} \qquad
   \eqtype{\G}{\tyA}{\tyB}
  }
  {\isterm{\G}{\e}{\tyB}}
$$

###### `term-var`

$$
  \infer
  {\isctx{\G} \qquad
   (\x{:}\tyA) \in \G
  }
  {\isterm{\G}{\x}{\tyA}}
$$

#### Universe

###### `ty-type`

$$
  \infer
  {\isctx{\G}
  }
  {\istype{\G}{\Type}}
$$

#### Products

###### `ty-prod`

$$\infer
  {\istype{\G}{\tyA} \qquad
   \istype{\ctxextend{\G}{\x}{\tyA}}{\tyB}
  }
  {\istype{\G}{\Prod{\x}{\tyA}{\tyB}}}
$$

###### `term-abs`

$$\infer
  {\isterm{\ctxextend{\G}{\x}{\tyA}}{\e}{\tyB}}
  {\isterm{\G}{(\lam{\x}{\tyA}{\tyB}{\e})}{\Prod{\x}{\tyA}{\tyB}}}
$$

###### `term-app`

$$\infer
  {\isterm{\G}{\e_1}{\Prod{x}{\tyA} \tyB} \qquad
   \isterm{\G}{\e_2}{\tyA}
  }
  {\isterm{\G}{\app{\e_1}{\x}{\tyA}{\tyB}{\e_2}}{\subst{\tyB}{\x}{\e_2}}}
$$

#### Equality type

###### `ty-eq`

$$
  \infer
  {\istype{\G}{\tyA} \qquad
   \isterm{\G}{\e_1}{\tyA} \qquad
   \isterm{\G}{\e_2}{\tyA}
  }
  {\istype{\G}{\JuEqual{\tyA}{\e_1}{\e_2}}}
$$

###### `term-refl`

$$\infer
  {\isterm{\G}{\e}{\tyA}}
  {\isterm{\G}{\juRefl{\tyA} \e}{\JuEqual{\tyA}{\e}{\e}}}
$$

### Equality

#### General rules

###### `eq-refl`

$$  \infer
  {\isterm{\G}{\e}{\tyA}}
  {\eqterm{\G}{\e}{\e}{\tyA}}
$$

###### `eq-sym`

$$\infer
  {\eqterm{\G}{\e_2}{\e_1}{\tyA}}
  {\eqterm{\G}{\e_1}{\e_2}{\tyA}}
$$

###### `eq-trans`

$$\infer
  {\eqterm{\G}{\e_1}{\e_2}{\tyA}\qquad
   \eqterm{\G}{\e_2}{\e_3}{\tyA}}
  {\eqterm{\G}{\e_1}{\e_3}{\tyA}}
$$

###### `eq-conv`

$$\infer
  {\eqterm{\G}{\e_1}{\e_2}{\tyA}\qquad
    \eqtype{\G}{\tyA}{\tyB}}
  {\eqterm{\G}{\e_1}{\e_2}{\tyB}}
$$

Remark: in the presence of `eq-reflection` (see below) the rules `eq-conv`,
`eq-sym` and `eq-trans` are derivable using `term-conv` and congruence rules.

#### Computations

###### `prod-beta`

$$
\infer
  {\isterm{\ctxextend{\G}{\x}{\tyA}}{\e_1}{\tyB}\qquad
   \isterm{\G}{\e_2}{\tyA}}
  {\eqterm{\G}{\bigl(\app{(\lam{\x}{\tyA}{\tyB}{\e_1})}{\x}{\tyA}{\tyB}{\e_2}\bigr)}
              {\subst{\e_1}{\x}{\e_2}}
              {\subst{\tyB}{\x}{\e_2}}}
$$

#### Reflection and extensionality

###### `eq-reflection`

$$
  \infer
  {\isterm{\G}{\e}{\JuEqual{\tyA}{\e_1}{\e_2}}}
  {\eqterm{\G}{\e_1}{\e_2}{\tyA}}
$$

###### `eq-ext`

$$\infer
  {\isterm{\G}{\e_3}{\JuEqual{\tyA}{\e_1}{\e_2}} \qquad
    \isterm{\G}{\e_4}{\JuEqual{\tyA}{\e_1}{\e_2}}
  }
  {\eqterm{\G}{\e_3}{e_4}{\JuEqual{\tyA}{\e_1}{\e_2}}}
$$

###### `prod-ext`

$$\infer
  {\begin{aligned}[t]
   &\isterm{\G}{\e_1}{\Prod{\x}{\tyA}{\tyB}}\qquad
    \isterm{\G}{\e_2}{\Prod{\x}{\tyA}{\tyB}}\\
   &\eqterm{\ctxextend{\G}{\x}{\tyA}}{(\app{\e_1}{\x}{\tyA}{\tyB}{\x})}
          {(\app{\e_2}{\x}{\tyA}{\tyB}{\x})}{\tyB}
  \end{aligned}
  }
  {\eqterm{\G}{\e_1}{\e_2}{\Prod{\x}{\tyA}{\tyB}}}
$$

#### Congruences

##### Type formers

###### `congr-prod`

$$\infer
  {\eqtype{\G}{\tyA_1}{\tyB_1}\qquad
   \eqtype{\ctxextend{\G}{\x}{\tyA_1}}{\tyA_2}{\tyB_2}}
  {\eqtype{\G}{\Prod{\x}{\tyA_1}{\tyA_2}}{\Prod{\x}{\tyB_1}{\tyB_2}}}
$$

###### `congr-eq`

$$
  \infer
  {\eqtype{\G}{\tyA}{\tyB}\qquad
   \eqterm{\G}{\e_1}{\e'_1}{\tyA}\qquad
   \eqterm{\G}{\e_2}{\e'_2}{\tyA}
  }
  {\eqtype{\G}{\JuEqual{\tyA}{\e_1}{\e_2}}
              {\JuEqual{\tyB}{\e'_1}{\e'_2}}}
$$

##### Products

###### `congr-lambda`

$$
  \infer
  {\eqtype{\G}{\tyA_1}{\tyB_1}\qquad
    \eqtype{\ctxextend{\G}{\x}{\tyA_1}}{\tyA_2}{\tyB_2}\qquad
    \eqterm{\ctxextend{\G}{\x}{\tyA_1}}{\e_1}{\e_2}{\tyA_2}}
  {\eqterm{\G}{(\lam{\x}{\tyA_1}{\tyA_2}{\e_1})}
              {(\lam{\x}{\tyB_1}{\tyB_2}{\e_2})}
              {\Prod{\x}{\tyA_1}{\tyA_2}}}
$$

###### `congr-apply`

$$
  \infer
  {\begin{aligned}[t]
   &\eqtype{\G}{\tyA_1}{\tyB_1}\qquad
    \eqtype{\ctxextend{\G}{\x}{\tyA_1}}{\tyA_2}{\tyB_2}\\
   &\eqterm{\G}{\e_1}{\e'_1}{\Prod{\x}{\tyA_1}{\tyA_2}}\qquad
    \eqterm{\G}{\e_2}{\e'_2}{\tyA_1}
   \end{aligned}}
{\eqterm{\G}{(\app{\e_1}{\x}{\tyA_1}{\tyA_2}{\e_2})}{(\app{\e'_1}{\x}{\tyB_1}{\tyB_2}{\e'_2})}{\subst{\tyA_2}{\x}{\e_2}}}
$$

##### Equality types

###### `congr-refl`

$$
\infer
{\eqterm{\G}{\e_1}{\e_2}{\tyA}\qquad
 \eqtype{\G}{\tyA}{\tyB}}
{\eqterm{\G}{\juRefl{\tyA} \e_1}{\juRefl{\tyB} \e_2}{\JuEqual{\tyA}{\e_1}{\e_1}}}
$$

TODO: Substitution.

