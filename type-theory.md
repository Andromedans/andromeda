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
   {\istype{\G}{\T} \qquad
    \isterm{\G}{\e_1}{\T} \qquad
    \isterm{\G}{\e_2}{\T}
   }
   {\istype{\G}{\JuEqual{\T}{\e_1}{\e_2}}}
   $$

   but is implemented as

   $$
   \infer
   {\istype{\G}{\T} \qquad
    \isterm{\D}{\e_1}{\T} \qquad
    \isterm{\Xi}{\e_2}{\T}
   }
   {\istype{(\G \bowtie \D \bowtie \Xi)}{\JuEqual{\T}{\e_1}{\e_2}}}
   $$

   where the *join* $\G \bowtie \D$ is computed as the union of (directed graphs
   representing) context $\G$ and $\D$. The join operation may fail if there is
   a variable appears in $\G$ and $\D$ with different types.

   TODO: Explain precisely how the context joins work and what properties
   they have.

Unlike in traditional type theory the terms are explicitly tagged with typing information.
For instance, a $\lambda$-abstraction is tagged with both the doman and the codomain.

### Syntax

Terms $\e$ and types $\T$, $\U$:

|---|---|
| $\Type$ | universe |
| $\Prod{x}{\T} \U$ | product |
| $\JuEqual{\T}{\e_1}{\e_2}$ | equality type |
| $\x$ | variable |
| $\lam{\x}{\T_1}{\T_2} \e$ | $\lambda$-abstraction |
| $\app{\e_1}{\x}{\T_1}{\T_2}{\e_2}$ | application |
| $\juRefl{\T} \e$ | reflexivity |

Contexts $\G$:

|---|---|
| $\ctxempty$ | empty context |
| $\ctxextend{\G}{\x}{\T}$ | context $\G$ extended with $\x : \T$ |

### Judgments

|---|---|
| $\isctx{\G}$          | $\G$ is a well formed context |
| $\isterm{\G}{\e}{\T}$ | $\e$ is a well formed term of type $\T$ in context $\G$ |
| $\eqterm{\G}{\e_1}{\e_2}{\T}$ | $e_1$ and $e_2$ are equal terms of type $\T$ in context |
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
   \istype{\G}{\T} \qquad
   x \not\in \mathsf{dom}(\G)
  }
  {\isctx{\ctxextend{\G}{\x}{\T}}}
$$

Here $\mathsf{dom}(\G)$ is the set of all variables that are declared in $\G$, i.e.:

$$
\mathsf{dom}(\ctxempty) = \emptyset
\qquad\text{and}\qquad
\mathsf{dom}(\ctxextend{\G}{\x}{\T}) = \mathsf{dom}(\G) \cup \{x\}.
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
   \istype{\G}{\T} \qquad
   \istype{\D}{\U}
   \end{aligned}}
  {\eqctx{\ctxextend{\G}{\x}{\T}}{\ctxextend{\D}{\x}{\U}}}
$$

###### `ctx-term-conv`

$$
  \infer
  {\eqctx{\G}{\D} \qquad
   \isterm{\G}{\e}{\T}}
  {\isterm{\D}{\e}{\T}}
$$

###### `ctx-eq-conv`

$$
  \infer
  {\eqctx{\G}{\D} \qquad
   \eqterm{\G}{\e_1}{\e_2}{\T}}
  {\eqterm{\D}{\e_1}{\e_2}{\T}}
$$

### Judgment: $\isterm{\G}{\e}{\T}$

#### General rules

###### `term-conv`

$$
  \infer
  {\isterm{\G}{\e}{\T} \qquad
   \eqtype{\G}{\T}{\U}
  }
  {\isterm{\G}{\e}{\U}}
$$

###### `term-var`

$$
  \infer
  {\isctx{\G} \qquad
   (\x{:}\T) \in \G
  }
  {\isterm{\G}{\x}{\T}}
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
  {\istype{\G}{\T} \qquad
   \istype{\ctxextend{\G}{\x}{\T}}{\U}
  }
  {\istype{\G}{\Prod{\x}{\T}{\U}}}
$$

###### `term-abs`

$$\infer
  {\isterm{\ctxextend{\G}{\x}{\T}}{\e}{\U}}
  {\isterm{\G}{(\lam{\x}{\T}{\U}{\e})}{\Prod{\x}{\T}{\U}}}
$$

###### `term-app`

$$\infer
  {\isterm{\G}{\e_1}{\Prod{x}{\T} \U} \qquad
   \isterm{\G}{\e_2}{\T}
  }
  {\isterm{\G}{\app{\e_1}{\x}{\T}{\U}{\e_2}}{\subst{\U}{\x}{\e_2}}}
$$

#### Equality type

###### `ty-eq`

$$
  \infer
  {\istype{\G}{\T} \qquad
   \isterm{\G}{\e_1}{\T} \qquad
   \isterm{\G}{\e_2}{\T}
  }
  {\istype{\G}{\JuEqual{\T}{\e_1}{\e_2}}}
$$

###### `term-refl`

$$\infer
  {\isterm{\G}{\e}{\T}}
  {\isterm{\G}{\juRefl{\T} \e}{\JuEqual{\T}{\e}{\e}}}
$$

### Equality

#### General rules

###### `eq-refl`

$$  \infer
  {\isterm{\G}{\e}{\T}}
  {\eqterm{\G}{\e}{\e}{\T}}
$$

###### `eq-sym`

$$\infer
  {\eqterm{\G}{\e_2}{\e_1}{\T}}
  {\eqterm{\G}{\e_1}{\e_2}{\T}}
$$

###### `eq-trans`

$$\infer
  {\eqterm{\G}{\e_1}{\e_2}{\T}\qquad
   \eqterm{\G}{\e_2}{\e_3}{\T}}
  {\eqterm{\G}{\e_1}{\e_3}{\T}}
$$

###### `eq-conv`

$$\infer
  {\eqterm{\G}{\e_1}{\e_2}{\T}\qquad
    \eqtype{\G}{\T}{\U}}
  {\eqterm{\G}{\e_1}{\e_2}{\U}}
$$

Remark: in the presence of `eq-reflection` (see below) the rules `eq-conv`,
`eq-sym` and `eq-trans` are derivable using `term-conv` and congruence rules.

#### Computations

###### `prod-beta`

$$
\infer
  {\isterm{\ctxextend{\G}{\x}{\T_1}}{\e_1}{\T_2}\qquad
   \isterm{\G}{\e_2}{\T_1}}
  {\eqterm{\G}{\bigl(\app{(\lam{\x}{\T_1}{\T_2}{\e_1})}{\x}{\T_1}{\T_2}{\e_2}\bigr)}
              {\subst{\e_1}{\x}{\e_2}}
              {\subst{\T_2}{\x}{\e_2}}}
$$

#### Reflection and extensionality

###### `eq-reflection`

$$
  \infer
  {\isterm{\G}{\e}{\JuEqual{\T}{\e_1}{\e_2}}}
  {\eqterm{\G}{\e_1}{\e_2}{\T}}
$$

###### `eq-ext`

$$\infer
  {\isterm{\G}{\e_3}{\JuEqual{\T}{\e_1}{\e_2}} \qquad
    \isterm{\G}{\e_4}{\JuEqual{\T}{\e_1}{\e_2}}
  }
  {\eqterm{\G}{\e_3}{e_4}{\JuEqual{\T}{\e_1}{\e_2}}}
$$

###### `prod-ext`

$$\infer
  {\begin{aligned}[t]
   &\isterm{\G}{\e_1}{\Prod{\x}{\T}{\U}}\qquad
    \isterm{\G}{\e_2}{\Prod{\x}{\T}{\U}}\\
   &\eqterm{\ctxextend{\G}{\x}{\T}}{(\app{\e_1}{\x}{\T}{\U}{\x})}
          {(\app{\e_2}{\x}{\T}{\U}{\x})}{\U}
  \end{aligned}
  }
  {\eqterm{\G}{\e_1}{\e_2}{\Prod{\x}{\T}{\U}}}
$$

#### Congruences

##### Type formers

###### `cong-prod`

$$\infer
  {\eqtype{\G}{\T_1}{\U_1}\qquad
   \eqtype{\ctxextend{\G}{\x}{\T_1}}{\T_2}{\U_2}}
  {\eqtype{\G}{\Prod{\x}{\T_1}{\T_2}}{\Prod{\x}{\U_1}{\U_2}}}
$$

###### `cong-eq`

$$
  \infer
  {\eqtype{\G}{\T}{\U}\qquad
   \eqterm{\G}{\e_1}{\e'_1}{\T}\qquad
   \eqterm{\G}{\e_2}{\e'_2}{\T}
  }
  {\eqtype{\G}{\JuEqual{\T}{\e_1}{\e_2}}
              {\JuEqual{\U}{\e'_1}{\e'_2}}}
$$

##### Products

###### `cong-abs`

$$
  \infer
  {\eqtype{\G}{\T_1}{\U_1}\qquad
    \eqtype{\ctxextend{\G}{\x}{\T_1}}{\T_2}{\U_2}\qquad
    \eqterm{\ctxextend{\G}{\x}{\T_1}}{\e_1}{\e_2}{\T_2}}
  {\eqterm{\G}{(\lam{\x}{\T_1}{\T_2}{\e_1})}
              {(\lam{\x}{\U_1}{\U_2}{\e_2})}
              {\Prod{\x}{\T_1}{\T_2}}}
$$

###### `cong-app`

$$
  \infer
  {\begin{aligned}[t]
   &\eqtype{\G}{\T_1}{\U_1}\qquad
    \eqtype{\ctxextend{\G}{\x}{\T_1}}{\T_2}{\U_2}\\
   &\eqterm{\G}{\e_1}{\e'_1}{\Prod{\x}{\T_1}{\T_2}}\qquad
    \eqterm{\G}{\e_2}{\e'_2}{\T_1}
   \end{aligned}}
{\eqterm{\G}{(\app{\e_1}{\x}{\T_1}{\T_2}{\e_2})}{(\app{\e'_1}{\x}{\U_1}{\U_2}{\e'_2})}{\subst{\T_2}{\x}{\e_2}}}
$$

##### Equality types

###### `cong-refl`

$$
\infer
{\eqterm{\G}{\e_1}{\e_2}{\T}\qquad
 \eqtype{\G}{\T}{\U}}
{\eqterm{\G}{\juRefl{\T} \e_1}{\juRefl{\U} \e_2}{\JuEqual{\T}{\e_1}{\e_1}}}
$$

TODO: Substitution.

