---
title: Type theory with equality reflection
layout: page
navigation: type-theory
use_math: true
---

## Type theory with equality reflection

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


### Judgment $\isctx{\G}$

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

TODO: explain $\mathsf{dom}(\G)$.

### Judgment $\isterm{\G}{\e}{\T}$

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

