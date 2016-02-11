---
title: Type theory with equality reflection
layout: page
navigation: type-theory
use_math: true
---

## Type theory with equality reflection

### Syntax

Contexts:

$$
\G
  \begin{aligned}[t]
    \bnf   {}& \ctxempty & & \text{empty context}\\
    \bnfor {}& \ctxextend{\G}{\x}{\T} & & \text{context $\G$ extended with $\x : \T$}
  \end{aligned}
$$

Terms and types:

$$
  \e, \T, \U
  \begin{aligned}[t]
    \bnf   {}& \Type & & \text{universe}\\
    \bnfor {}& \Prod{x}{\T} \U & & \text{product}\\
    \bnfor {}& \JuEqual{\T}{\e_1}{\e_2} & & \text{equality type} \\
    \bnfor {}&  \x   &&\text{variable} \\
    \bnfor {}&  \lam{\x}{\T_1}{\T_2} \e  &&\text{$\lambda$-abstraction} \\
    \bnfor {}&  \app{\e_1}{\x}{\T_1}{\T_2}{\e_2}  &&\text{application} \\
    \bnfor {}&  \juRefl{\T} \e  &&\text{reflexivity} \\
  \end{aligned}
$$

### Judgements

$$
\begin{aligned}[t]
& \isctx{\G} & & \text{$\G$ is a well formed context} \\
& \isterm{\G}{\e}{\T} & & \text{$\e$ is a well formed term of type $\T$ in context $\G$} \\
& \eqterm{\G}{\e_1}{\e_2}{\T} & & \text{$e_1$ and $e_2$ are equal terms of type $\T$ in context $\G$}
\end{aligned}
$$

### Judgement $\isctx{\G}$

Rule `ctx-empty`:

$$
  \infer
  { }
  {\isctx{\ctxempty}}
$$

Rule `ctx-extend`:

$$
  \infer
  {\isctx{\G} \qquad
   \istype{\G}{\T} \qquad
   x \not\in \mathsf{dom}(\G)
  }
  {\isctx{\ctxextend{\G}{\x}{\T}}}
$$

TODO: explain $\mathsf{dom}(\G)$.

### Judgement $\isterm{\G}{\e}{\T}$

#### General rules

Rule `term-conv`

$$
  \infer
  {\isterm{\G}{\e}{\T} \qquad
   \eqtype{\G}{\T}{\U}
  }
  {\isterm{\G}{\e}{\U}}
$$

Rule `term-var`:

$$
  \infer
  {\isctx{\G} \qquad
   (\x{:}\T) \in \G
  }
  {\isterm{\G}{\x}{\T}}
$$

#### Universe

Rule `ty-type`:

$$
  \infer
  {\isctx{\G}
  }
  {\istype{\G}{\Type}}
$$

#### Products

Rule `ty-prod`:

$$\infer
  {\istype{\G}{\T} \qquad
   \istype{\ctxextend{\G}{\x}{\T}}{\U}
  }
  {\istype{\G}{\Prod{\x}{\T}{\U}}}
$$

Rule `term-abs`:

$$\infer
  {\isterm{\ctxextend{\G}{\x}{\T}}{\e}{\U}}
  {\isterm{\G}{(\lam{\x}{\T}{\U}{\e})}{\Prod{\x}{\T}{\U}}}
$$

Rule `term-app`:

$$\infer
  {\isterm{\G}{\e_1}{\Prod{x}{\T} \U} \qquad
   \isterm{\G}{\e_2}{\T}
  }
  {\isterm{\G}{\app{\e_1}{\x}{\T}{\U}{\e_2}}{\subst{\U}{\x}{\e_2}}}
$$

#### Equality type

Rule `ty-eq`:

$$
  \infer
  {\istype{\G}{\T} \qquad
   \isterm{\G}{\e_1}{\T} \qquad
   \isterm{\G}{\e_2}{\T}
  }
  {\istype{\G}{\JuEqual{\T}{\e_1}{\e_2}}}
$$

Rule `term-refl`:

$$\infer
  {\isterm{\G}{\e}{\T}}
  {\isterm{\G}{\juRefl{\T} \e}{\JuEqual{\T}{\e}{\e}}}
$$

### Equality

#### General rules

Rule `eq-refl`:

$$  \infer
  {\isterm{\G}{\e}{\T}}
  {\eqterm{\G}{\e}{\e}{\T}}
$$

Rule `eq-sym`:

$$\infer
  {\eqterm{\G}{\e_2}{\e_1}{\T}}
  {\eqterm{\G}{\e_1}{\e_2}{\T}}
$$

Rule `eq-trans`:

$$\infer
  {\eqterm{\G}{\e_1}{\e_2}{\T}\qquad
   \eqterm{\G}{\e_2}{\e_3}{\T}}
  {\eqterm{\G}{\e_1}{\e_3}{\T}}
$$

Rule `eq-conv`:

$$\infer
  {\eqterm{\G}{\e_1}{\e_2}{\T}\qquad
    \eqtype{\G}{\T}{\U}}
  {\eqterm{\G}{\e_1}{\e_2}{\U}}
$$

Remark: in the presence of `eq-reflection` (see below) the rules `eq-conv`,
`eq-sym` and `eq-trans` are derivable using `term-conv` and congruence rules.

#### Equality reflection

Rule `eq-reflection`:

$$
  \infer
  {\isterm{\G}{\e}{\JuEqual{\T}{\e_1}{\e_2}}}
  {\eqterm{\G}{\e_1}{\e_2}{\T}}
$$

#### Computations

Rule `prod-beta`:

$$
\infer
  {\isterm{\ctxextend{\G}{\x}{\T_1}}{\e_1}{\T_2}\qquad
   \isterm{\G}{\e_2}{\T_1}}
  {\eqterm{\G}{\bigl(\app{(\lam{\x}{\T_1}{\T_2}{\e_1})}{\x}{\T_1}{\T_2}{\e_2}\bigr)}
              {\subst{\e_1}{\x}{\e_2}}
              {\subst{\T_2}{\x}{\e_2}}}
$$

#### Extensionality

Rule `eq-eta`:

$$\infer
  {\isterm{\G}{\e_3}{\JuEqual{\T}{\e_1}{\e_2}} \qquad
    \isterm{\G}{\e_4}{\JuEqual{\T}{\e_1}{\e_2}}
  }
  {\eqterm{\G}{\e_3}{e_4}{\JuEqual{\T}{\e_1}{\e_2}}}
$$

Rule `prod-eta`:

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

Rule `cong-prod`:

$$\infer
  {\eqtype{\G}{\T_1}{\U_1}\qquad
   \eqtype{\ctxextend{\G}{\x}{\T_1}}{\T_2}{\U_2}}
  {\eqtype{\G}{\Prod{\x}{\T_1}{\T_2}}{\Prod{\x}{\U_1}{\U_2}}}
$$

Rule `cong-eq`:

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

Rule `cong-abs`:

$$
  \infer
  {\eqtype{\G}{\T_1}{\U_1}\qquad
    \eqtype{\ctxextend{\G}{\x}{\T_1}}{\T_2}{\U_2}\qquad
    \eqterm{\ctxextend{\G}{\x}{\T_1}}{\e_1}{\e_2}{\T_2}}
  {\eqterm{\G}{(\lam{\x}{\T_1}{\T_2}{\e_1})}
              {(\lam{\x}{\U_1}{\U_2}{\e_2})}
              {\Prod{\x}{\T_1}{\T_2}}}
$$

Rule `cong-app`:

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

Rule `cong-refl`:

$$
\infer
{\eqterm{\G}{\e_1}{\e_2}{\T}\qquad
 \eqtype{\G}{\T}{\U}}
{\eqterm{\G}{\juRefl{\T} \e_1}{\juRefl{\U} \e_2}{\JuEqual{\T}{\e_1}{\e_1}}}
$$

TODO: Substitution.

