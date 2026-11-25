---
title: SVGD on a compact domain
subtitle: A Lean 4 formalization of Stein Variational Gradient Descent on a compact domain
abstract: >
  Stein Variational Gradient Descent (SVGD) moves a cloud of particles so that their distribution
  approaches a target distribution $\pi$. This formalization studies SVGD on a compact domain
  $\Omega \subseteq \mathbb{R}^d$, without any regularity of its boundary. It proves that the
  continuous-time dynamics of SVGD exists and keeps the particles in $\Omega$, that the
  Kullback–Leibler divergence to $\pi$ decreases along it at the rate of the kernelized Stein
  discrepancy, and that the dynamics converges weakly to $\pi$ when the kernel is Stein-universal.
  There is no `sorry`.
module: CompactSVGD.Paper
trusted:
  - CompactSVGD.Definitions
docgen: https://gaetanserre.fr/CompactSVGD/docs/
# The docgen of the project also documents Lean, Mathlib and the other dependencies, at their versions.
docgen_external: https://gaetanserre.fr/CompactSVGD/docs/
# The source links point to `<repository>/blob/<commit>/<file>#L<line>`. Without this line, the
# repository is the `origin` remote of git; the commit is the current one (`git rev-parse HEAD`).
repository: https://github.com/gaetanserre/CompactSVGD
bibliography: ../docs/references.bib
links:
  divergence: https://en.wikipedia.org/wiki/Divergence
  modulusOfContinuityOn: https://en.wikipedia.org/wiki/Modulus_of_continuity
  ODE.integralCurveThrough: https://en.wikipedia.org/wiki/Integral_curve
  SVGD.trajectory: https://en.wikipedia.org/wiki/Flow_(mathematics)
  ProbabilityTheory.steinOperator: https://en.wikipedia.org/wiki/Stein%27s_method
  SVGD.kernelSteinDiscrepancy: https://en.wikipedia.org/wiki/Stein_discrepancy
  SVGD.klFirstVariation: https://en.wikipedia.org/wiki/Kullback%E2%80%93Leibler_divergence
  SVGD.TargetAssumption: https://en.wikipedia.org/wiki/Probability_density_function
---

Stein Variational Gradient Descent (SVGD) [Liu2016SVGD] moves a cloud of particles so that their
distribution approaches a target distribution $\pi$. This page presents the theory of SVGD on a
compact domain $\Omega \subseteq \mathbb{R}^d$, as formalized in Lean. Each statement below is a
translation of the Lean statement. Each proof is given as a map of its arguments, or as one
sentence when it is short. The Lean statement and the Lean proof of each result can be unfolded
below it.

## Setting

Let $d \ge 1$ be the dimension. The space $\mathbb{R}^d$ has the Euclidean norm and its Borel
$\sigma$-algebra. Let $\lambda$ be the Lebesgue measure on $\mathbb{R}^d$. For $A \subseteq
\mathbb{R}^d$, let $A^\circ$ be its interior and $\partial A$ its boundary. For a measurable map
$T : \mathbb{R}^d \to \mathbb{R}^d$ and a measure $\rho$, let $T_\# \rho = \rho \circ T^{-1}$ be
the push-forward of $\rho$ by $T$.

Let $\mathcal{P}(\Omega)$ be the set of the probability measures $\rho$ on $\mathbb{R}^d$ such that
$\rho(\mathbb{R}^d \setminus \Omega) = 0$. We then say that $\rho$ is *carried by* $\Omega$. A
measure of $\mathcal{P}(\Omega)$ needs no density. The expectation $\mathbb{E}_{x \sim \rho}[g(x)]$
is the integral of $g$ against $\rho$. When $g$ takes its values in a Hilbert space, it is the
Bochner integral. In Lean, an integral is always defined, with the value $0$ when the function is
not integrable.

Let $E$ and $F$ be real normed spaces. Let $E^*$ be the space of continuous linear forms on $E$,
with the operator norm. For $g : E \to F$ differentiable at $x$, let $Dg(x)$ be its derivative at
$x$. For a vector field $v : E \to E$, let $\operatorname{div} v(x) = \operatorname{tr} Dv(x)$ be its
[divergence](#divergence).

The target distribution $\pi$ has a density $p$ with respect to the Lebesgue measure on $\Omega$,
and a score $s$ that plays the role of $\nabla \log p$.

{{SVGD.TargetAssumption | Assumption 1}}

```informal SVGD.TargetAssumption | Target distribution
Let $\Omega \subseteq \mathbb{R}^d$, let $\pi$ be a measure on $\mathbb{R}^d$, let
$p : \mathbb{R}^d \to \mathbb{R}$ and let $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$. The target
distribution $\pi$ satisfies Assumption 1 with density $p$ and score $s$ if
$$\forall A \subseteq \mathbb{R}^d \text{ Borel}, \quad \pi(A) = \int_{A \cap \Omega} \max(p, 0) \, d\lambda,$$
and if the following conditions hold.

(i) $\pi$ is a probability measure.

(ii) $p$ is measurable and continuous on $\Omega$, and $p(x) > 0$ for every $x \in \Omega$.

(iii) For every $x \in \Omega^\circ$, $\log p$ is differentiable at $x$ and $D(\log p)(x) = s(x)$.

(iv) $s$ is continuous on $\Omega$.

By (ii), $\max(p, 0) = p$ on $\Omega$. By (iii), $s = \nabla \log p$ on $\Omega^\circ$. No
regularity of $\partial \Omega$ is assumed.
```

For instance, the Boltzmann distribution $p = e^{-\kappa f} / Z$ of a continuously differentiable
function $f$, restricted to a compact set of positive measure, satisfies Assumption 1 with
$s = -\kappa Df$. A measure at finite Kullback–Leibler divergence from $\pi$ is carried by $\Omega$.

{{SVGD.TargetAssumption.ae_mem_of_klDiv_ne_top | Property}}

```informal SVGD.TargetAssumption.ae_mem_of_klDiv_ne_top | Finite divergence implies support in $\Omega$
Suppose that Assumption 1 holds and that $\Omega$ is measurable. Let $\rho$ be a measure on
$\mathbb{R}^d$ such that $\mathrm{KL}(\rho \,\|\, \pi) < \infty$. Then,
$\rho(\mathbb{R}^d \setminus \Omega) = 0$.
```

```sketch SVGD.TargetAssumption.ae_mem_of_klDiv_ne_top
As $\mathrm{KL}(\rho \,\|\, \pi) < \infty$, $\rho \ll \pi$, and $\pi(\mathbb{R}^d \setminus \Omega) = 0$.
```

## Stein's method

SVGD is based on Stein's method [Stein1972]. We first define the Stein operator. Then, we show that
Stein's identity holds for the target distribution, for the vector fields that vanish on
$\partial \Omega$, without any assumption on $\partial \Omega$. To do so, we compute the first
variation of the Kullback–Leibler divergence. This computation is also the basis of SVGD, and the
template of the time derivative of the Kullback–Leibler divergence along the dynamics.

### The Stein operator

{{ProbabilityTheory.steinOperator | Definition 1}}

```informal ProbabilityTheory.steinOperator | Stein operator
Let $E$ be a real normed space and let $s : E \to E^*$. The Stein operator of score $s$ maps a
vector field $v : E \to E$ to the function $\mathcal{A}_s v : E \to \mathbb{R}$ defined by
$$\mathcal{A}_s v(x) = s(x)(v(x)) + \operatorname{div} v(x).$$
It is meant for a finite-dimensional space $E$ and for the points $x$ where $v$ is differentiable.
```

When $s = \nabla \log p$ for a positive differentiable density $p$, we have that
$\mathcal{A}_s v = \nabla \log p^\top v + \operatorname{div} v$. This is the Stein operator of $p$
[Liu2016]. As $Dp = p s$, we have that $\operatorname{div}(p v) = p \, \mathcal{A}_s v$. Stein's
identity states that $\mathcal{A}_s v$ has mean zero under $p$. It classically follows from the
divergence theorem, which requires a regular boundary. Here, the boundary of $\Omega$ is arbitrary.
However, for the vector fields that vanish on $\partial \Omega$, Stein's identity still holds. Its
proof relies on the first variation of the Kullback–Leibler divergence.

### First variation of the Kullback–Leibler divergence

Let $\rho$ and $\rho'$ be probability measures on $\mathbb{R}^d$. The Kullback–Leibler divergence
of $\rho$ with respect to $\rho'$ is
$$\mathrm{KL}(\rho \,\|\, \rho') = \int \log \frac{d\rho}{d\rho'} \, d\rho$$
if $\rho \ll \rho'$ and this logarithm is $\rho$-integrable, and $\mathrm{KL}(\rho \,\|\, \rho') =
\infty$ otherwise. A small perturbation of the identity by a vector field that vanishes on
$\partial \Omega$ maps $\Omega$ onto itself (see the figure below). Let $I_d$ be the identity map of
$\mathbb{R}^d$.

```figure
figures/perturbation_a.svg | $v = u$
figures/perturbation_b.svg | $v = \min(1, \operatorname{dist}(\cdot, \partial \Omega) / \delta) \, u$
Transport of a grid of particles by $I_d + \varepsilon v$, with $d = 2$ and $\varepsilon = 0.06$.
The set $\Omega = \{(x, y) \in \mathbb{R}^2 \mid y^2 \le x^3, \ x^2 + y^2 \le 1\}$ is in gray. Its
boundary has a cusp at $0$ and two corners, where it has no outward normal. The field
$u = (\partial_y \chi, -\partial_x \chi)$ has two counter-rotating vortices, with
$\chi(z) = e^{-\|z - p_1\|^2 / \sigma^2} - e^{-\|z - p_2\|^2 / \sigma^2}$, $p_1 = (0.5, 0.3)$,
$p_2 = (0.5, -0.3)$ and $\sigma = 0.6$. Each arrow goes from a particle $x$ to $x + \varepsilon v(x)$.
**a)** The field $v = u$ does not vanish on $\partial \Omega$. The red particles cross
$\partial \Omega$. **b)** The field $v$ is equal to $u$ at distance at least $\delta = 0.2$ from
$\partial \Omega$, and vanishes on $\partial \Omega$. As $\varepsilon K_v < 1$, each arrow is shorter
than the distance from its particle to $\partial \Omega$, so no particle crosses $\partial \Omega$.
This illustrates [Lemma 1 (ii)](#SVGD.perturbations_of_identity_image).
```

{{SVGD.perturbations_of_identity_isHomeomorph | Lemma 1 (i)}}

```informal SVGD.perturbations_of_identity_isHomeomorph | Perturbations of the identity
Let $v : \mathbb{R}^d \to \mathbb{R}^d$ be $K_v$-Lipschitz, and let $\varepsilon \in \mathbb{R}$
such that $|\varepsilon| K_v < 1$. Then, $\Psi = I_d + \varepsilon v$ is a homeomorphism of
$\mathbb{R}^d$.
```

```sketch SVGD.perturbations_of_identity_isHomeomorph
For every $y$, the map $x \mapsto y - \varepsilon v(x)$ is a contraction, whose fixed point is
$\Psi^{-1}(y)$. Tau Ceti proves it in `LipschitzWith.idAddHomeomorph`.
```

{{SVGD.perturbations_of_identity_image | Lemma 1 (ii)}}

```informal SVGD.perturbations_of_identity_image | Perturbations of the identity preserve $\Omega$
Let $\Omega \subseteq \mathbb{R}^d$. Let $v : \mathbb{R}^d \to \mathbb{R}^d$ be $K_v$-Lipschitz,
with $v(y) = 0$ for every $y \in \partial \Omega$. Let $\varepsilon \in \mathbb{R}$ such that
$|\varepsilon| K_v < 1$, and let $\Psi = I_d + \varepsilon v$. Then, $\Psi(\Omega) = \Omega$.
```

```diagram SVGD.perturbations_of_identity_image
bij: `SVGD.perturbations_of_identity_isHomeomorph`
  $\Psi_\tau = I_d + \tau \varepsilon v$ is a bijection, for $\tau \in [0, 1]$
rest: step
  $\Psi_\tau(z) = z$ for $z \in \partial \Omega$
  > As $v$ vanishes on $\partial \Omega$, the points of $\partial \Omega$ do not move.
avoid: step <- bij, rest
  if $x \notin \partial \Omega$, the path $\tau \mapsto \Psi_\tau(x)$ avoids $\partial \Omega$
  > As $\Psi_\tau$ is injective and fixes the points of $\partial \Omega$, $\Psi_\tau(x) \neq z$ for every $z \in \partial \Omega$.
conn: Connected sets and frontiers `IsPreconnected.inter_frontier_nonempty` <- avoid
  $x \in \Omega \iff \Psi(x) \in \Omega$
  > If a connected set meets both $\Omega$ and $\mathbb{R}^d \setminus \Omega$, then it meets $\partial \Omega$. The path $\{\Psi_\tau(x) \mid \tau \in [0, 1]\}$ is connected, contains $x = \Psi_0(x)$ and $\Psi(x) = \Psi_1(x)$, and does not meet $\partial \Omega$. Thus, $x$ and $\Psi(x)$ are both in $\Omega$ or both outside $\Omega$. If $x \in \partial \Omega$, then $\Psi(x) = x$.
goal <- conn, bij
  $\Psi(\Omega) = \Omega$
  > $\Psi$ maps $\Omega$ and its complement into themselves. As $\Psi$ is a bijection, $\Psi(\Omega) = \Omega$.
```

{{SVGD.perturbations_of_identity_image_interior | Lemma 1 (iii)}}

```informal SVGD.perturbations_of_identity_image_interior | Perturbations of the identity preserve $\Omega^\circ$
Under the assumptions of [Lemma 1 (ii)](#SVGD.perturbations_of_identity_image),
$\Psi(\Omega^\circ) = \Omega^\circ$.
```

```sketch SVGD.perturbations_of_identity_image_interior
The argument of [Lemma 1 (ii)](#SVGD.perturbations_of_identity_image) also shows that the path
$\tau \mapsto \Psi_\tau(x)$ stays in $\Omega^\circ$ when $x \in \Omega^\circ$.
```

The next lemma expresses the Kullback–Leibler divergence of a transported measure.

{{SVGD.transport_kl_ne_top | Lemma 2 (i)}}

```informal SVGD.transport_kl_ne_top | Transport of the Kullback–Leibler divergence
Suppose that $\Omega$ is compact and that Assumption 1 holds. Let $\Psi$ be a homeomorphism of
$\mathbb{R}^d$, differentiable at every point of $\Omega$, such that $\Psi(\Omega) = \Omega$ and
$\det D\Psi(x) > 0$ for every $x \in \Omega$. Let $\rho$ be a probability measure on
$\mathbb{R}^d$ such that $\mathrm{KL}(\rho \,\|\, \pi) < \infty$ and $\log \det D\Psi$ is
$\rho$-integrable. Then, $\mathrm{KL}(\Psi_\# \rho \,\|\, \pi) < \infty$.
```

```sketch SVGD.transport_kl_ne_top
This is the finiteness part of the computation of [Lemma 2 (ii)](#SVGD.transport_kl).
```

{{SVGD.transport_kl | Lemma 2 (ii)}}

```informal SVGD.transport_kl | Transport of the Kullback–Leibler divergence
Under the assumptions of [Lemma 2 (i)](#SVGD.transport_kl_ne_top),
$$\mathrm{KL}(\Psi_\# \rho \,\|\, \pi) = \mathrm{KL}(\rho \,\|\, \pi) - \int \big(\log p(\Psi(x)) - \log p(x) + \log \det D\Psi(x)\big) \, d\rho(x).$$
```

```diagram SVGD.transport_kl
inv: Invariance under a bijection `MeasurableEquiv.klDiv_map_left`
  $\mathrm{KL}(\Psi_\# \rho \,\|\, \pi) = \mathrm{KL}(\rho \,\|\, \Psi^{-1}_\# \pi)$
  > The Kullback–Leibler divergence is invariant when both measures are transported by the same measurable bijection.
cov: Change of variables `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` [Fremlin2010]
  $\Psi^{-1}_\# \pi = q \cdot \pi$, where $q = (p \circ \Psi) \det D\Psi / p$ on $\Omega$
  > Let $A$ be a Borel set. As $\Psi(\Omega) = \Omega$ and $\pi$ is carried by $\Omega$, $\Psi^{-1}_\# \pi(A) = \pi(\Psi(A \cap \Omega))$. The change of variables formula on $\Omega$ then gives the density $q$. It only requires $\Psi$ to be injective and differentiable on $\Omega$.
rew: Change of reference measure `InformationTheory.toReal_klDiv_withDensity_ofReal_right` <- inv, cov
  $\mathrm{KL}(\rho \,\|\, q \cdot \pi) = \mathrm{KL}(\rho \,\|\, \pi) - \mathbb{E}_{x \sim \rho}[\log q(x)]$
  > As $q > 0$ on $\Omega$, $\log \frac{d\rho}{d(q \cdot \pi)} = \log \frac{d\rho}{d\pi} - \log q$. The function $\log q$ is $\rho$-integrable, as $\log p$ is bounded on the compact set $\Omega$ and $\log \det D\Psi$ is $\rho$-integrable.
goal <- rew
```

We can now differentiate the Kullback–Leibler divergence along a perturbation of the identity. Its
derivative at the identity is the *first variation* of the Kullback–Leibler divergence.

{{SVGD.first_variation_integrable | Theorem 1 (i)}}

```informal SVGD.first_variation_integrable | First variation of the Kullback–Leibler divergence
Suppose that $\Omega$ is compact and that Assumption 1 holds. Let
$v : \mathbb{R}^d \to \mathbb{R}^d$ be continuously differentiable and $K_v$-Lipschitz, with
$v(y) = 0$ for every $y \in \partial \Omega$. Let $\rho$ be a probability measure on
$\mathbb{R}^d$ such that $\mathrm{KL}(\rho \,\|\, \pi) < \infty$. Then, $\mathcal{A}_s v$ is
$\rho$-integrable.
```

```sketch SVGD.first_variation_integrable
$\mathcal{A}_s v$ is continuous on the compact set $\Omega$, which carries $\rho$ by the
[Property](#SVGD.TargetAssumption.ae_mem_of_klDiv_ne_top) of Assumption 1.
```

{{SVGD.first_variation_ne_top | Theorem 1 (ii)}}

```informal SVGD.first_variation_ne_top | First variation of the Kullback–Leibler divergence
Under the assumptions of [Theorem 1 (i)](#SVGD.first_variation_integrable), there exists
$\varepsilon_0 > 0$ such that
$$\forall \varepsilon \in (-\varepsilon_0, \varepsilon_0), \quad \mathrm{KL}\big((I_d + \varepsilon v)_\# \rho \,\|\, \pi\big) < \infty.$$
```

```sketch SVGD.first_variation_ne_top
For $\varepsilon$ small, $\det(I_d + \varepsilon Dv) \ge 1/2$ on $\Omega$, and
[Lemma 1](#SVGD.perturbations_of_identity_image) and [Lemma 2 (i)](#SVGD.transport_kl_ne_top)
apply to $\Psi = I_d + \varepsilon v$.
```

{{SVGD.first_variation | Theorem 1 (iii)}}

```informal SVGD.first_variation | First variation of the Kullback–Leibler divergence
Under the assumptions of [Theorem 1 (i)](#SVGD.first_variation_integrable), the function
$h : \varepsilon \mapsto \mathrm{KL}((I_d + \varepsilon v)_\# \rho \,\|\, \pi)$ is differentiable at
$0$, and
$$h'(0) = -\mathbb{E}_{x \sim \rho}[\mathcal{A}_s v(x)].$$
```

```diagram SVGD.first_variation
L1: `SVGD.perturbations_of_identity_image`
  $\Psi_\varepsilon = I_d + \varepsilon v$ maps $\Omega$ and $\Omega^\circ$ onto themselves
det: step
  $\det(I_d + \varepsilon Dv(x)) \ge 1/2$ on $\Omega$, for $|\varepsilon| < \varepsilon_0$
  > $Dv(\Omega)$ is compact, and $(\tau, A) \mapsto \det(I_d + \tau A)$ is continuous and equal to $1$ at $\tau = 0$.
L2: `SVGD.transport_kl` <- L1, det
  $h(\varepsilon) = \mathrm{KL}(\rho \,\|\, \pi) - \mathbb{E}_{x \sim \rho}[\ell(\varepsilon, x)]$
  > Here, $\ell(\varepsilon, x) = \log p(x + \varepsilon v(x)) - \log p(x) + \log \det(I_d + \varepsilon Dv(x))$.
der: step <- L1
  $\partial_\varepsilon \ell(\varepsilon, x)$, by the chain rule
  > We have that $$\partial_\varepsilon \ell(\varepsilon, x) = s(x + \varepsilon v(x))(v(x)) + \frac{D\det(I_d + \varepsilon Dv(x))(Dv(x))}{\det(I_d + \varepsilon Dv(x))}.$$ On $\Omega^\circ$, which $\Psi_\varepsilon$ preserves, this follows from the chain rule and (iii) of Assumption 1. On $\partial \Omega$, $v = 0$ and both sides vanish.
bound: step <- der, det
  $|\partial_\varepsilon \ell(\varepsilon, x)| \le M_s M_v + 2M$
  > $M_s$ and $M_v$ are the maxima of $\|s\|$ and $\|v\|$ on $\Omega$, and $M$ bounds the derivative of the determinant. They are finite by continuity on compact sets.
leib: Leibniz integral rule `hasDerivAt_integral_of_dominated_loc_of_deriv_le` [Folland1999] <- L2, bound
  $h'(0) = -\mathbb{E}_{x \sim \rho}[\partial_\varepsilon \ell(0, x)]$
  > Differentiation under the integral sign, with a derivative dominated by an integrable constant.
jac: Jacobi's formula `hasDerivAt_det_id_add_smul_zero`
  $\frac{d}{d\varepsilon} \det(I_d + \varepsilon A) \big|_{\varepsilon = 0} = \operatorname{tr} A$
goal <- leib, jac
  $h'(0) = -\mathbb{E}_{x \sim \rho}[\mathcal{A}_s v(x)]$
  > At $\varepsilon = 0$, $\partial_\varepsilon \ell(0, x) = s(x)(v(x)) + \operatorname{tr} Dv(x) = \mathcal{A}_s v(x)$.
```

Stein's identity for the target distribution follows, as the Kullback–Leibler divergence is
minimal at $\pi$.

{{SVGD.stein_identity_integrable | Corollary 1 (i)}}

```informal SVGD.stein_identity_integrable | Stein's identity for the target distribution
Suppose that $\Omega$ is compact and that Assumption 1 holds. Let
$v : \mathbb{R}^d \to \mathbb{R}^d$ be continuously differentiable and Lipschitz, with $v(y) = 0$
for every $y \in \partial \Omega$. Then, $\mathcal{A}_s v$ is $\pi$-integrable.
```

```sketch SVGD.stein_identity_integrable
[Theorem 1 (i)](#SVGD.first_variation_integrable) with $\rho = \pi$, as
$\mathrm{KL}(\pi \,\|\, \pi) = 0$.
```

{{SVGD.stein_identity | Corollary 1 (ii)}}

```informal SVGD.stein_identity | Stein's identity for the target distribution
Under the assumptions of [Corollary 1 (i)](#SVGD.stein_identity_integrable),
$$\mathbb{E}_{x \sim \pi}[\mathcal{A}_s v(x)] = 0.$$
```

```diagram SVGD.stein_identity
T1: `SVGD.first_variation`
  $h'(0) = -\mathbb{E}_{x \sim \pi}[\mathcal{A}_s v(x)]$, with $\rho = \pi$
  > Here, $h(\varepsilon) = \mathrm{KL}((I_d + \varepsilon v)_\# \pi \,\|\, \pi)$.
min: step
  $h \ge 0 = h(0)$
  > The Kullback–Leibler divergence is nonnegative, and $\mathrm{KL}(\pi \,\|\, \pi) = 0$.
fermat: Fermat's theorem `IsLocalMin.hasDerivAt_eq_zero` <- T1, min
  $h'(0) = 0$
  > A differentiable function has a zero derivative at a local minimum.
goal <- fermat
```

Thus, every continuously differentiable and Lipschitz vector field that vanishes on
$\partial \Omega$ satisfies Stein's identity for $\pi$. The boundary is handled by the vector field
itself. For another measure $\rho$, the mean $\mathbb{E}_{x \sim \rho}[\mathcal{A}_s v(x)]$ is no
longer zero in general. The Stein discrepancy [Gorham2015] measures how much $\rho$ violates Stein's
identity, over a set $\mathcal{F}$ of such vector fields, i.e.
$$\mathbb{S}(\rho, \pi) = \sup_{v \in \mathcal{F}} \mathbb{E}_{x \sim \rho}[\mathcal{A}_s v(x)].$$
When $\mathcal{F}$ is the unit ball of a space of vector fields given by a kernel, its square has a
closed form [Liu2016]. This is the kernelized Stein discrepancy.

## The kernelized Stein discrepancy

### The kernel

In SVGD [Liu2016SVGD], the vector fields lie in a product of reproducing kernel Hilbert spaces
(RKHS). Here, the kernel is only given by a feature map $\Phi$, with values in a real inner product
space $H_0$, which need not be an RKHS.

{{SVGD.KernelAssumption | Assumption 2}}

```informal SVGD.KernelAssumption | Kernel
Let $H_0$ be a real inner product space, let $\Phi : \mathbb{R}^d \to H_0$, let
$\Omega \subseteq \mathbb{R}^d$ and let $K, C \ge 0$. The kernel is
$k(x, y) = \langle \Phi(x), \Phi(y) \rangle_{H_0}$, and it satisfies Assumption 2 if the following
conditions hold.

(i) $\Phi$ is continuously differentiable on $\mathbb{R}^d$.

(ii) $\Phi$ is $K$-Lipschitz.

(iii) $\|\Phi(y)\|_{H_0} \le C$ for every $y \in \mathbb{R}^d$.

(iv) $\Phi(y) = 0$ for every $y \in \partial \Omega$.
```

Let $\mathcal{H} = H_0^d$ be the space of the $d$-tuples $f = (f_1, \dots, f_d)$ of elements of $H_0$,
with $\langle f, g \rangle_{\mathcal{H}} = \sum_{i=1}^d \langle f_i, g_i \rangle_{H_0}$. An element
$f \in \mathcal{H}$ is not a vector field by itself. It defines one through the feature map, i.e.
$$f_\Phi(y) = \big(\langle f_1, \Phi(y) \rangle_{H_0}, \dots, \langle f_d, \Phi(y) \rangle_{H_0}\big).$$
Each coordinate of $f_\Phi$ is a linear model in the features. We have that $f_\Phi = P_f \circ
\Phi$, where $P_f$ is the [pairing](#SVGD.pairing) $u \mapsto (\langle f_i, u \rangle_{H_0})_i$. By
the Cauchy–Schwarz inequality, $\|P_f\| \le \|f\|_{\mathcal{H}}$. Thus, by Assumption 2, $f_\Phi$ is
continuously differentiable, $\|f\|_{\mathcal{H}} K$-Lipschitz, bounded by $\|f\|_{\mathcal{H}} C$,
and zero on $\partial \Omega$. Theorem 1 and Corollary 1 apply to it.

When $H_0$ is the RKHS of a kernel $k_0$ and $\Phi(y) = k_0(\cdot, y)$, the reproducing property
gives $f_\Phi = f$. Conversely, $H_0$ need not be the RKHS of $k$. Translation-invariant kernels,
such as the Gaussian kernel, do not satisfy (iv). Weighted kernels $w(x) w(y) k_0(x, y)$, where $w$
vanishes on $\partial \Omega$, satisfy it, with $\Phi = w \Phi_0$.

{{SVGD.StandingAssumptions | Assumptions}}

```informal SVGD.StandingAssumptions | The standing assumptions
$\Omega \subseteq \mathbb{R}^d$ is compact, the target distribution $\pi$ satisfies Assumption 1
with density $p$ and score $s$, and the feature map $\Phi$ satisfies Assumption 2 with constants
$K$ and $C$.
```

Most results below take the standing assumptions. Some of them also assume that $H_0$ is complete,
i.e. a Hilbert space. Then, so is $\mathcal{H}$.

### Definition of the kernelized Stein discrepancy

The kernelized Stein discrepancy is the Stein discrepancy of the vector fields $f_\Phi$ of the
closed unit ball of $\mathcal{H}$.

{{SVGD.kernelSteinDiscrepancy | Definition 2}}

```informal SVGD.kernelSteinDiscrepancy | Kernelized Stein discrepancy
Let $\Phi : \mathbb{R}^d \to H_0$, let $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and let $\rho$ be a
measure on $\mathbb{R}^d$. The kernelized Stein discrepancy (KSD) of $\rho$ with respect to $\pi$ is
$$\mathfrak{K}(\rho \mid \pi) = \sup_{f \in \mathcal{H}, \ \|f\|_{\mathcal{H}} \le 1} \mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)]^2.$$
It depends on $\pi$ only through its score $s$. The supremum is a supremum of real numbers, equal to
$0$ if the family is unbounded. For $\rho \in \mathcal{P}(\Omega)$, the family is bounded, and its
supremum is reached ([Theorem 2](#SVGD.stein_witness_ksd)).
```

Under the standing assumptions, $\mathcal{A}_s f_\Phi$ is continuous on $\Omega$ for every
$f \in \mathcal{H}$. By Corollary 1, $\mathfrak{K}(\pi \mid \pi) = 0$. The supremum is reached at an
explicit element of $\mathcal{H}$, which we now compute.

### The Stein witness

To find this element, we write the Stein operator of $f_\Phi$ as an inner product in $\mathcal{H}$.

{{SVGD.steinFeature | Definition}}

```informal SVGD.steinFeature | Stein feature
Let $\Phi : \mathbb{R}^d \to H_0$ and $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$. Let
$(e_1, \dots, e_d)$ be the canonical basis of $\mathbb{R}^d$. The Stein feature of
$x \in \mathbb{R}^d$ is the element $\xi_x \in \mathcal{H}$ defined by
$$(\xi_x)_i = s(x)(e_i) \, \Phi(x) + D\Phi(x)(e_i), \quad 1 \le i \le d.$$
```

{{SVGD.stein_feature | Lemma 3}}

```informal SVGD.stein_feature | Stein feature
Suppose that the standing assumptions hold. Then,
$$\forall x \in \mathbb{R}^d, \forall f \in \mathcal{H}, \quad \mathcal{A}_s f_\Phi(x) = \langle f, \xi_x \rangle_{\mathcal{H}}.$$
```

```sketch SVGD.stein_feature
By the chain rule, $Df_\Phi(x) = P_f \circ D\Phi(x)$, so that
$\operatorname{div} f_\Phi(x) = \sum_i \langle f_i, D\Phi(x)(e_i) \rangle_{H_0}$. Adding
$s(x)(f_\Phi(x)) = \sum_i \langle f_i, \Phi(x) \rangle_{H_0} \, s(x)(e_i)$ gives
$\langle f, \xi_x \rangle_{\mathcal{H}}$.
```

{{SVGD.xi_regularity_uniformContinuousOn | Lemma 4 (i)}}

```informal SVGD.xi_regularity_uniformContinuousOn | Regularity of $\xi$
Suppose that the standing assumptions hold. Then, the map $x \mapsto \xi_x$ is uniformly continuous
from $\Omega$ to $\mathcal{H}$.
```

```sketch SVGD.xi_regularity_uniformContinuousOn
$s$, $\Phi$ and $D\Phi$ are continuous on $\Omega$, so $\xi$ is continuous on the compact set
$\Omega$, and uniformly continuous by the Heine–Cantor theorem
(`IsCompact.uniformContinuousOn_of_continuous`).
```

{{SVGD.xi_regularity_exists_bound | Lemma 4 (ii)}}

```informal SVGD.xi_regularity_exists_bound | Regularity of $\xi$
Suppose that the standing assumptions hold. Then,
$$\exists B \ge 0, \forall x \in \Omega, \quad \|\xi_x\|_{\mathcal{H}} \le B.$$
```

```sketch SVGD.xi_regularity_exists_bound
A function continuous on a compact set is bounded on it
(`IsCompact.exists_bound_of_continuousOn`), and $\xi$ is continuous by
[Lemma 4 (i)](#SVGD.xi_regularity_uniformContinuousOn).
```

{{SVGD.xi_regularity_integrable | Lemma 4 (iii)}}

```informal SVGD.xi_regularity_integrable | Regularity of $\xi$
Suppose that the standing assumptions hold. Let $\rho \in \mathcal{P}(\Omega)$. Then, the map
$x \mapsto \xi_x$ is $\rho$-integrable.
```

```sketch SVGD.xi_regularity_integrable
$\xi$ is continuous on the compact set $\Omega$, which carries the probability measure $\rho$.
```

In the rest of the page, $B$ denotes a bound of $\|\xi_x\|_{\mathcal{H}}$ on $\Omega$, as given by
Lemma 4 (ii).

{{SVGD.steinWitness | Definition}}

```informal SVGD.steinWitness | Stein witness
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and let $\rho$ be a
measure on $\mathbb{R}^d$. The Stein witness of $\rho$ is the Bochner integral
$$\phi^*_\rho = \mathbb{E}_{x \sim \rho}[\xi_x] \in \mathcal{H}.$$
```

{{SVGD.stein_witness | Theorem 2}}

```informal SVGD.stein_witness | Existence of the Stein witness
Suppose that the standing assumptions hold and that $H_0$ is complete. Let
$\rho \in \mathcal{P}(\Omega)$. Then,
$$\forall f \in \mathcal{H}, \quad \mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)] = \langle f, \phi^*_\rho \rangle_{\mathcal{H}}.$$
```

```sketch SVGD.stein_witness
By [Lemma 4 (iii)](#SVGD.xi_regularity_integrable), $\xi$ is $\rho$-integrable, and the linear form
$\langle f, \cdot \rangle_{\mathcal{H}}$ commutes with the Bochner integral (`integral_inner`).
Thus, $\langle f, \phi^*_\rho \rangle_{\mathcal{H}} = \mathbb{E}_{x \sim \rho}[\langle f, \xi_x
\rangle_{\mathcal{H}}]$, which is the result by [Lemma 3](#SVGD.stein_feature).
```

{{SVGD.stein_witness_unique | Theorem 2}}

```informal SVGD.stein_witness_unique | Uniqueness of the Stein witness
Under the assumptions of [Theorem 2](#SVGD.stein_witness), let $f' \in \mathcal{H}$ such that
$\mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)] = \langle f, f' \rangle_{\mathcal{H}}$ for every
$f \in \mathcal{H}$. Then, $f' = \phi^*_\rho$.
```

```sketch SVGD.stein_witness_unique
By [Theorem 2](#SVGD.stein_witness), $\langle f, f' - \phi^*_\rho \rangle_{\mathcal{H}} = 0$ for every
$f \in \mathcal{H}$. With $f = f' - \phi^*_\rho$, this gives $\|f' - \phi^*_\rho\|_{\mathcal{H}}^2 = 0$.
```

{{SVGD.stein_witness_isMaxOn | Theorem 2 (i)}}

```informal SVGD.stein_witness_isMaxOn | The Stein witness maximizes the violation of Stein's identity
Under the assumptions of [Theorem 2](#SVGD.stein_witness), on the closed unit ball of
$\mathcal{H}$, the function $f \mapsto \mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)]$ reaches its
maximum at $f^* = \phi^*_\rho / \|\phi^*_\rho\|_{\mathcal{H}}$, where $f^* = 0$ if $\phi^*_\rho = 0$.
```

```sketch SVGD.stein_witness_isMaxOn
By [Theorem 2](#SVGD.stein_witness) and the Cauchy–Schwarz inequality, $\langle f, \phi^*_\rho
\rangle_{\mathcal{H}} \le \|\phi^*_\rho\|_{\mathcal{H}} = \langle f^*, \phi^*_\rho
\rangle_{\mathcal{H}}$ when $\|f\|_{\mathcal{H}} \le 1$.
```

{{SVGD.stein_witness_ksd | Theorem 2 (ii)}}

```informal SVGD.stein_witness_ksd | The KSD is the squared norm of the Stein witness
Under the assumptions of [Theorem 2](#SVGD.stein_witness),
$$\mathfrak{K}(\rho \mid \pi) = \|\phi^*_\rho\|_{\mathcal{H}}^2.$$
```

```sketch SVGD.stein_witness_ksd
By [Theorem 2](#SVGD.stein_witness), $\mathfrak{K}(\rho \mid \pi)$ is the supremum of $\langle f,
\phi^*_\rho \rangle_{\mathcal{H}}^2$ over the closed unit ball. Each term is at most
$\|\phi^*_\rho\|_{\mathcal{H}}^2$ by the Cauchy–Schwarz inequality, and the term of $f^*$ is equal
to it.
```

{{SVGD.stein_witness_ksd_eq_integral | Theorem 2 (ii)}}

```informal SVGD.stein_witness_ksd_eq_integral | The KSD as an expectation
Under the assumptions of [Theorem 2](#SVGD.stein_witness),
$$\mathfrak{K}(\rho \mid \pi) = \mathbb{E}_{x \sim \rho}[\mathcal{A}_s (\phi^*_\rho)_\Phi(x)].$$
```

```sketch SVGD.stein_witness_ksd_eq_integral
[Theorem 2](#SVGD.stein_witness) with $f = \phi^*_\rho$ gives
$\mathbb{E}_{x \sim \rho}[\mathcal{A}_s (\phi^*_\rho)_\Phi(x)] = \|\phi^*_\rho\|_{\mathcal{H}}^2$, which is the KSD by [Theorem 2 (ii)](#SVGD.stein_witness_ksd).
```

We call $\phi^*_\rho$ the *Stein witness* of $\rho$, by analogy with the witness function of the
maximum mean discrepancy [Gretton2012]. Up to normalization, it is the direction of $\mathcal{H}$
along which $\rho$ violates Stein's identity the most. As $\|\xi_x\|_{\mathcal{H}} \le B$ on
$\Omega$, we have that $\|\phi^*_\rho\|_{\mathcal{H}} \le B$ and $\|(\phi^*_\rho)_\Phi(y)\| \le B C$
for every $y \in \mathbb{R}^d$. The vector field of $\phi^*_\rho$ is thus bounded by a constant that
does not depend on $\rho$. The figure below shows this vector field in dimension $1$.

```figure
figures/stein_witness_1d.svg
The vector field of the Stein witness on $\Omega = [0, 1]$. **a)** The target density
$p \propto e^{-3 f}$, with $f(x) = 16 x^2 (1 - x)^2$, whose modes are the endpoints of $\Omega$. The
density of $\rho$ is a Gaussian of mean $0.5$ and standard deviation $0.25$, restricted to $\Omega$.
**b)** The field $(\phi^*_\rho)_\Phi$ for the Gaussian kernel
$k_0(x, y) = e^{-(x - y)^2 / (2 \cdot 0.15^2)}$, in red, and for the weighted kernel
$w(x) w(y) k_0(x, y)$ with $w(x) = x (1 - x)$, in blue. Each field is divided by its maximum absolute
value on $\Omega$. A positive value moves a particle to the right. **c)** The particles of a regular
grid of $\Omega$, and their displacements $y \mapsto y + \varepsilon (\phi^*_\rho)_\Phi(y)$ for a
small step $\varepsilon > 0$. The arrows are red when they leave $\Omega$. Both fields move the
particles toward the modes of $p$. The Gaussian kernel does not satisfy (iv) of Assumption 2, and the
particles at $0$ and $1$ leave $\Omega$. With the weighted kernel, the field vanishes at $0$ and $1$,
and these particles do not move. Outside $\Omega$, $w$ can be modified to be bounded and Lipschitz,
as Assumption 2 requires, without changing the figure.
```

As $\mathfrak{K}(\pi \mid \pi) = 0$, the Stein witness of $\pi$ vanishes.

The KSD can also be computed from the kernel $k$ and the score $s$ only. Expanding the inner product
of the Stein features, we obtain
$$\langle \xi_x, \xi_y \rangle_{\mathcal{H}} = k(x, y) \langle s(x), s(y) \rangle + \langle s(x), \nabla_y k(x, y) \rangle + \langle s(y), \nabla_x k(x, y) \rangle + \sum_{i=1}^d \partial_{x_i} \partial_{y_i} k(x, y),$$
so that $\mathfrak{K}(\rho \mid \pi) = \mathbb{E}_{x, y \sim \rho}[\langle \xi_x, \xi_y
\rangle_{\mathcal{H}}]$, where $x$ and $y$ are independent. This is the expression of the KSD of
[Liu2016]. It is not formalized.

## The steepest descent of the Kullback–Leibler divergence

The Stein witness is also the direction of steepest descent of the Kullback–Leibler divergence to
$\pi$ [Liu2016SVGD]. Let $\rho$ be a probability measure on $\mathbb{R}^d$ such that
$\mathrm{KL}(\rho \,\|\, \pi) < \infty$. For $f \in \mathcal{H}$ and $\varepsilon \in \mathbb{R}$,
let
$$h_f(\varepsilon) = \mathrm{KL}\big((I_d + \varepsilon f_\Phi)_\# \rho \,\|\, \pi\big).$$

{{SVGD.klFirstVariation | Definition}}

```informal SVGD.klFirstVariation | First variation along $f$
Let $\Phi : \mathbb{R}^d \to H_0$, let $\pi$ and $\rho$ be measures on $\mathbb{R}^d$, and let
$f \in \mathcal{H}$. The first variation of the Kullback–Leibler divergence to $\pi$ at $\rho$ along
$f$ is $h'_f(0)$, the derivative at $0$ of
$\varepsilon \mapsto \mathrm{KL}((I_d + \varepsilon f_\Phi)_\# \rho \,\|\, \pi)$. It is $0$ when this
function is not differentiable at $0$.
```

{{SVGD.kl_steepest_descent_ne_top | Theorem 3 (i)}}

```informal SVGD.kl_steepest_descent_ne_top | KL steepest descent
Suppose that the standing assumptions hold and that $H_0$ is complete. Let $\rho$ be a probability
measure on $\mathbb{R}^d$ such that $\mathrm{KL}(\rho \,\|\, \pi) < \infty$, and let
$f \in \mathcal{H}$. Then, $h_f(\varepsilon) < \infty$ for every $\varepsilon$ in a neighborhood of
$0$.
```

```sketch SVGD.kl_steepest_descent_ne_top
[Theorem 1 (ii)](#SVGD.first_variation_ne_top) applies to $v = f_\Phi$, which is continuously
differentiable, Lipschitz and zero on $\partial \Omega$ by Assumption 2.
```

{{SVGD.kl_steepest_descent_hasDerivAt | Theorem 3 (i)}}

```informal SVGD.kl_steepest_descent_hasDerivAt | KL steepest descent
Under the assumptions of [Theorem 3 (i)](#SVGD.kl_steepest_descent_ne_top), $h_f$ is
differentiable at $0$, and
$$h'_f(0) = -\langle f, \phi^*_\rho \rangle_{\mathcal{H}}.$$
```

```diagram SVGD.kl_steepest_descent_hasDerivAt
supp: `SVGD.TargetAssumption.ae_mem_of_klDiv_ne_top`
  $\rho \in \mathcal{P}(\Omega)$
field: step
  $f_\Phi$ is $C^1$, $\|f\|_{\mathcal{H}} K$-Lipschitz, and zero on $\partial \Omega$
  > By Assumption 2, through $f_\Phi = P_f \circ \Phi$ and $\|P_f\| \le \|f\|_{\mathcal{H}}$.
T1: `SVGD.first_variation` <- field
  $h'_f(0) = -\mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)]$
T2: `SVGD.stein_witness` <- supp
  $\mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)] = \langle f, \phi^*_\rho \rangle_{\mathcal{H}}$
goal <- T1, T2
```

{{SVGD.kl_steepest_descent_eq_inner | Theorem 3 (i)}}

```informal SVGD.kl_steepest_descent_eq_inner | KL steepest descent
Under the assumptions of [Theorem 3 (i)](#SVGD.kl_steepest_descent_ne_top), the
[first variation](#SVGD.klFirstVariation) along $f$ is
$h'_f(0) = -\langle f, \phi^*_\rho \rangle_{\mathcal{H}}$.
```

```sketch SVGD.kl_steepest_descent_eq_inner
This is [Theorem 3 (i)](#SVGD.kl_steepest_descent_hasDerivAt), as $h_f$ is differentiable at $0$.
```

{{SVGD.kl_steepest_descent_isMinOn | Theorem 3 (ii)}}

```informal SVGD.kl_steepest_descent_isMinOn | The Stein witness is the steepest direction
Under the assumptions of [Theorem 3 (i)](#SVGD.kl_steepest_descent_ne_top), on the closed unit ball
of $\mathcal{H}$, the function $f \mapsto h'_f(0)$ reaches its minimum at
$f^* = \phi^*_\rho / \|\phi^*_\rho\|_{\mathcal{H}}$, where $f^* = 0$ if $\phi^*_\rho = 0$.
```

```sketch SVGD.kl_steepest_descent_isMinOn
By [Theorem 3 (i)](#SVGD.kl_steepest_descent_eq_inner), minimizing $h'_f(0)$ amounts to maximizing
$\langle f, \phi^*_\rho \rangle_{\mathcal{H}}$, which [Theorem 2 (i)](#SVGD.stein_witness_isMaxOn)
does.
```

{{SVGD.kl_steepest_descent_eq | Theorem 3 (ii)}}

```informal SVGD.kl_steepest_descent_eq | Uniqueness of the steepest direction
Under the assumptions of [Theorem 3 (i)](#SVGD.kl_steepest_descent_ne_top), suppose that
$\phi^*_\rho \neq 0$. Let $f$ be in the closed unit ball of $\mathcal{H}$, with
$h'_f(0) = h'_{f^*}(0)$. Then, $f = f^*$.
```

```sketch SVGD.kl_steepest_descent_eq
By [Theorem 3 (i)](#SVGD.kl_steepest_descent_eq_inner), $\langle f, \phi^*_\rho \rangle_{\mathcal{H}} =
\langle f^*, \phi^*_\rho \rangle_{\mathcal{H}} = \|\phi^*_\rho\|_{\mathcal{H}}$, i.e.
$\langle f, f^* \rangle_{\mathcal{H}} = 1$. As $\|f^*\|_{\mathcal{H}} = 1$, we have that
$\|f - f^*\|_{\mathcal{H}}^2 = \|f\|_{\mathcal{H}}^2 - 1 \le 0$.
```

{{SVGD.kl_steepest_descent_ksd | Theorem 3 (iii)}}

```informal SVGD.kl_steepest_descent_ksd | The descent rate is the KSD
Under the assumptions of [Theorem 3 (i)](#SVGD.kl_steepest_descent_ne_top),
$$h'_{\phi^*_\rho}(0) = -\mathfrak{K}(\rho \mid \pi).$$
```

```sketch SVGD.kl_steepest_descent_ksd
[Theorem 3 (i)](#SVGD.kl_steepest_descent_eq_inner) with $f = \phi^*_\rho$ gives
$h'_f(0) = -\|\phi^*_\rho\|_{\mathcal{H}}^2$, which is $-\mathfrak{K}(\rho \mid \pi)$ by
[Theorem 2 (ii)](#SVGD.stein_witness_ksd).
```

Thus, $\phi^*_\rho$ is the optimal direction, within $\mathcal{H}$, to update $\rho$ in order to
decrease the Kullback–Leibler divergence to $\pi$. SVGD iteratively updates $\rho$ in this
direction, with a small step size $\varepsilon > 0$, i.e.
$$\rho_{n+1} = (I_d + \varepsilon (\phi^*_{\rho_n})_\Phi)_\# \rho_n, \quad n \in \mathbb{N}.$$
If $\varepsilon B K < 1$, Lemma 1 shows that every $\rho_n$ stays in $\mathcal{P}(\Omega)$. In
practice, $\rho_0$ is the empirical measure of $N$ particles, and each particle $x^j_n$ moves to
$x^j_n + \varepsilon (\phi^*_{\rho_n})_\Phi(x^j_n)$. With $\rho = \frac{1}{N} \sum_j \delta_{x^j}$,
we have that
$$(\phi^*_\rho)_\Phi(y) = \frac{1}{N} \sum_{j=1}^N \big(k(x^j, y) \, s(x^j) + \nabla_x k(x^j, y)\big),$$
which is the update of [Liu2016SVGD]. The iteration itself is not formalized. The figure below
shows it on the domain of the first figure, whose boundary has a cusp and two corners.

```figure
figures/svgd_simulation.svg
SVGD with $N = 200$ particles on $\Omega = \{(x, y) \in \mathbb{R}^2 \mid y^2 \le x^3, \ x^2 + y^2
\le 1\}$. The density of $\pi$ is proportional to a mixture of two Gaussians of standard deviation
$0.12$, restricted to $\Omega$ (gray levels). The kernel is $k(z, z') = w(z) w(z') e^{-\|z - z'\|^2
/ (2 \cdot 0.3^2)}$, with $w(z) = c (z_1^3 - z_2^2)(1 - \|z\|^2)$ and $c \approx 5.38$, so that
$\max_\Omega w = 1$. The weight $w$ vanishes on $\partial \Omega$. Outside $\Omega$, it can be
modified to be bounded and Lipschitz, as Assumption 2 requires, without changing the figure. The
particles start near the cusp and follow the iteration above with $\varepsilon = 0.08$. **Left.**
The particles at the iterations $n = 0$, $300$ and $3000$. They spread over the two modes of $\pi$,
and none of them leaves $\Omega$. **Right.** The KSD of the empirical measure $\rho_n$, computed
from the kernel as a double sum over the particles. [Theorem 7](#SVGD.convergence_to_target) does
not cover empirical measures.
```

## SVGD in continuous time

We now study SVGD in continuous time. The particles follow a differential equation, of which the
iteration above is a time discretization. We show that this equation has a solution for all times,
and that the particles never leave $\Omega$.

### The continuous-time dynamics

{{SVGD.drift | Definition}}

```informal SVGD.drift | Drift
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$, and let $\rho$ be a
measure on $\mathbb{R}^d$. The drift at $x \in \mathbb{R}^d$ is
$$b(x, \rho) = (\phi^*_\rho)_\Phi(x).$$
It is the velocity of a particle located at $x$, when the particles are distributed according to
$\rho$.
```

Let $X_t$ be the position at time $t$ of a particle whose initial position $X_0$ is drawn from
$\rho_0$. SVGD in continuous time is the McKean–Vlasov equation
$$dX_t = b(X_t, \rho_t) \, dt, \quad \text{where } \rho_t \text{ is the law of } X_t.$$
It is studied on the whole space $\mathbb{R}^d$ by [Liu2017] and [Lu2019]. There is no noise, so a
particle moves deterministically. Let $T_t(x)$ be the position at time $t$ of the particle that
starts from $x$. Then, $\rho_t = (T_t)_\# \rho_0$, and the equation reads
$$\frac{d}{dt} T_t(x) = b(T_t(x), \rho_t), \quad \text{where } \rho_t = (T_t)_\# \rho_0.$$
We call it the continuous-time SVGD equation.

{{SVGD.IsSolution | Definition}}

```informal SVGD.IsSolution | Solution of the continuous-time SVGD equation
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$, $\Omega \subseteq
\mathbb{R}^d$ and let $\rho_0$ be a measure on $\mathbb{R}^d$. A family $(T_t)_{t \ge 0}$ of maps
from $\mathbb{R}^d$ to $\mathbb{R}^d$ solves the continuous-time SVGD equation from $\rho_0$ if,
with $\rho_t = (T_t)_\# \rho_0$, the following conditions hold.

(i) $T_t$ is continuous for every $t \ge 0$.

(ii) $T_0 = I_d$.

(iii) $\rho_t(\mathbb{R}^d \setminus \Omega) = 0$ for every $t \ge 0$.

(iv) For all $x \in \mathbb{R}^d$ and $t \ge 0$,
$\frac{d}{dt} T_t(x) = b(T_t(x), \rho_t)$, with a right derivative at $t = 0$.
```

This equation is not a standard differential equation. The drift $b(\cdot, \rho_t)$ depends on the
distribution of the particles, which depends on their positions, which are the unknown.

### Existence of a solution

{{SVGD.exists_continuous_time_dynamics | Theorem 4}}

```informal SVGD.exists_continuous_time_dynamics | Existence of the continuous-time dynamics
Suppose that the standing assumptions hold and that $H_0$ is complete. Let
$\rho_0 \in \mathcal{P}(\Omega)$. Then, there exists a family $(T_t)_{t \ge 0}$ of maps from
$\mathbb{R}^d$ to $\mathbb{R}^d$ that solves the continuous-time SVGD equation from $\rho_0$.
```

```diagram SVGD.exists_continuous_time_dynamics
L8: `SVGD.consistent_candidate_bounded_interval`
  from any $\rho \in \mathcal{P}(\Omega)$, a consistent curve on $[0, 1]$
ind: step <- L8
  by induction, $g_n$ from $\rho_n$, and $\rho_{n+1} = (T^{g_n}_1)_\# \rho_n \in \mathcal{P}(\Omega)$
  > Lemma 8 with $\rho = \rho_n$ and $a = 1$ gives $g_n$. By Lemma 5 (i), $\rho_{n+1}$ is carried by $\Omega$.
glue: step <- ind
  $m(t) = g_n(t - n)$ on $[n, n + 1]$ is a continuous curve in $\mathcal{W}$
  > The pieces agree at the integers, as $g_n(1) = \phi^*_{\rho_{n+1}} = g_{n+1}(0)$.
uniq: `SVGD.positions_unique`
  the positions are unique
flow: step <- glue, uniq
  $T^m_t = T^{g_n}_{t - n} \circ T^m_n$ and $(T^m_n)_\# \rho_0 = \rho_n$
  > Between the times $n$ and $n + 1$, the particles follow the velocity field of $g_n$.
cons: step <- flow
  $m(t) = \phi^*_{(T^m_t)_\# \rho_0}$ for every $t \ge 0$
L7: `SVGD.consistent_candidate_isSolution` <- glue, cons
  $T_t = T^m_t$ solves the equation
goal <- L7
```

Every solution has three properties, proved in [Lemma 9](#SVGD.solution_properties_isHomeomorph).
Every $T_t$ is a homeomorphism of $\mathbb{R}^d$, i.e. two particles never meet. Every particle that
starts in $\Omega$ stays in $\Omega$, as the particles located on $\partial \Omega$ do not move. The
Stein witness $\phi^*_{\rho_t}$ varies continuously in time. Theorem 4 does not claim that the
solution is unique.

### Strategy of the proof

The proof breaks the circular dependence in two halves. Suppose first that the drift is given, by a
*candidate*, i.e. a continuous and bounded curve $m : [0, \infty) \to \mathcal{H}$. At time $t$, it
gives the velocity $m(t)_\Phi(y)$ to a particle located at $y$. The particles no longer interact,
and their positions $T^m_t$ solve a standard differential equation (Lemma 5). Conversely, the
positions give a distribution, for which SVGD prescribes a drift. Chaining the two halves gives a
map $m \mapsto G_{\rho_0}(m)$. A fixed point of this map gives a solution (Lemma 7). On a bounded
time interval, a fixed point exists by Schauder's theorem (Lemma 8). Gluing the fixed points of the
intervals $[n, n + 1]$ gives a solution for all times (Theorem 4).

### From the drift to the positions

Let $m : \mathbb{R} \to \mathcal{H}$ be a continuous curve, and let $R \ge 0$ such that
$\|m(t)\|_{\mathcal{H}} \le R$ for every $t$. In Lean, a curve on $[0, \infty)$ is a curve on
$\mathbb{R}$ whose values at negative times do not matter. Let $T^m_t(x)$ be the value at time $t$
of the [trajectory](#SVGD.trajectory) of the velocity field $(t, y) \mapsto m(t)_\Phi(y)$ that
starts from $x$ at time $0$.

{{SVGD.positions_hasDerivAt | Lemma 5}}

```informal SVGD.positions_hasDerivAt | Positions for a given drift, existence
Suppose that the standing assumptions hold. Let $m : \mathbb{R} \to \mathcal{H}$ be continuous, with
$\|m(t)\|_{\mathcal{H}} \le R$ for every $t \in \mathbb{R}$. Then, for all $x \in \mathbb{R}^d$ and
$t \in \mathbb{R}$,
$$\frac{d}{dt} T^m_t(x) = m(t)_\Phi(T^m_t(x)).$$
```

```sketch SVGD.positions_hasDerivAt
The velocity field is continuous in time and $R K$-Lipschitz in space, so the equation has a global
solution by the Cauchy–Lipschitz theorem. Tau Ceti builds it in `ODE.nonautonomousSolution`.
```

{{SVGD.positions_zero | Lemma 5}}

```informal SVGD.positions_zero | Positions for a given drift, initial condition
Under the assumptions of [Lemma 5](#SVGD.positions_hasDerivAt), $T^m_0(x) = x$ for every
$x \in \mathbb{R}^d$.
```

```sketch SVGD.positions_zero
The trajectory starts from $x$ at time $0$.
```

{{SVGD.positions_unique | Lemma 5}}

```informal SVGD.positions_unique | Positions for a given drift, uniqueness
Under the assumptions of [Lemma 5](#SVGD.positions_hasDerivAt), let $x \in \mathbb{R}^d$ and let
$\alpha : \mathbb{R} \to \mathbb{R}^d$ such that $\alpha(0) = x$ and
$\alpha'(t) = m(t)_\Phi(\alpha(t))$ for every $t \ge 0$, with a right derivative at $t = 0$. Then,
$\alpha(t) = T^m_t(x)$ for every $t \ge 0$.
```

```sketch SVGD.positions_unique
Two solutions of an equation with a Lipschitz velocity field and the same initial condition are
equal, by Grönwall's inequality (`ODE_solution_unique_of_mem_Icc_right`).
```

{{SVGD.positions_isHomeomorph | Lemma 5 (i)}}

```informal SVGD.positions_isHomeomorph | Positions for a given drift, homeomorphism
Under the assumptions of [Lemma 5](#SVGD.positions_hasDerivAt), $T^m_t$ is a homeomorphism of
$\mathbb{R}^d$ for every $t \in \mathbb{R}$.
```

```sketch SVGD.positions_isHomeomorph
Following the trajectories backward from time $t$ inverts $T^m_t$, by uniqueness of the solutions.
Both maps are continuous, as two solutions satisfy
$\|\alpha(r) - \beta(r)\| \le e^{R K |r - r'|} \|\alpha(r') - \beta(r')\|$ by Grönwall's inequality.
```

{{SVGD.positions_image | Lemma 5 (i)}}

```informal SVGD.positions_image | Positions for a given drift, invariance of $\Omega$
Under the assumptions of [Lemma 5](#SVGD.positions_hasDerivAt), $T^m_t(\Omega) = \Omega$ for every
$t \in \mathbb{R}$.
```

```diagram SVGD.positions_image
rest: step
  $m(t)_\Phi(z) = 0$ for $z \in \partial \Omega$
  > By (iv) of Assumption 2, $\Phi(z) = 0$. Thus, the constant curve equal to $z$ is a solution.
uniq: step <- rest
  no other trajectory reaches a point of $\partial \Omega$
  > By uniqueness of the solutions, a trajectory through $z \in \partial \Omega$ is the constant curve equal to $z$.
conn: Connected sets and frontiers `IsPreconnected.inter_frontier_nonempty` <- uniq
  a trajectory that meets $\Omega$ stays in $\Omega$
  > If a connected set meets both $\Omega$ and $\mathbb{R}^d \setminus \Omega$, then it meets $\partial \Omega$. A trajectory is connected, as the image of an interval by a continuous map. By the previous step, it does not meet $\partial \Omega$, unless it is constant.
homeo: `SVGD.positions_isHomeomorph`
  $T^m_t$ is a bijection, with inverse $S_t$
goal <- conn, homeo
  $T^m_t(\Omega) = \Omega$
  > $T^m_t$ and its inverse $S_t$ map $\Omega$ into $\Omega$, so that $\Omega = T^m_t(S_t(\Omega)) \subseteq T^m_t(\Omega)$.
```

{{SVGD.positions_dist_le | Lemma 5 (ii)}}

```informal SVGD.positions_dist_le | Positions for a given drift, speed
Under the assumptions of [Lemma 5](#SVGD.positions_hasDerivAt),
$$\forall x \in \mathbb{R}^d, \forall t, t' \in \mathbb{R}, \quad \|T^m_t(x) - T^m_{t'}(x)\| \le R C |t - t'|.$$
```

```sketch SVGD.positions_dist_le
The derivative of $t \mapsto T^m_t(x)$ is the velocity $m(t)_\Phi(T^m_t(x))$, which is bounded by
$R C$.
```

{{SVGD.positions_dist_le_of_dist_le | Lemma 5 (iii)}}

```informal SVGD.positions_dist_le_of_dist_le | Close candidates give close positions
Under the assumptions of [Lemma 5](#SVGD.positions_hasDerivAt), let
$m' : \mathbb{R} \to \mathcal{H}$ be continuous, with $\|m'(t)\|_{\mathcal{H}} \le R$ for every
$t \in \mathbb{R}$. Let $t \ge 0$ and $\Delta \in \mathbb{R}$ such that
$\|m(r) - m'(r)\|_{\mathcal{H}} \le \Delta$ for every $r \in [0, t]$. Then, for every
$x \in \mathbb{R}^d$,
$$\|T^m_t(x) - T^{m'}_t(x)\| \le C \, t \, e^{R K t} \, \Delta.$$
```

```sketch SVGD.positions_dist_le_of_dist_le
The gap $\eta(r) = T^m_r(x) - T^{m'}_r(x)$ satisfies $\|\eta'(r)\| \le R K \|\eta(r)\| + C \Delta$
and $\eta(0) = 0$, and Grönwall's inequality (`dist_le_of_approx_trajectories_ODE`) concludes.
```

### From the positions to the drift

{{SVGD.fixedPointMap | Definition}}

```informal SVGD.fixedPointMap | The map $G_{\rho_0}$
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$, let $\rho_0$ be a measure
on $\mathbb{R}^d$ and let $m : \mathbb{R} \to \mathcal{H}$. The curve $G_{\rho_0}(m)$ is
$$G_{\rho_0}(m)(t) = \phi^*_{(T^m_t)_\# \rho_0}, \quad t \in \mathbb{R}.$$
It is the drift that SVGD prescribes for the positions that $m$ produces.
```

{{SVGD.IsConsistent | Definition}}

```informal SVGD.IsConsistent | Consistent candidate
A curve $m : \mathbb{R} \to \mathcal{H}$ is consistent if it solves the fixed-point equation
$$\forall t \ge 0, \quad m(t) = G_{\rho_0}(m)(t) = \phi^*_{(T^m_t)_\# \rho_0}.$$
```

The curve $m$ appears on both sides, as the right-hand side depends on $m$ through the positions.
All the Stein witnesses live in a fixed compact set.

{{SVGD.witnessSet | Definition}}

```informal SVGD.witnessSet | The set $\mathcal{W}$
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and
$\Omega \subseteq \mathbb{R}^d$. The set $\mathcal{W}$ is the closed convex hull of
$\{\xi_x \mid x \in \Omega\}$ in $\mathcal{H}$.
```

{{SVGD.witness_set_isCompact | Lemma 6}}

```informal SVGD.witness_set_isCompact | Set of the Stein witnesses, compactness
Suppose that the standing assumptions hold and that $H_0$ is complete. Then, $\mathcal{W}$ is
compact.
```

```sketch SVGD.witness_set_isCompact
$\{\xi_x \mid x \in \Omega\}$ is compact by [Lemma 4 (i)](#SVGD.xi_regularity_uniformContinuousOn),
and the closed convex hull of a compact set of a Banach space is compact, by Mazur's theorem
(`IsCompact.closedConvexHull`).
```

{{SVGD.witness_set_norm_le | Lemma 6}}

```informal SVGD.witness_set_norm_le | Set of the Stein witnesses, bound
Let $B \ge 0$ such that $\|\xi_x\|_{\mathcal{H}} \le B$ for every $x \in \Omega$. Then,
$\|f\|_{\mathcal{H}} \le B$ for every $f \in \mathcal{W}$.
```

```sketch SVGD.witness_set_norm_le
The closed ball of radius $B$ is closed and convex, and contains every $\xi_x$, so it contains
$\mathcal{W}$.
```

{{SVGD.witness_set_steinWitness_mem | Lemma 6}}

```informal SVGD.witness_set_steinWitness_mem | Set of the Stein witnesses, membership
Suppose that the standing assumptions hold and that $H_0$ is complete. Let
$\rho \in \mathcal{P}(\Omega)$. Then, $\phi^*_\rho \in \mathcal{W}$.
```

```sketch SVGD.witness_set_steinWitness_mem
$\phi^*_\rho = \mathbb{E}_{x \sim \rho}[\xi_x]$, and $\xi_x \in \mathcal{W}$ for $\rho$-almost every
$x$. The mean of a function with values in a closed convex set lies in this set
(`Convex.integral_mem`).
```

{{SVGD.consistent_candidate_isSolution | Lemma 7}}

```informal SVGD.consistent_candidate_isSolution | A consistent candidate gives a solution
Suppose that the standing assumptions hold. Let $\rho_0$ be a measure on $\mathbb{R}^d$ such that
$\rho_0(\mathbb{R}^d \setminus \Omega) = 0$. Let $m : \mathbb{R} \to \mathcal{H}$ be continuous,
with values in $\mathcal{W}$, and consistent. Then, the maps $T_t = T^m_t$ solve the
continuous-time SVGD equation from $\rho_0$.
```

```sketch SVGD.consistent_candidate_isSolution
By [Lemma 6](#SVGD.witness_set_norm_le), $m$ is bounded by $B$, and [Lemma 5](#SVGD.positions_image)
keeps the particles in $\Omega$. As $m(t) = \phi^*_{\rho_t}$, the equation of Lemma 5 is the
continuous-time SVGD equation.
```

### A consistent candidate on a bounded time interval

Let $\omega(r) = \sup \{\|\xi_x - \xi_y\|_{\mathcal{H}} \mid x, y \in \Omega, \|x - y\| \le r\}$ be
the [modulus of continuity](#modulusOfContinuityOn) of the Stein feature on $\Omega$. It is
nondecreasing, and $\omega(r) \to 0$ as $r \to 0$, by Lemma 4 (i). The next estimate controls how
much the Stein witness changes when the particles are moved.

{{SVGD.dist_steinWitness_map_le | Estimate}}

```informal SVGD.dist_steinWitness_map_le | Witness estimate
Suppose that the standing assumptions hold. Let $\rho$ be a probability measure on $\mathbb{R}^d$,
and let $\psi_1, \psi_2 : \mathbb{R}^d \to \mathbb{R}^d$ be $\rho$-almost everywhere measurable, with
$\psi_1(x), \psi_2(x) \in \Omega$ and $\|\psi_1(x) - \psi_2(x)\| \le r$ for $\rho$-almost every $x$.
Then,
$$\|\phi^*_{(\psi_1)_\# \rho} - \phi^*_{(\psi_2)_\# \rho}\|_{\mathcal{H}} \le \omega(r).$$
```

```sketch SVGD.dist_steinWitness_map_le
By the change of variables formula, $\phi^*_{(\psi_k)_\# \rho} = \mathbb{E}_{x \sim
\rho}[\xi_{\psi_k(x)}]$, and the norm of a mean is at most the mean of the norms, each bounded by
$\omega(r)$.
```

We look for a fixed point of $G$ on a bounded time interval with the following theorem, which needs
no contraction.

{{SVGD.schauder | Theorem 5}}

```informal SVGD.schauder | Schauder
Let $\Gamma$ be a nonempty, compact and convex subset of a real normed space. Then, every
continuous map from $\Gamma$ to $\Gamma$ has a fixed point.
```

```sketch SVGD.schauder
This is Schauder's fixed point theorem [Schauder1930], proved in Tau Ceti
(`TauCeti.schauderFixedPoint_compactConvex`). It is usually stated in a Banach space, but
completeness is not needed.
```

{{SVGD.consistent_candidate_bounded_interval | Lemma 8}}

```informal SVGD.consistent_candidate_bounded_interval | A consistent candidate on a bounded time interval
Suppose that the standing assumptions hold and that $H_0$ is complete. Let
$\rho \in \mathcal{P}(\Omega)$ and $a > 0$. Then, there exists a continuous curve
$g : [0, a] \to \mathcal{W}$ such that
$$\forall t \in [0, a], \quad g(t) = \phi^*_{(T^{\bar g}_t)_\# \rho},$$
where $\bar g$ extends $g$ to $\mathbb{R}$ by $g(0)$ before $0$ and by $g(a)$ after $a$.
```

```diagram SVGD.consistent_candidate_bounded_interval
speed: `SVGD.positions_dist_le`
  the particles move at speed at most $B C$
est: `SVGD.dist_steinWitness_map_le`
  moving the particles by $r$ changes $\phi^*$ by $\omega(r)$
close: `SVGD.positions_dist_le_of_dist_le`
  close curves give close positions
W: `SVGD.witness_set_isCompact`
  $\mathcal{W}$ is compact and convex
Gamma: Arzelà–Ascoli theorem `BoundedContinuousFunction.arzela_ascoli₂` <- W, speed, est
  $\Gamma$ is compact and convex
  > $\Gamma$ is the set of the continuous curves $g : [0, a] \to \mathcal{W}$ with $\|g(t) - g(t')\|_{\mathcal{H}} \le \omega(B C |t - t'|)$. Its curves take their values in the compact set $\mathcal{W}$ and are equicontinuous, as $\omega(r) \to 0$ as $r \to 0$.
into: step <- speed, est, W
  $G(\Gamma) \subseteq \Gamma$
  > $G g(t) \in \mathcal{W}$ by Lemma 6. Between $t$ and $t'$, the particles move by at most $B C |t - t'|$, so that $\|G g(t) - G g(t')\|_{\mathcal{H}} \le \omega(B C |t - t'|)$.
cont: step <- close, est
  $G$ is continuous on $\Gamma$
  > $\|G g - G g'\|_\infty \le \omega(a C e^{B K a} \|g - g'\|_\infty)$, and $\omega(r) \to 0$ as $r \to 0$.
fix: `SVGD.schauder` <- Gamma, into, cont
  $G$ has a fixed point $g \in \Gamma$
goal <- fix
```

### Properties of the solutions

Every solution, and not only the one of Theorem 4, has the following properties. Once a solution is
fixed, its Stein witnesses form a fixed curve, and Lemma 5 applies to it.

{{SVGD.witnessCurve | Definition}}

```informal SVGD.witnessCurve | Curve of the Stein witnesses
Let $(T_t)_{t \ge 0}$ be a family of maps from $\mathbb{R}^d$ to $\mathbb{R}^d$, let $\rho_0$ be a
measure on $\mathbb{R}^d$ and let $\rho_t = (T_t)_\# \rho_0$. The curve of the Stein witnesses is
$m(t) = \phi^*_{\rho_t}$ for $t \ge 0$, extended to negative times by $m(0)$.
```

{{SVGD.solution_properties_dist_le | Lemma 9 (i)}}

```informal SVGD.solution_properties_dist_le | Properties of the solutions, continuity of the Stein witness
Suppose that the standing assumptions hold. Let $\rho_0$ be a probability measure on
$\mathbb{R}^d$, let $(T_t)_{t \ge 0}$ solve the continuous-time SVGD equation from $\rho_0$, and let
$m$ be the curve of its Stein witnesses. Let $B \ge 0$ such that $\|\xi_x\|_{\mathcal{H}} \le B$ for
every $x \in \Omega$. Then,
$$\forall t, t' \ge 0, \quad \|m(t) - m(t')\|_{\mathcal{H}} \le \omega(B C |t - t'|).$$
```

```sketch SVGD.solution_properties_dist_le
As every Stein witness is bounded by $B$, the particles move at speed at most $B C$, i.e.
$\|T_t(x) - T_{t'}(x)\| \le B C |t - t'|$. As $m(t) = \phi^*_{(T_t)_\# \rho_0}$, the
[witness estimate](#SVGD.dist_steinWitness_map_le) with the maps $T_t$ and $T_{t'}$ concludes.
```

{{SVGD.solution_properties_continuous | Lemma 9 (i)}}

```informal SVGD.solution_properties_continuous | Properties of the solutions, continuity of the Stein witness
Under the assumptions of [Lemma 9 (i)](#SVGD.solution_properties_dist_le), the curve $m$ is
continuous on $\mathbb{R}$.
```

```sketch SVGD.solution_properties_continuous
By [Lemma 9 (i)](#SVGD.solution_properties_dist_le) with the bound $B$ of Lemma 4 (ii), as
$\omega(r) \to 0$ as $r \to 0$.
```

{{SVGD.solution_properties_eq_positions | Lemma 9 (ii)}}

```informal SVGD.solution_properties_eq_positions | Properties of the solutions, trajectories
Under the assumptions of [Lemma 9 (i)](#SVGD.solution_properties_dist_le), $T_t = T^m_t$ for every
$t \ge 0$.
```

```sketch SVGD.solution_properties_eq_positions
$t \mapsto T_t(x)$ solves the equation of Lemma 5 for the fixed curve $m$, which is continuous and
bounded by $B$, so it is $T^m_t(x)$ by [uniqueness](#SVGD.positions_unique). This does not use any
uniqueness of the solution itself.
```

{{SVGD.solution_properties_isHomeomorph | Lemma 9 (iii)}}

```informal SVGD.solution_properties_isHomeomorph | Properties of the solutions, homeomorphisms
Under the assumptions of [Lemma 9 (i)](#SVGD.solution_properties_dist_le), $T_t$ is a homeomorphism
of $\mathbb{R}^d$ for every $t \ge 0$.
```

```sketch SVGD.solution_properties_isHomeomorph
By [Lemma 9 (ii)](#SVGD.solution_properties_eq_positions) and
[Lemma 5 (i)](#SVGD.positions_isHomeomorph).
```

{{SVGD.solution_properties_image | Lemma 9 (iii)}}

```informal SVGD.solution_properties_image | Properties of the solutions, invariance of $\Omega$
Under the assumptions of [Lemma 9 (i)](#SVGD.solution_properties_dist_le), $T_t(\Omega) = \Omega$
for every $t \ge 0$.
```

```sketch SVGD.solution_properties_image
By [Lemma 9 (ii)](#SVGD.solution_properties_eq_positions) and [Lemma 5 (i)](#SVGD.positions_image).
```

{{SVGD.solution_properties_boundary | Lemma 9 (iv)}}

```informal SVGD.solution_properties_boundary | Properties of the solutions, the boundary is at rest
Under the assumptions of [Lemma 9 (i)](#SVGD.solution_properties_dist_le), $T_t(z) = z$ for all
$z \in \partial \Omega$ and $t \ge 0$.
```

```sketch SVGD.solution_properties_boundary
As $\Phi(z) = 0$, the constant curve equal to $z$ solves the equation of Lemma 5, so it is
$t \mapsto T_t(z)$ by [uniqueness](#SVGD.positions_unique).
```

## The time derivative of the Kullback–Leibler divergence

By Theorem 3, the derivative of the divergence in the direction of the Stein witness is
$-\mathfrak{K}(\rho \mid \pi)$. In continuous time, the particles follow the Stein witness of their
distribution at every time. Thus, the divergence decreases at rate $\mathfrak{K}(\rho_t \mid \pi)$.

{{SVGD.time_derivative_kl | Theorem 6}}

```informal SVGD.time_derivative_kl | Time derivative of the KL divergence
Suppose that the standing assumptions hold and that $H_0$ is complete. Let $\rho_0$ be a probability
measure on $\mathbb{R}^d$ such that $\mathrm{KL}(\rho_0 \,\|\, \pi) < \infty$. Let $(T_t)_{t \ge 0}$
solve the continuous-time SVGD equation from $\rho_0$, and let $\rho_t = (T_t)_\# \rho_0$. Then,
$t \mapsto \mathrm{KL}(\rho_t \,\|\, \pi)$ is differentiable on $[0, \infty)$, with a right
derivative at $0$, and
$$\forall t \ge 0, \quad \frac{d}{dt} \mathrm{KL}(\rho_t \,\|\, \pi) = -\mathfrak{K}(\rho_t \mid \pi).$$
```

```diagram SVGD.time_derivative_kl
L9: `SVGD.solution_properties_image`
  $T_t$ is a homeomorphism with $T_t(\Omega) = \Omega$
L10: `SVGD.jacobian_abs_log_le`
  $T_t$ is differentiable, $J_t > 0$, and $|\log J_t| \le d B K t$
L2: `SVGD.transport_kl` <- L9, L10
  $\mathrm{KL}(\rho_t \,\|\, \pi) = \mathrm{KL}(\rho_0 \,\|\, \pi) - \mathbb{E}_{x \sim \rho_0}[\ell(t, x)]$
  > Here, $\ell(t, x) = \log p(T_t(x)) - \log p(x) + \log J_t(x)$, and $J_t(x) = \det DT_t(x)$.
L10d: `SVGD.jacobian_hasDerivWithinAt`
  $\partial_t \log J_t(x) = \operatorname{div} v_t(T_t(x))$
der: step <- L10d, L9
  $\partial_t \ell(t, x) = \mathcal{A}_s v_t(T_t(x))$
  > Here, $v_t = (\phi^*_{\rho_t})_\Phi$ is the velocity field at time $t$. On $\Omega^\circ$, which $T_t$ preserves, by the chain rule. On $\partial \Omega$, $x$ is at rest by [Lemma 9 (iv)](#SVGD.solution_properties_boundary) and $v_t(x) = 0$, so that both sides vanish.
leib: Leibniz integral rule `hasDerivAt_integral_of_dominated_loc_of_deriv_le` [Folland1999] <- L2, der
  $\frac{d}{dt} \mathrm{KL}(\rho_t \,\|\, \pi) = -\mathbb{E}_{x \sim \rho_0}[\mathcal{A}_s v_t(T_t(x))]$
  > The derivative of $\ell$ is bounded by $M_s B C + d B K$, uniformly in $t$ and $x$.
cov: step <- leib
  $= -\mathbb{E}_{y \sim \rho_t}[\mathcal{A}_s v_t(y)]$
  > Change of variables $y = T_t(x)$.
T2: `SVGD.stein_witness_ksd_eq_integral`
  $\mathbb{E}_{y \sim \rho_t}[\mathcal{A}_s v_t(y)] = \mathfrak{K}(\rho_t \mid \pi)$
  > As $v_t$ is the vector field of the Stein witness of $\rho_t$ itself.
goal <- cov, T2
```

{{SVGD.time_derivative_kl_ne_top | Theorem 6}}

```informal SVGD.time_derivative_kl_ne_top | Time derivative of the KL divergence, finiteness
Under the assumptions of [Theorem 6](#SVGD.time_derivative_kl),
$\mathrm{KL}(\rho_t \,\|\, \pi) < \infty$ for every $t \ge 0$.
```

```sketch SVGD.time_derivative_kl_ne_top
[Lemma 2 (i)](#SVGD.transport_kl_ne_top) applies to $\Psi = T_t$, by
[Lemma 9 (iii)](#SVGD.solution_properties_image) and [Lemma 10](#SVGD.jacobian_abs_log_le).
```

{{SVGD.time_derivative_kl_antitoneOn | Theorem 6}}

```informal SVGD.time_derivative_kl_antitoneOn | Time derivative of the KL divergence, monotonicity
Under the assumptions of [Theorem 6](#SVGD.time_derivative_kl),
$t \mapsto \mathrm{KL}(\rho_t \,\|\, \pi)$ is nonincreasing on $[0, \infty)$.
```

```sketch SVGD.time_derivative_kl_antitoneOn
The derivative $-\mathfrak{K}(\rho_t \mid \pi)$ is nonpositive, and the mean value theorem concludes
(`antitoneOn_of_deriv_nonpos`).
```

The derivation of [Liu2017] uses the continuity equation satisfied by the density of $\rho_t$. The
proof above follows the particles instead. It never differentiates the density of $\rho_t$, and it
needs no regularity of $\partial \Omega$. It writes $\mathrm{KL}(\rho_t \,\|\, \pi)$ with Lemma 2,
as an integral against the fixed measure $\rho_0$, and differentiates the integrand along the
trajectories. The Jacobian determinant $J_t(x) = \det DT_t(x)$ of $T_t$ is studied first. Let
$v_t = b(\cdot, \rho_t)$ be the velocity field at time $t$.

{{SVGD.jacobian_differentiable | Lemma 10}}

```informal SVGD.jacobian_differentiable | Jacobian of $T_t$, differentiability
Suppose that the standing assumptions hold. Let $\rho_0$ be a probability measure on
$\mathbb{R}^d$, and let $(T_t)_{t \ge 0}$ solve the continuous-time SVGD equation from $\rho_0$.
Then, $T_t$ is differentiable on $\mathbb{R}^d$ for every $t \ge 0$.
```

```sketch SVGD.jacobian_differentiable
By [Lemma 9 (ii)](#SVGD.solution_properties_eq_positions), $T_t$ is the flow of $v_t$, whose
derivative is continuous in $(t, y)$, and the flow of such a field is differentiable in the initial
condition [Hartman2002].
```

{{SVGD.jacobian_pos | Lemma 10 (i)}}

```informal SVGD.jacobian_pos | Jacobian of $T_t$, positivity
Under the assumptions of [Lemma 10](#SVGD.jacobian_differentiable), $J_t(x) > 0$ for all
$x \in \mathbb{R}^d$ and $t \ge 0$.
```

```sketch SVGD.jacobian_pos
By [Lemma 10 (ii)](#SVGD.jacobian_hasDerivWithinAt), $t \mapsto J_t(x)$ solves a scalar linear
equation, with $J_0(x) = 1$, so it stays positive.
```

{{SVGD.jacobian_hasDerivWithinAt | Lemma 10 (ii)}}

```informal SVGD.jacobian_hasDerivWithinAt | Jacobian of $T_t$, Liouville's formula
Under the assumptions of [Lemma 10](#SVGD.jacobian_differentiable), for all $x \in \mathbb{R}^d$ and
$t \ge 0$,
$$\partial_t \log J_t(x) = \operatorname{div} v_t(T_t(x)),$$
with a right derivative at $t = 0$.
```

```diagram SVGD.jacobian_hasDerivWithinAt
m: `SVGD.solution_properties_continuous`
  $t \mapsto \phi^*_{\rho_t}$ is continuous
joint: step <- m
  $Dv_t(y)$ is continuous in $(t, y)$
  > $Dv_t(y) = P_{m(t)} \circ D\Phi(y)$, and $m$ and $D\Phi$ are continuous.
var: Differentiability in the initial condition `ODE.hasFDerivAt_apply_of_hasDerivAt_variational` [Hartman2002] <- joint
  $Y_t = DT_t(x)$ solves $\partial_t Y_t = Dv_t(T_t(x)) \, Y_t$, $Y_0 = I_d$
  > This is the variational equation. A small displacement of the initial position is transported by the derivative of the velocity field along the trajectory.
liou: Liouville's formula `hasDerivAt_det_of_hasDerivAt_comp` <- var
  $\partial_t \det Y_t = \operatorname{tr}\big(Dv_t(T_t(x))\big) \det Y_t$
  > By Jacobi's formula for the derivative of the determinant.
goal <- liou
  $\partial_t \log J_t(x) = \operatorname{div} v_t(T_t(x))$
  > As $J_t(x) > 0$ and $\operatorname{tr} Dv_t = \operatorname{div} v_t$.
```

{{SVGD.jacobian_abs_log_le | Lemma 10 (iii)}}

```informal SVGD.jacobian_abs_log_le | Jacobian of $T_t$, bound
Under the assumptions of [Lemma 10](#SVGD.jacobian_differentiable), let $B \ge 0$ such that
$\|\xi_x\|_{\mathcal{H}} \le B$ for every $x \in \Omega$. Then, for all $x \in \mathbb{R}^d$ and
$t \ge 0$, $|\log J_t(x)| \le d B K t$.
```

```sketch SVGD.jacobian_abs_log_le
$v_t$ is $B K$-Lipschitz, so that $|\operatorname{div} v_t| \le d B K$, and
[Lemma 10 (ii)](#SVGD.jacobian_hasDerivWithinAt) bounds the speed of $\log J_t(x)$, which is $0$ at
$t = 0$.
```

## Convergence

We now show that $\rho_t$ converges to $\pi$ when the kernel is rich enough.

### Weak convergence and Stein-universal kernels

Let $C^0(\Omega)$ be the set of the functions $g : \mathbb{R}^d \to \mathbb{R}$ continuous on
$\Omega$. A sequence $(\rho_n)$ of $\mathcal{P}(\Omega)$ converges weakly to $\rho$, written
$\rho_n \rightharpoonup \rho$, if $\mathbb{E}_{x \sim \rho_n}[g(x)] \to \mathbb{E}_{x \sim \rho}[g(x)]$
for every $g \in C^0(\Omega)$. This is the weak convergence of the restrictions of these measures to
the compact metric space $\Omega$ [Billingsley1999].

{{SVGD.ksd_eq_zero_iff | Property}}

```informal SVGD.ksd_eq_zero_iff | Zero KSD
Suppose that the standing assumptions hold and that $H_0$ is complete. Let
$\rho \in \mathcal{P}(\Omega)$. Then, $\mathfrak{K}(\rho \mid \pi) = 0 \iff \phi^*_\rho = 0$.
```

```sketch SVGD.ksd_eq_zero_iff
By [Theorem 2 (ii)](#SVGD.stein_witness_ksd), $\mathfrak{K}(\rho \mid \pi) =
\|\phi^*_\rho\|_{\mathcal{H}}^2$.
```

{{SVGD.steinWitness_eq_zero_iff | Property}}

```informal SVGD.steinWitness_eq_zero_iff | Zero KSD
Under the assumptions of the [Property above](#SVGD.ksd_eq_zero_iff),
$$\phi^*_\rho = 0 \iff \forall f \in \mathcal{H}, \quad \mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)] = 0.$$
```

```sketch SVGD.steinWitness_eq_zero_iff
By [Theorem 2](#SVGD.stein_witness), $\mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)] = \langle f,
\phi^*_\rho \rangle_{\mathcal{H}}$, and the converse takes $f = \phi^*_\rho$.
```

Thus, the KSD of $\rho$ vanishes if and only if $\rho$ satisfies Stein's identity for every
$f_\Phi$, as $\pi$ does. To deduce that $\rho = \pi$, the functions $\mathcal{A}_s f_\Phi$ must be
rich enough. For instance, if $D\Phi(y) = 0$ at some $y \in \partial \Omega$, then $\xi_y = 0$ and
$\mathfrak{K}(\delta_y \mid \pi) = 0$, whereas $\delta_y \neq \pi$. The figure below shows such a
kernel in dimension $1$.

```figure
figures/boundary_degeneracy.svg
A kernel whose KSD vanishes at Dirac masses that are not $\pi$. Here, $\Omega = [0, 1]$, the density
of $\pi$ is $p \propto e^{-3 f}$, with $f(x) = 16 x^2 (1 - x)^2$, and $k_0(x, y) = e^{-(x - y)^2 /
(2 \cdot 0.15^2)}$, as for the Stein witness above. The kernel is $k(x, y) = w(x) w(y) k_0(x, y)$
with $w(x) = 16 x^2 (1 - x)^2$. Its feature map is $\Phi = w \Phi_0$, where $\Phi_0$ is a feature
map of $k_0$. **a)** The weight $w$, in black, and its derivative $w'$, in blue, vanish on $\partial
\Omega = \{0, 1\}$ (red dots). Thus, so do $\Phi = w \Phi_0$ and $D\Phi = w' \Phi_0 + w \, D\Phi_0$.
**b)** The KSD of the Dirac mass at $x$. By [Theorem 2 (ii)](#SVGD.stein_witness_ksd),
$\mathfrak{K}(\delta_x \mid \pi) = \|\xi_x\|_{\mathcal{H}}^2 = (s(x) w(x) + w'(x))^2 + w(x)^2 /
0.15^2$. It is positive on $(0, 1)$, but it vanishes at $0$ and $1$ (red dots), whereas $\delta_0
\neq \pi$ and $\delta_1 \neq \pi$.
```

{{SVGD.IsSteinUniversal | Definition 3}}

```informal SVGD.IsSteinUniversal | Stein-universal kernel
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and
$\Omega \subseteq \mathbb{R}^d$. The kernel is Stein-universal if the set of the functions
$$\{\mathcal{A}_s f_\Phi + c \mid f \in \mathcal{H}, \ c \in \mathbb{R}\},$$
restricted to $\Omega$, is dense in the space of the continuous functions from $\Omega$ to
$\mathbb{R}$, with the topology of the uniform convergence on compact sets.
```

As $\Omega$ is compact, this is the uniform convergence on $\Omega$.

{{SVGD.isSteinUniversal_iff | Definition 3}}

```informal SVGD.isSteinUniversal_iff | Stein-universal kernel, unfolded
Suppose that the standing assumptions hold. Then, the kernel is Stein-universal if and only if
$$\forall g \in C^0(\Omega), \forall \eta > 0, \exists f \in \mathcal{H}, \exists c \in \mathbb{R}, \quad \sup_{x \in \Omega} |g(x) - \mathcal{A}_s f_\Phi(x) - c| \le \eta.$$
```

```sketch SVGD.isSteinUniversal_iff
As $\Omega$ is compact, the topology of the continuous functions on $\Omega$ is that of the uniform
norm, and $\mathcal{A}_s f_\Phi$ is continuous on $\Omega$.
```

{{SVGD.isSteinUniversal_iff_mean | Property}}

```informal SVGD.isSteinUniversal_iff_mean | Stein-universality through means
Suppose that the standing assumptions hold. Then, the kernel is Stein-universal if and only if
$$\forall g \in C^0(\Omega), \forall \eta > 0, \exists f \in \mathcal{H}, \quad \sup_{x \in \Omega} |g(x) - \mathbb{E}_{y \sim \pi}[g(y)] - \mathcal{A}_s f_\Phi(x)| \le \eta.$$
```

```sketch SVGD.isSteinUniversal_iff_mean
By [Corollary 1](#SVGD.stein_identity), $\mathcal{A}_s f_\Phi$ has mean zero under $\pi$, so that
integrating the bound of [Definition 3](#SVGD.isSteinUniversal_iff) against $\pi$ gives
$|\mathbb{E}_{y \sim \pi}[g(y)] - c| \le \eta / 2$, and the triangle inequality concludes.
```

{{SVGD.ksd_vanishes_only_at_target | Proposition 1}}

```informal SVGD.ksd_vanishes_only_at_target | The KSD vanishes only at $\pi$
Suppose that the standing assumptions hold, that $H_0$ is complete, and that the kernel is
Stein-universal. Let $\rho \in \mathcal{P}(\Omega)$. Then,
$\mathfrak{K}(\rho \mid \pi) = 0 \iff \rho = \pi$.
```

```diagram SVGD.ksd_vanishes_only_at_target
zero: `SVGD.steinWitness_eq_zero_iff`
  $\mathbb{E}_{x \sim \rho}[\mathcal{A}_s f_\Phi(x)] = 0$ for every $f \in \mathcal{H}$
  > As $\mathfrak{K}(\rho \mid \pi) = \|\phi^*_\rho\|_{\mathcal{H}}^2$, the KSD vanishes if and only if $\phi^*_\rho = 0$, i.e. if and only if this holds.
mean: `SVGD.isSteinUniversal_iff_mean`
  $g - \mathbb{E}_\pi[g]$ is a uniform limit on $\Omega$ of functions $\mathcal{A}_s f_\Phi$
eq: step <- zero, mean
  $\mathbb{E}_{x \sim \rho}[g(x)] = \mathbb{E}_{y \sim \pi}[g(y)]$ for every $g \in C^0(\Omega)$
  > $|\mathbb{E}_\rho[g] - \mathbb{E}_\pi[g]| = |\mathbb{E}_\rho[g - \mathbb{E}_\pi[g] - \mathcal{A}_s f_\Phi]| \le \eta$, for every $\eta > 0$.
ext: Measures and bounded continuous functions `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure` [Billingsley1999] <- eq
  $\rho = \pi$
  > Two finite measures on a metric space that give the same integral to every bounded continuous function are equal. Here, they are the restrictions of $\rho$ and $\pi$ to $\Omega$, which determine $\rho$ and $\pi$.
target: step
  $\mathfrak{K}(\pi \mid \pi) = 0$
  > By [Corollary 1](#SVGD.stein_identity), $\mathbb{E}_{x \sim \pi}[\mathcal{A}_s f_\Phi(x)] = 0$ for every $f \in \mathcal{H}$. This gives the converse implication.
goal <- ext, target
```

### Convergence to the target distribution

{{SVGD.convergence_to_target | Theorem 7}}

```informal SVGD.convergence_to_target | Convergence to the target distribution
Suppose that the standing assumptions hold, that $H_0$ is complete, and that the kernel is
Stein-universal. Let $\rho_0$ be a probability measure on $\mathbb{R}^d$ such that
$\mathrm{KL}(\rho_0 \,\|\, \pi) < \infty$. Let $(T_t)_{t \ge 0}$ solve the continuous-time SVGD
equation from $\rho_0$, and let $\rho_t = (T_t)_\# \rho_0$. Then, for every $g \in C^0(\Omega)$,
$$\mathbb{E}_{x \sim \rho_t}[g(x)] \xrightarrow[t \to \infty]{} \mathbb{E}_{x \sim \pi}[g(x)].$$
```

```diagram SVGD.convergence_to_target
crit: Subsequences `tendsto_of_subseq_tendsto`
  it is enough that every $t_n \to \infty$ has a subsequence along which $\mathbb{E}_{\rho_t}[g] \to \mathbb{E}_\pi[g]$
prok: Prokhorov's theorem `instCompactSpaceProbabilityMeasure` [Billingsley1999]
  the probability measures on the compact set $\Omega$ form a compact space
  > For the weak convergence. On a compact space, the tightness condition holds with the whole space.
sub: step <- prok
  $(\rho_{t_n})$ has a subsequence $\rho_{\tau_k} \rightharpoonup \rho_\infty$
L13: `SVGD.limit_points_ksd_eq_zero` <- sub
  $\mathfrak{K}(\rho_\infty \mid \pi) = 0$
P1: `SVGD.ksd_vanishes_only_at_target` <- L13
  $\rho_\infty = \pi$
goal <- crit, P1
```

For the particles, Theorem 7 states that the average of $g$ over the positions at time $t$,
$\mathbb{E}_{x \sim \rho_0}[g(T_t(x))]$, tends to its average under $\pi$. It has four limitations.
It gives no rate of convergence. It concerns the continuous-time dynamics, and not the iteration of
SVGD. The assumption $\mathrm{KL}(\rho_0 \,\|\, \pi) < \infty$ excludes the empirical measures of
finitely many particles. Finally, it assumes that the kernel is Stein-universal.

The proof has three steps. First, $\mathfrak{K}(\rho_t \mid \pi) \to 0$ (Corollary 2). This does
not follow from the convergence of the divergence alone, as a function can converge while its
derivative keeps oscillating. The uniform continuity of the KSD excludes these oscillations, by
Barbalat's lemma. Second, the limit points of $\rho_t$ have a zero KSD (Lemma 13). Third, they are
equal to $\pi$ (Proposition 1). Only the last step uses the Stein-universality of the kernel.

### The KSD tends to zero

The figure below shows a function that converges while its derivative does not tend to $0$.
Barbalat's lemma states that uniform continuity excludes this behavior.

```figure
figures/converging_spikes.svg
A function that converges while its derivative does not tend to $0$. **Top.** The function
$F(t) = \ell + \int_t^\infty \theta(\tau) \, d\tau$ decreases to its limit $\ell$ (dashed).
**Bottom.** Its derivative $-F' = \theta$, with $\theta(t) = \sum_{n \ge 1} \max(0, 1 - n^2 |t - n|)$,
keeps reaching the height $1$ (dashed). Its spikes have area $1 / n^2$ and get thinner and thinner,
so that $\theta$ is not uniformly continuous. Here, $F$ plays the role of
$t \mapsto \mathrm{KL}(\rho_t \,\|\, \pi)$, and $\theta$ the role of
$t \mapsto \mathfrak{K}(\rho_t \mid \pi)$. This illustrates why
[Lemma 11](#SVGD.barbalat) requires uniform continuity.
```

{{SVGD.barbalat | Lemma 11}}

```informal SVGD.barbalat | Barbalat
Let $u : \mathbb{R} \to \mathbb{R}$ be uniformly continuous on $[0, \infty)$, with $u(t) \ge 0$ for
every $t \ge 0$. Let $M \in \mathbb{R}$ such that $\int_0^a u(t) \, dt \le M$ for every $a \ge 0$.
Then, $u(t) \to 0$ as $t \to \infty$.
```

```sketch SVGD.barbalat
Otherwise, $u \ge \eta$ at times $t_n$ with $t_{n+1} \ge t_n + 1$, and by uniform continuity
$u \ge \eta / 2$ on intervals $[t_n, t_n + \delta]$, whose contributions make the integral unbounded
[Khalil2002].
```

{{SVGD.ksd_uniform_continuity_le | Lemma 12}}

```informal SVGD.ksd_uniform_continuity_le | Uniform continuity of the KSD, bound
Suppose that the standing assumptions hold and that $H_0$ is complete. Let $\rho_0$ be a
probability measure on $\mathbb{R}^d$, let $(T_t)_{t \ge 0}$ solve the continuous-time SVGD
equation from $\rho_0$, and let $\rho_t = (T_t)_\# \rho_0$. Let $B \ge 0$ such that
$\|\xi_x\|_{\mathcal{H}} \le B$ for every $x \in \Omega$. Then,
$$\forall t, t' \ge 0, \quad |\mathfrak{K}(\rho_t \mid \pi) - \mathfrak{K}(\rho_{t'} \mid \pi)| \le 2 B \, \omega(B C |t - t'|).$$
```

```sketch SVGD.ksd_uniform_continuity_le
By [Theorem 2 (ii)](#SVGD.stein_witness_ksd), the difference is $(\|\phi^*_{\rho_t}\| +
\|\phi^*_{\rho_{t'}}\|) \, \big| \|\phi^*_{\rho_t}\| - \|\phi^*_{\rho_{t'}}\| \big| \le 2 B \,
\|\phi^*_{\rho_t} - \phi^*_{\rho_{t'}}\|$, and [Lemma 9 (i)](#SVGD.solution_properties_dist_le)
concludes.
```

{{SVGD.ksd_uniform_continuity | Lemma 12}}

```informal SVGD.ksd_uniform_continuity | Uniform continuity of the KSD
Under the assumptions of [Lemma 12](#SVGD.ksd_uniform_continuity_le),
$t \mapsto \mathfrak{K}(\rho_t \mid \pi)$ is uniformly continuous on $[0, \infty)$.
```

```sketch SVGD.ksd_uniform_continuity
By [Lemma 12](#SVGD.ksd_uniform_continuity_le), with the bound $B$ of Lemma 4 (ii), as
$\omega(r) \to 0$ as $r \to 0$.
```

{{SVGD.ksd_convergence | Corollary 2}}

```informal SVGD.ksd_convergence | Convergence of the KSD
Under the assumptions of [Lemma 12](#SVGD.ksd_uniform_continuity_le), suppose that
$\mathrm{KL}(\rho_0 \,\|\, \pi) < \infty$. Then,
$$\mathfrak{K}(\rho_t \mid \pi) \xrightarrow[t \to \infty]{} 0.$$
```

```diagram SVGD.ksd_convergence
T6: `SVGD.time_derivative_kl`
  $F' = -u$ on $[0, \infty)$
  > Here, $F(t) = \mathrm{KL}(\rho_t \,\|\, \pi)$ and $u(t) = \mathfrak{K}(\rho_t \mid \pi)$.
L12: `SVGD.ksd_uniform_continuity`
  $u$ is uniformly continuous on $[0, \infty)$
ftc: Fundamental theorem of calculus `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` <- T6, L12
  $\int_0^a u = F(0) - F(a) \le F(0)$
  > It applies, as $u$ is continuous. Moreover, $F(a) \ge 0$, as the Kullback–Leibler divergence is nonnegative.
bar: `SVGD.barbalat` <- ftc, L12
  $u(t) \to 0$
goal <- bar
```

As $\mathfrak{K}(\rho_t \mid \pi) = \|\phi^*_{\rho_t}\|_{\mathcal{H}}^2$, the velocity of the
particles tends to $0$, uniformly in space. This does not yet show that $\rho_t$ converges.

### Limit points of the dynamics

{{SVGD.limit_points_ksd_eq_zero | Lemma 13}}

```informal SVGD.limit_points_ksd_eq_zero | Limit points have a zero KSD
Under the assumptions of [Corollary 2](#SVGD.ksd_convergence), let $(t_n)_{n \in \mathbb{N}}$ be a
sequence with $t_n \to \infty$, and let $\rho_\infty$ be a measure on $\mathbb{R}^d$ such that
$$\forall g \in C^0(\Omega), \quad \mathbb{E}_{x \sim \rho_{t_n}}[g(x)] \xrightarrow[n \to \infty]{} \int g \, d\rho_\infty.$$
Then, $\mathfrak{K}(\rho_\infty \mid \pi) = 0$.
```

```sketch SVGD.limit_points_ksd_eq_zero
For $f$ in the closed unit ball, $\mathbb{E}_{\rho_{t_n}}[\mathcal{A}_s f_\Phi]^2 \le
\mathfrak{K}(\rho_{t_n} \mid \pi) \to 0$ by [Corollary 2](#SVGD.ksd_convergence), and
$\mathcal{A}_s f_\Phi \in C^0(\Omega)$, so $\mathbb{E}_{\rho_\infty}[\mathcal{A}_s f_\Phi] = 0$.
```

The statement of Lemma 13 does not assume that $\rho_\infty \in \mathcal{P}(\Omega)$. This
hypothesis is not needed, as the weak convergence is given by its definition on the integrals, and
as an integral is always defined in Lean. Theorem 7 applies the lemma to a limit that lies in
$\mathcal{P}(\Omega)$.

```informal 𝓗[d, H₀] | The space $\mathcal{H}$
Let $H_0$ be a real inner product space. Then, $\mathcal{H} = H_0^d$ is the product of $d$ copies
of $H_0$, with the inner product
$$\langle f, g \rangle_{\mathcal{H}} = \sum_{i=1}^d \langle f_i, g_i \rangle_{H_0}.$$
```

```informal divergence | The divergence
Let $\mathbb{K}$ be a nontrivially normed field and $E$ a normed space over $\mathbb{K}$. For
$f : E \to E$ and $x \in E$,
$$\operatorname{div} f(x) = \operatorname{tr} Df(x),$$
where $Df(x)$ is the derivative of $f$ at $x$, equal to $0$ if $f$ is not differentiable at $x$.
The trace is equal to $0$ if $E$ is not finite-dimensional. If $E = \mathbb{R}^d$ and $f$ is
differentiable at $x$, then $\operatorname{div} f(x) = \sum_{i=1}^d \partial_i f_i(x)$.
```

```informal modulusOfContinuityOn | The modulus of continuity
Let $\alpha$ and $\beta$ be metric spaces, let $f : \alpha \to \beta$, let $S \subseteq \alpha$ and
let $r \in \mathbb{R}$. The modulus of continuity of $f$ on $S$ is
$$\omega(r) = \sup \{d(f(x), f(y)) \mid x, y \in S, \ d(x, y) \le r\},$$
a supremum of real numbers, equal to $0$ if this set is empty or unbounded.
```

```informal ODE.integralCurveThrough | The solution of an ODE
Let $E$ be a real normed space and $v : \mathbb{R} \times E \to E$ a time-dependent vector field.
An integral curve of $v$ is a curve $\alpha : \mathbb{R} \to E$, differentiable at every
$t \in \mathbb{R}$, with $\alpha'(t) = v(t, \alpha(t))$. Let $t_0 \in \mathbb{R}$ and $x \in E$. If
$v$ has an integral curve $\alpha$ with $\alpha(t_0) = x$, then $\operatorname{sol}_v(t_0, x)$ is one
of them, chosen with the axiom of choice. Otherwise, $\operatorname{sol}_v(t_0, x)$ is the constant
curve $t \mapsto x$. When $v$ is continuous in time and Lipschitz in space, the integral curve exists
and is unique.
```

```informal SVGD.pairing | The pairing $P_f$
Let $H_0$ be a real inner product space and $f = (f_1, \dots, f_d) \in \mathcal{H}$. The pairing of
$f$ is the continuous linear map
$$P_f : H_0 \to \mathbb{R}^d, \qquad u \mapsto \big(\langle f_1, u \rangle_{H_0}, \dots, \langle f_d, u \rangle_{H_0}\big).$$
```

```informal SVGD.toVectorField | The vector field $f_\Phi$
Let $\Phi : \mathbb{R}^d \to H_0$ and $f \in \mathcal{H}$. The vector field of $f$ is
$$f_\Phi : \mathbb{R}^d \to \mathbb{R}^d, \qquad y \mapsto P_f(\Phi(y)) = \big(\langle f_1, \Phi(y) \rangle_{H_0}, \dots, \langle f_d, \Phi(y) \rangle_{H_0}\big).$$
If $H_0$ is the RKHS of a kernel $k_0$ and $\Phi(y) = k_0(\cdot, y)$, then
$f_\Phi(y) = (f_1(y), \dots, f_d(y))$ by the reproducing property.
```

```informal SVGD.trajectory | The trajectories
Let $\Phi : \mathbb{R}^d \to H_0$, let $m : \mathbb{R} \to \mathcal{H}$ be a curve, $s \in \mathbb{R}$
and $x \in \mathbb{R}^d$. The trajectory of $m$ through $x$ at time $s$ is
$\operatorname{sol}_v(s, x)$, where $v(t, y) = m(t)_\Phi(y)$. The positions of Lemma 5 are
$T^m_t(x) = \operatorname{sol}_v(0, x)(t)$.
```
