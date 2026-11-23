---
title: SVGD on a compact domain
subtitle: A Lean 4 formalization of the convergence theory of Stein Variational Gradient Descent
paper: Stein Boltzmann Sampling (G. Serré, A. Kalogeratos, N. Vayatis), AISTATS 2025
abstract: >
  This formalization follows the theoretical appendix of *Stein Boltzmann Sampling*. On a compact
  domain $\Omega \subseteq \mathbb{R}^d$, it proves that the mean-field SVGD flow exists, that the Kullback–Leibler
  divergence to the target decreases along it at the rate of the kernelized Stein discrepancy, and
  that the flow converges weakly to the target when the kernel is Stein-universal. It also builds an
  explicit kernel on $[-1, 1]$ that satisfies every hypothesis. There is no `sorry`.
module: CompactSVGD.Paper
trusted:
  - CompactSVGD.Definitions
docgen: https://gaetanserre.fr/CompactSVGD/docs/
# The source links point to `<repository>/blob/<commit>/<file>#L<line>`. Without this line, the
# repository is the `origin` remote of git; the commit is the current one (`git rev-parse HEAD`).
repository: https://github.com/gaetanserre/CompactSVGD
bibliography: ../docs/references.bib
links:
  divergence: https://en.wikipedia.org/wiki/Divergence
  ContinuousLinearMap.traceCLM: https://en.wikipedia.org/wiki/Trace_(linear_algebra)
  ODE.globalSolution: https://en.wikipedia.org/wiki/Integral_curve
  SVGD.toVectorField: https://en.wikipedia.org/wiki/Reproducing_kernel_Hilbert_space
  SVGD.trajectory: https://en.wikipedia.org/wiki/Flow_(mathematics)
  SVGD.seqFeatureMap: https://en.wikipedia.org/wiki/Kernel_method
  ProbabilityTheory.steinOperator: https://en.wikipedia.org/wiki/Stein%27s_method
  ProbabilityTheory.steinClass: https://en.wikipedia.org/wiki/Stein%27s_method
  SVGD.kernelSteinDiscrepancy: https://en.wikipedia.org/wiki/Stein_discrepancy
  SVGD.klFirstVariation: https://en.wikipedia.org/wiki/Kullback%E2%80%93Leibler_divergence
  SVGD.AdmissibleTarget: https://en.wikipedia.org/wiki/Probability_density_function
  SVGD.intervalCutoff: https://en.wikipedia.org/wiki/Bump_function
---

Stein Variational Gradient Descent (SVGD) moves a cloud of particles so that their empirical
law approaches a target distribution $\pi$. Its mean-field limit is a flow of probability measures
$(\mu_t)_{t \ge 0}$. This page presents the theory of this flow on a compact domain
$\Omega \subseteq \mathbb{R}^d$, as formalized in Lean. Each statement and each proof below is a
translation of the Lean code. The proof, the Lean statement and the Lean proof of each result can be
unfolded below it.

## The setting

Most results share one hypothesis, the standing assumptions. They fix the domain $\Omega \subseteq \mathbb{R}^d$, the target $\pi$ and the kernel $k$.

The target $\pi$ has a density $p$ with respect to the Lebesgue measure $\lambda$ on $\Omega$, and a score $s = \nabla \log p$.

{{SVGD.AdmissibleTarget | Definition}}

```informal SVGD.AdmissibleTarget
Let $\Omega \subseteq \mathbb{R}^d$ and let $\pi$ be a measure on $\mathbb{R}^d$. Let $p : \mathbb{R}^d \to \mathbb{R}$ and $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$, where $(\mathbb{R}^d)^*$ is the space of linear forms on $\mathbb{R}^d$, with the operator norm. The target $\pi$, with density $p$ and score $s$, is admissible on $\Omega$ if the following seven conditions hold.

(i) $\pi(A) = \int_A \max(p, 0) \, d\lambda|_\Omega$ for every Borel set $A \subseteq \mathbb{R}^d$, where $\lambda|_\Omega$ is the restriction of $\lambda$ to $\Omega$. By (v), $\max(p, 0) = p$ on $\Omega$, and we write $\pi = p \cdot \lambda|_\Omega$.

(ii) $\pi$ is a probability measure.

(iii) $p$ is measurable.

(iv) $p$ is continuous on $\Omega$.

(v) $p(x) > 0$ for every $x \in \Omega$.

(vi) For every $x$ in the interior $\operatorname{int} \Omega$ of $\Omega$, the function $\log p$ is differentiable at $x$ and $D(\log p)(x) = s(x)$. Thus, $s = \nabla \log p$ on $\operatorname{int} \Omega$.

(vii) $s$ is continuous on $\Omega$.
```

The kernel is $k(x, y) = \langle \Phi(x), \Phi(y) \rangle$, given by a feature map $\Phi$ with values in a real inner product space $H_0$.

{{SVGD.AdmissibleFeatureMap | Definition}}

```informal SVGD.AdmissibleFeatureMap
Let $H_0$ be a real inner product space, $\Phi : \mathbb{R}^d \to H_0$, $\Omega \subseteq \mathbb{R}^d$ and $K, C \ge 0$. The feature map $\Phi$, of kernel $k(x, y) = \langle \Phi(x), \Phi(y) \rangle$, is admissible on $\Omega$ with constants $K$ and $C$ if the following four conditions hold.

(i) $\Phi$ is continuously differentiable on $\mathbb{R}^d$.

(ii) $\Phi$ is $K$-Lipschitz, i.e. $\|\Phi(x) - \Phi(y)\| \le K \|x - y\|$ for every $x, y \in \mathbb{R}^d$, where $\mathbb{R}^d$ has the Euclidean norm.

(iii) $\|\Phi(y)\| \le C$ for every $y \in \mathbb{R}^d$.

(iv) $\Phi(y) = 0$ for every $y$ in the boundary $\partial \Omega = \overline{\Omega} \setminus \operatorname{int} \Omega$ of $\Omega$.
```

Condition (iv) makes every vector field $h_\Phi$, for $h \in \mathcal{H}$, vanish on $\partial \Omega$. This is what keeps the particles in $\Omega$.

The standing assumptions gather a compact domain, an admissible target and an admissible feature map. Most results below take them as a hypothesis, plus their own hypotheses. Every statement lists all its hypotheses explicitly.

{{SVGD.StandingAssumptions | Assumptions}}

```informal SVGD.StandingAssumptions
Let $d \in \mathbb{N}$ and let $H_0$ be a real inner product space. Let $\Omega \subseteq \mathbb{R}^d$, $\pi$ a measure on $\mathbb{R}^d$, $p : \mathbb{R}^d \to \mathbb{R}$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$, $\Phi : \mathbb{R}^d \to H_0$ and $K, C \ge 0$. The standing assumptions are the following three conditions.

(i) $\Omega$ is compact.

(ii) The target $\pi$, with density $p$ and score $s$, is [admissible](#SVGD.AdmissibleTarget) on $\Omega$.

(iii) The feature map $\Phi$ is [admissible](#SVGD.AdmissibleFeatureMap) on $\Omega$ with constants $K$ and $C$.
```

In the following, we write $\mu \in \mathcal{P}(\Omega)$ when $\mu$ is a probability measure on $\mathbb{R}^d$ such that $x \in \Omega$ for $\mu$-almost every $x$.

## Stein's method

The Stein operator turns a vector field $v$ into a real function. Stein's identity states that the mean of this function under the target vanishes when $v$ is differentiable almost everywhere and in the Stein class.

We state these notions on a real normed space $E$, with a reference measure $\rho$. The setting of [Serre2025] is $E = \mathbb{R}^d$ and $\rho = \lambda|_\Omega$.

{{ProbabilityTheory.steinOperator | Definition}}

```informal ProbabilityTheory.steinOperator
Let $E$ be a real normed space and $E^*$ the space of continuous linear forms on $E$. Let $s : E \to E^*$ and let $v : E \to E$ be a vector field. The Stein operator with score $s$ maps $v$ to the function $\mathcal{A}_s v : E \to \mathbb{R}$ defined by
$$\mathcal{A}_s v(x) = s(x)\big(v(x)\big) + \operatorname{div} v(x).$$
The divergence $\operatorname{div} v(x) = \operatorname{tr} Dv(x)$ is $0$ if $v$ is not differentiable at $x$, or if $E$ is not finite-dimensional. If $E = \mathbb{R}^d$ and $s = \nabla \log p$ for a density $p$, then $\mathcal{A}_s v = \nabla \log p^\top v + \nabla \cdot v$ wherever $v$ is differentiable.
```

In [Serre2025], the Stein class is defined by $v \in H^1(\Omega)$ and a boundary condition. The formalization asks instead that $p v$ is differentiable almost everywhere, with an integrable divergence of integral $0$. With $\rho = \lambda|_\Omega$, a regular boundary $\partial \Omega$ and a regular enough $p v$, the divergence theorem turns the last condition into $\oint_{\partial \Omega} p v \cdot \vec{n} \, dS = 0$, where $\vec{n}$ is the outward unit normal.

{{ProbabilityTheory.steinClass | Definition A.2}}

```informal ProbabilityTheory.steinClass
Let $E$ be a real normed space, endowed with a $\sigma$-algebra. Let $\rho$ be a measure on $E$ and $p : E \to \mathbb{R}$. The Stein class $\mathcal{S}_\rho(p)$ of $p$ with respect to $\rho$ is the set of vector fields $v : E \to E$ that satisfy the following three conditions.

(i) The vector field $p v : x \mapsto p(x) v(x)$ is differentiable at $\rho$-almost every $x \in E$.

(ii) The function $\operatorname{div}(p v)$ is $\rho$-integrable.

(iii) $\displaystyle \int_E \operatorname{div}(p v)(x) \, d\rho(x) = 0$.
```

The score enters Stein's identity through $Dp = p \, s$, i.e. $s = \nabla \log p$ where $p > 0$. Then, for $v$ differentiable almost everywhere and in the Stein class, the Stein operator has integral $0$ against $p \cdot \rho$.

{{ProbabilityTheory.stein_identity | Lemma A.3}}

```informal ProbabilityTheory.stein_identity
Let $E$ be a finite-dimensional real normed space, endowed with a $\sigma$-algebra, and let $\rho$ be a measure on $E$. Let $p : E \to \mathbb{R}$ be $\rho$-almost everywhere measurable, with $p \ge 0$ $\rho$-almost everywhere. Let $s : E \to E^*$ be such that, for $\rho$-almost every $x \in E$, $p$ is differentiable at $x$ and
$$Dp(x) = p(x) \, s(x).$$
Let $v : E \to E$ be differentiable at $\rho$-almost every $x \in E$, with $v \in \mathcal{S}_\rho(p)$. Then,
$$\int_E \mathcal{A}_s v(x) \, d(p \cdot \rho)(x) = 0,$$
where $p \cdot \rho$ is the measure of density $\max(p, 0)$ with respect to $\rho$, and where the integral is $0$ by convention if $\mathcal{A}_s v$ is not $(p \cdot \rho)$-integrable.
```

```proof ProbabilityTheory.stein_identity
Integrating against $p \cdot \rho$ multiplies the integrand by the density. As $\max(p, 0)$ is $\rho$-almost everywhere measurable and finite, we have that, for every $g : E \to \mathbb{R}$,
$$\int_E g \, d(p \cdot \rho) = \int_E \max(p, 0) \, g \, d\rho.$$
This identity needs no integrability. Indeed, $g$ is $(p \cdot \rho)$-integrable if and only if $\max(p, 0) \, g$ is $\rho$-integrable, and both integrals are $0$ otherwise. By condition (iii) of the Stein class, $\int_E \operatorname{div}(p v) \, d\rho = 0$. As two functions equal $\rho$-almost everywhere have the same integral, it is sufficient to show that
$$\max(p(x), 0) \, \mathcal{A}_s v(x) = \operatorname{div}(p v)(x)$$
for $\rho$-almost every $x \in E$.

By hypothesis, $\rho$-almost every $x \in E$ satisfies $p(x) \ge 0$ and $Dp(x) = p(x) \, s(x)$, with $v$ differentiable at $x$. Let $x$ be such a point. Then, $\max(p(x), 0) = p(x)$.

We use the following product rule for the divergence. Let $E$ be finite-dimensional, let $c : E \to \mathbb{R}$ be differentiable at $x$ with $Dc(x) = c(x) \, L$ for some $L \in E^*$, and let $f : E \to E$ be differentiable at $x$. Then,
$$\operatorname{div}(c f)(x) = c(x) \big( L(f(x)) + \operatorname{div} f(x) \big).$$
It follows from the product rule $D(c f)(x)(w) = c(x) \, Df(x)(w) + Dc(x)(w) \, f(x)$, for $w \in E$. As the trace of the rank-one map $w \mapsto Dc(x)(w) \, f(x)$ is $Dc(x)(f(x))$, we have that $\operatorname{div}(c f)(x) = c(x) \operatorname{div} f(x) + Dc(x)(f(x))$. It remains to substitute $Dc(x)(f(x)) = c(x) \, L(f(x))$.

Applying this lemma with $c = p$, $L = s(x)$ and $f = v$, we have that
$$\begin{aligned} \operatorname{div}(p v)(x) &= p(x) \big( s(x)(v(x)) + \operatorname{div} v(x) \big) \\ &= p(x) \, \mathcal{A}_s v(x), \end{aligned}$$
which concludes the proof.
```

In the rest of the paper, $s$ is the score of the target $\pi$, and we write $\mathcal{A}_\pi f = \mathcal{A}_s(f_\Phi)$ for $f \in \mathcal{H}$, as in [Serre2025].

## The kernelized Stein discrepancy

The kernel is $k(x, y) = \langle \Phi(x), \Phi(y) \rangle$, and its RKHS is represented by the real inner product space $H_0$. The product RKHS of [Serre2025] (Definition A.4) is the space $\mathcal{H} = H_0^d$ of the $d$-tuples $f = (f_1, \dots, f_d)$ of elements of $H_0$, with the inner product $\langle f, g \rangle_{\mathcal{H}} = \sum_{i=1}^d \langle f_i, g_i \rangle_{H_0}$. It is a Hilbert space when $H_0$ is. An element $f \in \mathcal{H}$ acts on $\mathbb{R}^d$ through its [vector field](#SVGD.toVectorField)
$$f_\Phi(y) = \big(\langle f_1, \Phi(y) \rangle, \dots, \langle f_d, \Phi(y) \rangle\big),$$
where $\Phi(y)$ plays the role of $k(\cdot, y)$. Thus, the reproducing property $f_i(y) = \langle f_i, k(\cdot, y) \rangle_{H_0}$ holds by definition. Its derivative form $\partial_i f_i(y) = \langle f_i, \partial_i k(\cdot, y) \rangle_{H_0}$ follows from the differentiability of $\Phi$. Together they give $\mathcal{A}_\pi f(x) = \langle f, \xi_x \rangle_{\mathcal{H}}$ at every $x$ where $\Phi$ is differentiable, for the element $\xi_x \in \mathcal{H}$ defined below (see the [reproducing property](#SVGD.reproducing_property)).

Nothing else is used about RKHS. The formalization needs neither the uniqueness of the RKHS, nor the integral positive definiteness of $k$, nor the density of $H_0$ in $L^2$. Every RKHS fits this setting, with its canonical feature map $x \mapsto k(\cdot, x)$. Conversely, $\mathcal{H}$ may contain elements whose vector field vanishes, namely those whose components are orthogonal to every $\Phi(y)$ and $\partial_i \Phi(y)$. They play no role in $\mathcal{A}_\pi f$, in the KSD, in $\varphi^*_\mu$ or in Stein-universality (Definition A.9).

The update direction $\varphi^*_\mu$ of SVGD is the mean under $\mu$ of an element $\xi_x$ of $\mathcal{H}$ that does not depend on $\mu$.

{{SVGD.steinFeature | Definition}}

```informal SVGD.steinFeature | The Stein feature $\xi$
Let $\Phi : \mathbb{R}^d \to H_0$ and $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$. Let $(e_1, \dots, e_d)$ be the canonical basis of $\mathbb{R}^d$. For $x \in \mathbb{R}^d$, the element $\xi_x \in \mathcal{H}$ is defined by
$$(\xi_x)_i = s(x)(e_i)\, \Phi(x) + D\Phi(x)(e_i), \qquad 1 \le i \le d,$$
where $D\Phi(x) = 0$ if $\Phi$ is not differentiable at $x$. When $s = \nabla \log p$ and $\Phi(x) = k(\cdot, x)$, this is the element $\xi_x = \nabla \log p(x)\, k(\cdot, x) + \nabla_x k(\cdot, x)$ of [Serre2025].
```

{{SVGD.direction | Definition}}

```informal SVGD.direction | The update direction
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $\mu$ a measure on $\mathbb{R}^d$. The update direction of SVGD is the Bochner integral
$$\varphi^*_\mu = \int \xi_x \, \mathrm{d}\mu(x) \in \mathcal{H}.$$
By convention, $\varphi^*_\mu = 0$ if $x \mapsto \xi_x$ is not $\mu$-integrable, or if $\mathcal{H}$ is not complete. The measure $\mu$ is arbitrary. It need not have a density, nor be a probability measure.
```

The KSD is the largest violation of Stein's identity (Lemma A.3) over the closed unit ball of $\mathcal{H}$. It depends on $\pi$ only through its score $s$.

{{SVGD.kernelSteinDiscrepancy | Definition A.5}}

```informal SVGD.kernelSteinDiscrepancy
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $\mu$ a measure on $\mathbb{R}^d$. For $f \in \mathcal{H}$, let $\mathcal{A}_\pi f = \mathcal{A}_s (f_\Phi)$ be the [Stein operator](#ProbabilityTheory.steinOperator) applied to the vector field of $f$. The kernelized Stein discrepancy (KSD) of $\mu$ with respect to $\pi$ is
$$\mathfrak{K}(\mu \mid \pi) = \sup_{f \in \mathcal{H}, \ \|f\|_{\mathcal{H}} \le 1} \left( \int \mathcal{A}_\pi f(x) \, \mathrm{d}\mu(x) \right)^2.$$
The supremum is a supremum in $\mathbb{R}$ over the closed unit ball of $\mathcal{H}$. By convention, it is $0$ if the family is not bounded above. Each integral is $0$ if $\mathcal{A}_\pi f$ is not $\mu$-integrable.
```

The paper defines the KSD as a maximum, for $\mu \in \mathcal{P}(\Omega)$. The definition above is a supremum, for every measure. Under the standing assumptions, with $H_0$ a Hilbert space and $\mu \in \mathcal{P}(\Omega)$, the proof of Theorem A.7 (iii) shows that the family is bounded and that the supremum is attained.

{{SVGD.ksd_nonneg | Lemma}}

```informal SVGD.ksd_nonneg | Nonnegativity of the KSD
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $\mu$ a measure on $\mathbb{R}^d$. Then,
$$\mathfrak{K}(\mu \mid \pi) \ge 0.$$
```

```proof SVGD.ksd_nonneg
Every term $\left( \int \mathcal{A}_\pi f \, \mathrm{d}\mu \right)^2$ is a square, hence nonnegative. The family is nonempty, as $0$ lies in the closed unit ball. If the family is bounded above, its supremum is at least any of its terms, hence nonnegative. Otherwise, the supremum is $0$ by convention. In both cases, the supremum is nonnegative, which concludes the proof.
```

The next lemma is the identity behind the closed form of the KSD. It holds at every point where $\Phi$ is differentiable, with no assumption on $s$.

{{SVGD.reproducing_property | Lemma}}

```informal SVGD.reproducing_property
Let $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $x \in \mathbb{R}^d$ such that $\Phi$ is differentiable at $x$. Then, for every $f \in \mathcal{H}$,
$$\mathcal{A}_\pi f(x) = \langle f, \xi_x \rangle_{\mathcal{H}}.$$
```

```proof SVGD.reproducing_property
Let $f \in \mathcal{H}$. In the canonical basis $(e_1, \dots, e_d)$ of $\mathbb{R}^d$, the vector field of $f$ at $x$ is
$$f_\Phi(x) = \sum_{i=1}^d \langle f_i, \Phi(x) \rangle \, e_i.$$
The map $f_\Phi = P_f \circ \Phi$ is the composition of $\Phi$ with the continuous linear map $P_f : u \mapsto \big(\langle f_i, u \rangle_{H_0}\big)_{1 \le i \le d}$ from $H_0$ to $\mathbb{R}^d$. By the chain rule, $f_\Phi$ is differentiable at $x$ and $Df_\Phi(x) = P_f \circ D\Phi(x)$. On $\mathbb{R}^d$, the divergence is the trace in the canonical basis, i.e.
$$\operatorname{div} f_\Phi(x) = \sum_{i=1}^d \big(Df_\Phi(x)(e_i)\big)_i.$$
As $s(x)$ is linear and $\big(P_f(u)\big)_i = \langle f_i, u \rangle$, we have that
$$\begin{aligned} \mathcal{A}_\pi f(x) &= s(x)\big(f_\Phi(x)\big) + \operatorname{div} f_\Phi(x) \\ &= \sum_{i=1}^d \langle f_i, \Phi(x) \rangle \, s(x)(e_i) + \sum_{i=1}^d \big(P_f(D\Phi(x)(e_i))\big)_i \\ &= \sum_{i=1}^d \Big( \langle f_i, \Phi(x) \rangle \, s(x)(e_i) + \langle f_i, D\Phi(x)(e_i) \rangle_{H_0} \Big) \\ &= \sum_{i=1}^d \big\langle f_i, s(x)(e_i)\, \Phi(x) + D\Phi(x)(e_i) \big\rangle_{H_0} \\ &= \sum_{i=1}^d \langle f_i, (\xi_x)_i \rangle_{H_0} = \langle f, \xi_x \rangle_{\mathcal{H}}, \end{aligned}$$
which concludes the proof.
```

The next lemma gives the regularity of $\xi$ on $\Omega$. Its five parts are five separate results. All of them except (iv) take the [standing assumptions](#SVGD.StandingAssumptions). The paper sets $B = \max_{x \in \Omega} \|\xi_x\|_{\mathcal{H}}$. Here, (iv) and (v) take any bound $B$ of $\|\xi_x\|_{\mathcal{H}}$ on $\Omega$, whose existence is (ii). Likewise, the paper sets $C = \max_{x \in \Omega} \|k(\cdot, x)\|_{H_0}$, whereas the $C$ of the standing assumptions bounds $\|\Phi(y)\|_{H_0}$ for every $y \in \mathbb{R}^d$.

{{SVGD.xi_regularity_uniformContinuousOn | Lemma A.6 (i)}}

```informal SVGD.xi_regularity_uniformContinuousOn | Regularity of $\xi$
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Then, $x \mapsto \xi_x$ is uniformly continuous from $\Omega$ to $\mathcal{H}$, i.e.
$$\forall \varepsilon > 0, \exists \delta > 0, \forall x, y \in \Omega, \ \|x - y\|_2 < \delta \implies \|\xi_x - \xi_y\|_{\mathcal{H}} < \varepsilon.$$
```

```proof SVGD.xi_regularity_uniformContinuousOn
As $\Omega$ is compact, the Heine–Cantor theorem reduces the claim to the continuity of $x \mapsto \xi_x$ on $\Omega$. The identity map from $H_0^d$, with the product topology, to $\mathcal{H}$ is continuous. Thus, it is sufficient to show that, for every $1 \le i \le d$, the component
$$x \mapsto (\xi_x)_i = s(x)(e_i)\, \Phi(x) + D\Phi(x)(e_i)$$
is continuous on $\Omega$. By the standing assumptions, the score $s$ is continuous on $\Omega$, and so is $x \mapsto s(x)(e_i)$. As the feature map $\Phi$ is $C^1$, the maps $\Phi$ and $x \mapsto D\Phi(x)$ are continuous, and so is $x \mapsto D\Phi(x)(e_i)$. Thus, $x \mapsto (\xi_x)_i$ is continuous on $\Omega$, as a product and a sum of continuous maps, which concludes the proof.
```

{{SVGD.xi_regularity_exists_bound | Lemma A.6 (ii)}}

```informal SVGD.xi_regularity_exists_bound | Regularity of $\xi$
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Then, there exists $B \in \mathbb{R}$ such that
$$\forall x \in \Omega, \ \|\xi_x\|_{\mathcal{H}} \le B.$$
```

```proof SVGD.xi_regularity_exists_bound
By Lemma A.6 (i), $x \mapsto \xi_x$ is continuous on $\Omega$. As $\Omega$ is compact, a function continuous on $\Omega$ is bounded in norm on $\Omega$, which concludes the proof.
```

{{SVGD.xi_regularity_integrable | Lemma A.6 (iii)}}

```informal SVGD.xi_regularity_integrable | Regularity of $\xi$
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Let $\nu$ be a finite measure on $\mathbb{R}^d$ such that $x \in \Omega$ for $\nu$-almost every $x$. Then, $x \mapsto \xi_x$ is $\nu$-integrable, i.e. it is $\nu$-almost everywhere strongly measurable and
$$\int \|\xi_x\|_{\mathcal{H}} \, \mathrm{d}\nu(x) < \infty.$$
```

```proof SVGD.xi_regularity_integrable
By Lemma A.6 (i), $x \mapsto \xi_x$ is continuous on the compact set $\Omega$. A function continuous on a compact set is integrable for every measure carried by this set and finite on compact sets. Indeed, such a measure is equal to its restriction to the set, and a function continuous on a compact set is integrable on it. The finite measure $\nu$ is finite on compact sets and carried by $\Omega$, which concludes the proof.
```

Thus, under the hypotheses of Lemma A.6 (iii) and when $H_0$ is a Hilbert space, $\varphi^*_\nu = \int \xi_x \, \mathrm{d}\nu(x)$ is the Bochner integral of an integrable function, and not the value $0$ given by convention.

{{SVGD.xi_regularity_norm_direction_le | Lemma A.6 (iv)}}

```informal SVGD.xi_regularity_norm_direction_le | Regularity of $\xi$
Let $\Omega \subseteq \mathbb{R}^d$, $\Phi : \mathbb{R}^d \to H_0$ and $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$. Let $B \in \mathbb{R}$ such that $\|\xi_x\|_{\mathcal{H}} \le B$ for every $x \in \Omega$. Let $\nu \in \mathcal{P}(\Omega)$, i.e. $\nu$ is a probability measure on $\mathbb{R}^d$ such that $x \in \Omega$ for $\nu$-almost every $x$. Then,
$$\|\varphi^*_\nu\|_{\mathcal{H}} \le B.$$
```

```proof SVGD.xi_regularity_norm_direction_le
As $x \in \Omega$ for $\nu$-almost every $x$, we have that $\|\xi_x\|_{\mathcal{H}} \le B$ for $\nu$-almost every $x$. For a finite measure, if the norm of the integrand is at most a constant almost everywhere, then the norm of its Bochner integral is at most this constant times the total mass. This bound needs no integrability. Thus,
$$\|\varphi^*_\nu\|_{\mathcal{H}} = \left\| \int \xi_x \, \mathrm{d}\nu(x) \right\|_{\mathcal{H}} \le B \, \nu(\mathbb{R}^d) = B.$$
In particular, the bound holds when $\varphi^*_\nu = 0$ by convention. Indeed, $\nu \neq 0$ and $B \ge \|\xi_x\|_{\mathcal{H}} \ge 0$ for $\nu$-almost every $x$, so that $B \ge 0$. This concludes the proof.
```

{{SVGD.xi_regularity_norm_direction_apply_le | Lemma A.6 (v)}}

```informal SVGD.xi_regularity_norm_direction_apply_le | Regularity of $\xi$
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Let $B \ge 0$ such that $\|\xi_x\|_{\mathcal{H}} \le B$ for every $x \in \Omega$. Let $\nu \in \mathcal{P}(\Omega)$. Then,
$$\forall y \in \mathbb{R}^d, \ \big\|(\varphi^*_\nu)_\Phi(y)\big\|_2 \le B\, C.$$
```

```proof SVGD.xi_regularity_norm_direction_apply_le
Let $y \in \mathbb{R}^d$. By Lemma A.6 (iv), $\|\varphi^*_\nu\|_{\mathcal{H}} \le B$. By the standing assumptions, $\|\Phi(y)\|_{H_0} \le C$. Let $h \in \mathcal{H}$ and $u \in H_0$, and let $P_h(u) = \big(\langle h_i, u \rangle_{H_0}\big)_{1 \le i \le d} \in \mathbb{R}^d$, so that $h_\Phi = P_h \circ \Phi$. By the Cauchy–Schwarz inequality in $H_0$, we have that
$$\|P_h(u)\|_2^2 = \sum_{i=1}^d \langle h_i, u \rangle_{H_0}^2 \le \sum_{i=1}^d \|h_i\|_{H_0}^2 \|u\|_{H_0}^2 = \|h\|_{\mathcal{H}}^2 \|u\|_{H_0}^2.$$
Taking square roots, $\|P_h(u)\|_2 \le \|h\|_{\mathcal{H}} \, \|u\|_{H_0}$. We apply this to $h = \varphi^*_\nu$ and $u = \Phi(y)$. As $B \ge 0$, we have that
$$\big\|(\varphi^*_\nu)_\Phi(y)\big\|_2 = \big\|P_{\varphi^*_\nu}(\Phi(y))\big\|_2 \le \|\varphi^*_\nu\|_{\mathcal{H}} \, \|\Phi(y)\|_{H_0} \le B\, C,$$
which concludes the proof.
```

As a consequence of the reproducing property and of Lemma A.6 (i), the Stein operator of every $f \in \mathcal{H}$ is continuous on $\Omega$.

{{SVGD.continuousOn_steinOperator | Lemma}}

```informal SVGD.continuousOn_steinOperator
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Then, for every $f \in \mathcal{H}$, the function $\mathcal{A}_\pi f$ is continuous on $\Omega$.
```

```proof SVGD.continuousOn_steinOperator
Let $f \in \mathcal{H}$. By the standing assumptions, $\Phi$ is $C^1$, hence differentiable at every $x \in \mathbb{R}^d$. By the [reproducing property](#SVGD.reproducing_property), we have that
$$\forall x \in \Omega, \ \mathcal{A}_\pi f(x) = \langle f, \xi_x \rangle_{\mathcal{H}}.$$
By Lemma A.6 (i), $x \mapsto \xi_x$ is continuous on $\Omega$. As the inner product is continuous, $x \mapsto \langle f, \xi_x \rangle_{\mathcal{H}}$ is continuous on $\Omega$. Thus, $\mathcal{A}_\pi f$ is continuous on $\Omega$, as it coincides with this function on $\Omega$, which concludes the proof.
```

The supremum in the KSD is attained along the update direction $\varphi^*_\mu$. Thus, the discrepancy is the squared norm of this direction. Theorem A.7 is made of four separate results. They all take the standing assumptions, a Hilbert space $H_0$ and a measure $\mu \in \mathcal{P}(\Omega)$.

{{SVGD.steepest_trajectory_integral | Theorem A.7 (i)}}

```informal SVGD.steepest_trajectory_integral
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Let $H_0$ be a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$. Then,
$$\forall f \in \mathcal{H}, \ \int \mathcal{A}_\pi f(x) \, \mathrm{d}\mu(x) = \langle f, \varphi^*_\mu \rangle_{\mathcal{H}}.$$
```

```proof SVGD.steepest_trajectory_integral
Let $f \in \mathcal{H}$. As $\mu$ is finite and carried by $\Omega$, $x \mapsto \xi_x$ is $\mu$-integrable by Lemma A.6 (iii). As $H_0$ is complete, so is $\mathcal{H}$. Thus, the continuous linear form $\langle f, \cdot \rangle_{\mathcal{H}}$ commutes with the Bochner integral, and
$$\langle f, \varphi^*_\mu \rangle_{\mathcal{H}} = \left\langle f, \int \xi_x \, \mathrm{d}\mu(x) \right\rangle_{\mathcal{H}} = \int \langle f, \xi_x \rangle_{\mathcal{H}} \, \mathrm{d}\mu(x).$$
By the standing assumptions, $\Phi$ is $C^1$, hence differentiable at every $x \in \mathbb{R}^d$. By the [reproducing property](#SVGD.reproducing_property), $\mathcal{A}_\pi f(x) = \langle f, \xi_x \rangle_{\mathcal{H}}$ for every $x \in \mathbb{R}^d$. Thus, the two integrands are equal, and
$$\int \mathcal{A}_\pi f(x) \, \mathrm{d}\mu(x) = \int \langle f, \xi_x \rangle_{\mathcal{H}} \, \mathrm{d}\mu(x) = \langle f, \varphi^*_\mu \rangle_{\mathcal{H}},$$
which concludes the proof.
```

{{SVGD.steepest_trajectory_isMaxOn | Theorem A.7 (ii)}}

```informal SVGD.steepest_trajectory_isMaxOn
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Let $H_0$ be a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$. Then,
$$\forall f \in \mathcal{H}, \ \|f\|_{\mathcal{H}} \le 1 \implies \int \mathcal{A}_\pi f(x) \, \mathrm{d}\mu(x) \le \int \mathcal{A}_\pi \big( \|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu \big)(x) \, \mathrm{d}\mu(x),$$
with the convention $0^{-1} = 0$. Thus, $\|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu = 0$ if $\varphi^*_\mu = 0$.
```

```proof SVGD.steepest_trajectory_isMaxOn
By Theorem A.7 (i), applied to $f$ and to $\|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu$, it is sufficient to show that
$$\forall h \in \mathcal{H}, \ \|h\|_{\mathcal{H}} \le 1 \implies \langle h, \varphi^*_\mu \rangle_{\mathcal{H}} \le \big\langle \|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu, \varphi^*_\mu \big\rangle_{\mathcal{H}}.$$
This holds for every vector of a real inner product space in place of $\varphi^*_\mu$. Let $h \in \mathcal{H}$ with $\|h\|_{\mathcal{H}} \le 1$. By the Cauchy–Schwarz inequality,
$$\langle h, \varphi^*_\mu \rangle_{\mathcal{H}} \le \|h\|_{\mathcal{H}} \, \|\varphi^*_\mu\|_{\mathcal{H}} \le \|\varphi^*_\mu\|_{\mathcal{H}}.$$
We also have that $\langle \|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu, \varphi^*_\mu \rangle_{\mathcal{H}} = \|\varphi^*_\mu\|_{\mathcal{H}}$. If $\varphi^*_\mu = 0$, both sides are $0$. Otherwise,
$$\big\langle \|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu, \varphi^*_\mu \big\rangle_{\mathcal{H}} = \|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \|\varphi^*_\mu\|_{\mathcal{H}}^2 = \|\varphi^*_\mu\|_{\mathcal{H}},$$
which concludes the proof.
```

The statement does not say that $\|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu$ lies in the closed unit ball. It does, as its norm is $0$ or $1$. This fact is used in the proof of Theorem A.7 (iii).

{{SVGD.steepest_trajectory_ksd | Theorem A.7 (iii)}}

```informal SVGD.steepest_trajectory_ksd
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Let $H_0$ be a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$. Then,
$$\mathfrak{K}(\mu \mid \pi) = \|\varphi^*_\mu\|_{\mathcal{H}}^2.$$
```

```proof SVGD.steepest_trajectory_ksd
By Theorem A.7 (i), we have that
$$\mathfrak{K}(\mu \mid \pi) = \sup_{f \in \mathcal{H}, \ \|f\|_{\mathcal{H}} \le 1} \langle f, \varphi^*_\mu \rangle_{\mathcal{H}}^2.$$
We show that the real supremum of $\langle h, \varphi^*_\mu \rangle_{\mathcal{H}}^2$ over the closed unit ball is $\|\varphi^*_\mu\|_{\mathcal{H}}^2$. Let $h \in \mathcal{H}$ with $\|h\|_{\mathcal{H}} \le 1$. By the Cauchy–Schwarz inequality, $|\langle h, \varphi^*_\mu \rangle_{\mathcal{H}}| \le \|h\|_{\mathcal{H}} \, \|\varphi^*_\mu\|_{\mathcal{H}} \le \|\varphi^*_\mu\|_{\mathcal{H}}$. Hence,
$$\langle h, \varphi^*_\mu \rangle_{\mathcal{H}}^2 \le \|\varphi^*_\mu\|_{\mathcal{H}}^2.$$
The family is thus bounded above by $\|\varphi^*_\mu\|_{\mathcal{H}}^2$. It is nonempty, as $0$ lies in the closed unit ball. Therefore, its real supremum is its least upper bound, which is at most $\|\varphi^*_\mu\|_{\mathcal{H}}^2$. Conversely, $\|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu$ lies in the closed unit ball, as its norm is $0$ or $1$. As in the proof of Theorem A.7 (ii), $\langle \|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu, \varphi^*_\mu \rangle_{\mathcal{H}} = \|\varphi^*_\mu\|_{\mathcal{H}}$. Thus, the supremum is at least
$$\big\langle \|\varphi^*_\mu\|_{\mathcal{H}}^{-1} \varphi^*_\mu, \varphi^*_\mu \big\rangle_{\mathcal{H}}^2 = \|\varphi^*_\mu\|_{\mathcal{H}}^2,$$
which concludes the proof.
```

{{SVGD.steepest_trajectory_ksd_eq_integral | Theorem A.7 (iv)}}

```informal SVGD.steepest_trajectory_ksd_eq_integral
Let $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$, $C$ satisfy the standing assumptions. Let $H_0$ be a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$. Then,
$$\mathfrak{K}(\mu \mid \pi) = \int \mathcal{A}_\pi \varphi^*_\mu(x) \, \mathrm{d}\mu(x).$$
```

```proof SVGD.steepest_trajectory_ksd_eq_integral
By Theorem A.7 (iii), then Theorem A.7 (i) with $f = \varphi^*_\mu$, we have that
$$\mathfrak{K}(\mu \mid \pi) = \|\varphi^*_\mu\|_{\mathcal{H}}^2 = \langle \varphi^*_\mu, \varphi^*_\mu \rangle_{\mathcal{H}} = \int \mathcal{A}_\pi \varphi^*_\mu(x) \, \mathrm{d}\mu(x),$$
which concludes the proof.
```

## The steepest descent of the Kullback–Leibler divergence

SVGD moves each particle $x$ to $x + \varepsilon f_\Phi(x)$, for a small step $\varepsilon$ and some
$f \in \mathcal{H}$. The first variation of the Kullback–Leibler divergence to $\pi$ measures the
effect of this move. Theorem A.8 shows that it is the linear form
$f \mapsto -\langle f, \varphi^*_\mu \rangle_{\mathcal{H}}$. Thus, $\varphi^*_\mu$ is the direction of
steepest descent in the unit ball of $\mathcal{H}$, and the slope along $\varphi^*_\mu$ is
$-\mathfrak{K}(\mu \mid \pi)$.

{{SVGD.klFirstVariation | Definition}}

```informal SVGD.klFirstVariation | The first variation of the KL divergence
Let $H_0$ be a real inner product space, $\Phi : \mathbb{R}^d \to H_0$, $\pi$ and $\mu$ two measures on
$\mathbb{R}^d$, and $f \in \mathcal{H}$. For $\varepsilon \in \mathbb{R}$, let
$T_\varepsilon(f) = I_d + \varepsilon f_\Phi$, i.e. $T_\varepsilon(f)(x) = x + \varepsilon f_\Phi(x)$.
Let $g_f(\varepsilon) = \mathrm{KL}\big(T_\varepsilon(f)_\#\mu \,\|\, \pi\big)$ if this divergence is
finite, and $g_f(\varepsilon) = 0$ otherwise. The first variation of the Kullback–Leibler divergence
to $\pi$ at $\mu$ along $f$ is
$$\nabla_\varepsilon \mathrm{KL}\big(T_\varepsilon(f)_\#\mu \,\|\, \pi\big)\big|_{\varepsilon = 0} = g_f'(0),$$
where $g_f'(0) = 0$ if $g_f : \mathbb{R} \to \mathbb{R}$ is not differentiable at $0$.

Here $\mathrm{KL}(\nu \,\|\, \pi) \in [0, \infty]$ is the Kullback–Leibler divergence. If
$\nu \ll \pi$ and $\log \frac{d\nu}{d\pi}$ is $\nu$-integrable, it is the positive part of
$\int \log \frac{d\nu}{d\pi} \, d\nu + \pi(\mathbb{R}^d) - \nu(\mathbb{R}^d)$, where an infinite mass
counts as $0$. Otherwise, it is $\infty$. For two probability measures, the masses cancel and the
integral is nonnegative, so that $\mathrm{KL}(\nu \,\|\, \pi) = \int \log \frac{d\nu}{d\pi} \, d\nu$ in
the first case. If $T_\varepsilon(f)$ is not
$\mu$-almost everywhere measurable, $T_\varepsilon(f)_\#\mu$ is by convention an arbitrary Dirac
mass, or $0$ if $\mu = 0$. This does not happen when $\Phi$ is continuous.
```

Under the standing assumptions, let $H_0$ be a Hilbert space and $\mu$ a probability measure with
$\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Then, $g_f$ is differentiable at $0$. Its derivative is minus
the mean of the Stein operator, which Theorem A.7 (i) turns into an inner product.

{{SVGD.kl_steepest_descent_hasDerivAt | Theorem A.8 (i)}}

```informal SVGD.kl_steepest_descent_hasDerivAt
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$, and let
$f \in \mathcal{H}$. For $\varepsilon \in \mathbb{R}$, let
$g_f(\varepsilon) = \mathrm{KL}\big((I_d + \varepsilon f_\Phi)_\#\mu \,\|\, \pi\big)$ if this divergence
is finite, and $g_f(\varepsilon) = 0$ otherwise. Then, $g_f : \mathbb{R} \to \mathbb{R}$ is
differentiable at $0$ and
$$g_f'(0) = -\langle f, \varphi^*_\mu \rangle_{\mathcal{H}}.$$
```

```proof SVGD.kl_steepest_descent_hasDerivAt
We first show that $\mu \in \mathcal{P}(\Omega)$, i.e. that $x \in \Omega$ for $\mu$-almost every $x$.
As $\mathrm{KL}(\mu \,\|\, \pi) < \infty$, we have that $\mu \ll \pi$. As $\pi = p \cdot \lambda|_\Omega$,
$\pi$ is carried by $\Omega$, which is measurable as it is compact. Thus, $\mu$ is carried by $\Omega$.

The proof rests on the following general first variation formula. Let $E$ be a finite-dimensional real
normed space, with its Borel $\sigma$-algebra and an additive Haar measure $\mathrm{vol}$. Let
$\Omega \subseteq E$ be compact. Let $p : E \to \mathbb{R}$ be measurable, continuous on $\Omega$ and
positive on $\Omega$. Let $s : E \to E^*$ be continuous on $\Omega$, such that, for every $x$ in the
interior of $\Omega$, $\log p$ is differentiable at $x$ and $D(\log p)(x) = s(x)$. Let
$\pi = p \cdot \mathrm{vol}|_\Omega$. Let $v : E \to E$ be $C^1$ and
$K_v$-Lipschitz, with $v = 0$ on the frontier $\partial \Omega$ of $\Omega$. Let $\mu$ be a finite
measure on $E$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Then, the map
$\varepsilon \mapsto \mathrm{KL}((I + \varepsilon v)_\#\mu \,\|\, \pi)$, with $\infty$ replaced by $0$,
is differentiable at $0$, with derivative
$$-\int \big( s(x)(v(x)) + \operatorname{div} v(x) \big) \, d\mu(x) = -\int \mathcal{A}_s v \, d\mu.$$

This formula is proved in two steps. As $\mathrm{KL}(\mu \,\|\, \pi) < \infty$, $\mu$ is carried by
$\Omega$, as in the first paragraph. The measure $\pi$
is finite, as $p$ is continuous on the compact set $\Omega$.

The first step is a transport formula. Let $e$ be a measurable bijection of $E$ with a measurable
inverse. A measurable map does not increase the divergence between two finite measures (data
processing inequality). Applied to $e$ and $e^{-1}$, this gives
$\mathrm{KL}(e_\#\mu \,\|\, \pi) = \mathrm{KL}(\mu \,\|\, e^{-1}_\#\pi)$. Assume now that $e$ is differentiable at every point of
$\Omega$, that $e(\Omega) = \Omega$, that $\det De > 0$ on $\Omega$ and that $\log \det De$ is
$\mu$-integrable. By the change of variables formula, $e^{-1}_\#\pi = w \cdot \pi$ with
$w = (p \circ e) \det De / p$. The
weight $w$ is positive on $\Omega$, hence $\pi$-almost everywhere, as $\pi$ is carried by $\Omega$. As $\mu$ is carried by $\Omega$, we
have that $\log w(x) = \log p(e(x)) - \log p(x) + \log \det De(x)$ for $\mu$-almost every $x$. Thus,
$\log w$ is $\mu$-integrable. Indeed, $\log p \circ e$ and $\log p$ are continuous on the compact set $\Omega$, which
carries the finite measure $\mu$, and $\log \det De$ is $\mu$-integrable. Reweighting the reference
measure by $w$ subtracts $\int \log w \, d\mu$ from the divergence and adds
$(w \cdot \pi)(E) - \pi(E)$. This
difference is $0$, as $w \cdot \pi = e^{-1}_\#\pi$ has the mass of $\pi$. Thus, as real numbers,
$$\mathrm{KL}(e_\#\mu \,\|\, \pi) = \mathrm{KL}(\mu \,\|\, \pi) - \int \big( \log p(e(x)) - \log p(x) + \log \det De(x) \big) \, d\mu(x).$$
If $|\varepsilon| K_v < 1$, then $I + \varepsilon v$ is a homeomorphism of $E$, as a Lipschitz-small
perturbation of the identity. Thus, it is a measurable
bijection with a measurable inverse. It maps $\Omega$ onto $\Omega$, as $v = 0$ on $\partial \Omega$. It is differentiable, as $v$ is $C^1$.
Thus, the transport formula applies to $e = I + \varepsilon v$ as soon as
$\det D(I + \varepsilon v) > 0$ on $\Omega$. The
function $\log \det De$ is then continuous on the compact set $\Omega$, which carries the finite
measure $\mu$, so it is $\mu$-integrable.

The second step differentiates under the integral sign. As $Dv$ is continuous, $Dv(\Omega)$ is
compact. As moreover $(\varepsilon, A) \mapsto \det(I + \varepsilon A)$ is continuous and $\det(I) = 1$, there is
$\varepsilon_0 > 0$ such that, for $|\varepsilon| < \varepsilon_0$, we have $|\varepsilon| K_v < 1$,
$|\varepsilon| \le 1$ and $\det(I + \varepsilon A) \ge 1/2$ for every $A \in Dv(\Omega)$. For such
$\varepsilon$, $D(I + \varepsilon v)(x) = I + \varepsilon Dv(x)$, so that
$\det D(I + \varepsilon v) \ge 1/2 > 0$ on $\Omega$. Thus, the transport formula gives, as real
numbers,
$$\mathrm{KL}((I + \varepsilon v)_\#\mu \,\|\, \pi) = \mathrm{KL}(\mu \,\|\, \pi) - \int G(\varepsilon, x) \, d\mu(x),$$
where $G(\varepsilon, x) = \log p(x + \varepsilon v(x)) - \log p(x) + \log \det(I + \varepsilon Dv(x))$.
Let $x \in \Omega$, which holds for $\mu$-almost every $x$. Then, $x + \varepsilon v(x) \in \Omega$, as
$v = 0$ on $\partial \Omega$. If $x$ is in
the interior of $\Omega$, so is $x + \varepsilon v(x)$, by the same argument, as $v$ vanishes on the
frontier of the interior, which is contained in $\partial \Omega$. Then, the chain rule gives
$\partial_\varepsilon \log p(x + \varepsilon v(x)) = s(x + \varepsilon v(x))(v(x))$. Otherwise,
$x \in \partial \Omega$, so $v(x) = 0$ and both sides vanish. As
$\det(I + \varepsilon Dv(x)) \ge 1/2 > 0$, we obtain
$$\partial_\varepsilon G(\varepsilon, x) = s(x + \varepsilon v(x))(v(x)) + \frac{D\det(I + \varepsilon Dv(x))(Dv(x))}{\det(I + \varepsilon Dv(x))}.$$
As $x + \varepsilon v(x) \in \Omega$, $|\varepsilon| \le 1$ and $\det(I + \varepsilon Dv(x)) \ge 1/2$, this
derivative is bounded by $S V + 2M$. Here $S$ and $V$ bound $\|s\|$ and $\|v\|$ on $\Omega$, and $M$
bounds $|D\det(I + \tau A)(A)|$ for $(\tau, A) \in [-1, 1] \times Dv(\Omega)$. These bounds exist by
continuity on compact sets. The constant $S V + 2M$ is $\mu$-integrable, as $\mu$ is finite.
Moreover, $G(0, \cdot) = 0$ is integrable. By differentiation under the integral sign with a
dominated derivative, the derivative at $0$ is
$-\int \partial_\varepsilon G(0, x) \, d\mu(x)$. Finally, Jacobi's formula at the identity,
$D\det(I)(A) = \operatorname{tr} A$, gives
$$\partial_\varepsilon G(0, x) = s(x)(v(x)) + \operatorname{tr} Dv(x) = s(x)(v(x)) + \operatorname{div} v(x).$$

We apply this formula with $E = \mathbb{R}^d$, $\mathrm{vol} = \lambda$ and $v = f_\Phi$. The hypotheses on
$\Omega$, $p$ and $s$ are the standing assumptions, and $\mu$ is a probability measure. The vector
field $f_\Phi$ is $\|f\|_{\mathcal{H}} K$-Lipschitz, as $\Phi$ is $K$-Lipschitz. It is $C^1$, as $f_\Phi = P_f \circ \Phi$ with $P_f$ continuous
linear and $\Phi$ of class $C^1$. It vanishes on $\partial \Omega$, as $\Phi$ does. Thus, $g_f$ is differentiable at $0$ and
$$g_f'(0) = -\int \big( s(x)(f_\Phi(x)) + \operatorname{div} f_\Phi(x) \big) \, d\mu(x) = -\mathbb{E}_{x \sim \mu}[\mathcal{A}_\pi f(x)].$$
As $\mu \in \mathcal{P}(\Omega)$ and $H_0$ is a Hilbert space, [Theorem A.7 (i)](#SVGD.steepest_trajectory_integral) gives
$\mathbb{E}_{x \sim \mu}[\mathcal{A}_\pi f(x)] = \langle f, \varphi^*_\mu \rangle_{\mathcal{H}}$, which
concludes the proof.
```

Thus, the first variation of the Definition is a linear form in $f$.

{{SVGD.kl_steepest_descent_eq_inner | Theorem A.8 (ii)}}

```informal SVGD.kl_steepest_descent_eq_inner
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$, and let
$f \in \mathcal{H}$. Then,
$$\nabla_\varepsilon \mathrm{KL}\big(T_\varepsilon(f)_\#\mu \,\|\, \pi\big)\big|_{\varepsilon = 0} = -\langle f, \varphi^*_\mu \rangle_{\mathcal{H}},$$
where $T_\varepsilon(f) = I_d + \varepsilon f_\Phi$.
```

```proof SVGD.kl_steepest_descent_eq_inner
By Theorem A.8 (i), $g_f$ is differentiable at $0$ with
$g_f'(0) = -\langle f, \varphi^*_\mu \rangle_{\mathcal{H}}$. The first variation is $g_f'(0)$ by
definition, and the convention for non-differentiable maps does not apply, which concludes the
proof.
```

On the unit ball of $\mathcal{H}$, this linear form is minimized at
$\varphi^*_\mu / \|\varphi^*_\mu\|_{\mathcal{H}}$. The minimizer is unique when $\varphi^*_\mu \neq 0$.
Together, (iii) and (iv) give the $\arg\min$ of [Serre2025] when $\varphi^*_\mu \neq 0$.

{{SVGD.kl_steepest_descent_isMinOn | Theorem A.8 (iii)}}

```informal SVGD.kl_steepest_descent_isMinOn
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let
$u = \varphi^*_\mu / \|\varphi^*_\mu\|_{\mathcal{H}}$, with the convention $u = 0$ if
$\varphi^*_\mu = 0$. Then, for every $f \in \mathcal{H}$ with $\|f\|_{\mathcal{H}} \le 1$,
$$\nabla_\varepsilon \mathrm{KL}\big(T_\varepsilon(u)_\#\mu \,\|\, \pi\big)\big|_{\varepsilon = 0} \le \nabla_\varepsilon \mathrm{KL}\big(T_\varepsilon(f)_\#\mu \,\|\, \pi\big)\big|_{\varepsilon = 0},$$
where $T_\varepsilon(h) = I_d + \varepsilon h_\Phi$ for $h \in \mathcal{H}$.
```

```proof SVGD.kl_steepest_descent_isMinOn
Let $f \in \mathcal{H}$ with $\|f\|_{\mathcal{H}} \le 1$. By Theorem A.8 (ii), applied to $u$ and to
$f$, the claim reads
$$-\langle u, \varphi^*_\mu \rangle_{\mathcal{H}} \le -\langle f, \varphi^*_\mu \rangle_{\mathcal{H}}.$$
We have that $\langle u, \varphi^*_\mu \rangle_{\mathcal{H}} = \|\varphi^*_\mu\|_{\mathcal{H}}$. Indeed, if $\varphi^*_\mu \neq 0$, then
$\langle u, \varphi^*_\mu \rangle_{\mathcal{H}} = \|\varphi^*_\mu\|_{\mathcal{H}}^2 / \|\varphi^*_\mu\|_{\mathcal{H}}$.
If $\varphi^*_\mu = 0$, both sides vanish. Thus, it is sufficient to show that
$\langle f, \varphi^*_\mu \rangle_{\mathcal{H}} \le \|\varphi^*_\mu\|_{\mathcal{H}}$. By the
Cauchy–Schwarz inequality and $\|f\|_{\mathcal{H}} \le 1$,
$$\langle f, \varphi^*_\mu \rangle_{\mathcal{H}} \le \|f\|_{\mathcal{H}} \, \|\varphi^*_\mu\|_{\mathcal{H}} \le \|\varphi^*_\mu\|_{\mathcal{H}},$$
which concludes the proof.
```

{{SVGD.kl_steepest_descent_eq | Theorem A.8 (iv)}}

```informal SVGD.kl_steepest_descent_eq
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$ and
$\varphi^*_\mu \neq 0$. Let $u = \varphi^*_\mu / \|\varphi^*_\mu\|_{\mathcal{H}}$. Let
$f \in \mathcal{H}$ with $\|f\|_{\mathcal{H}} \le 1$ and
$$\nabla_\varepsilon \mathrm{KL}\big(T_\varepsilon(f)_\#\mu \,\|\, \pi\big)\big|_{\varepsilon = 0} = \nabla_\varepsilon \mathrm{KL}\big(T_\varepsilon(u)_\#\mu \,\|\, \pi\big)\big|_{\varepsilon = 0},$$
where $T_\varepsilon(h) = I_d + \varepsilon h_\Phi$ for $h \in \mathcal{H}$. Then, $f = u$.
```

```proof SVGD.kl_steepest_descent_eq
By Theorem A.8 (ii), and as $\langle u, \varphi^*_\mu \rangle_{\mathcal{H}} = \|\varphi^*_\mu\|_{\mathcal{H}}$
(see the proof of [Theorem A.8 (iii)](#SVGD.kl_steepest_descent_isMinOn)), the hypothesis reads
$-\langle f, \varphi^*_\mu \rangle_{\mathcal{H}} = -\|\varphi^*_\mu\|_{\mathcal{H}}$. Thus,
$\langle f, \varphi^*_\mu \rangle_{\mathcal{H}} = \|\varphi^*_\mu\|_{\mathcal{H}}$.

We conclude by the equality case of the Cauchy–Schwarz inequality on the unit ball. As $\varphi^*_\mu \neq 0$, we have that
$\|u\|_{\mathcal{H}} = 1$. Thus, $\|f\|_{\mathcal{H}} \le \|u\|_{\mathcal{H}}$ and
$$\langle f, u \rangle_{\mathcal{H}} = \frac{\langle f, \varphi^*_\mu \rangle_{\mathcal{H}}}{\|\varphi^*_\mu\|_{\mathcal{H}}} = 1 = \|u\|_{\mathcal{H}}^2.$$
Then,
$$\|f - u\|_{\mathcal{H}}^2 = \|f\|_{\mathcal{H}}^2 - 2 \langle f, u \rangle_{\mathcal{H}} + \|u\|_{\mathcal{H}}^2 = \|f\|_{\mathcal{H}}^2 - \|u\|_{\mathcal{H}}^2 \le 0.$$
Thus, $f = u$, which concludes the proof.
```

Along $\varphi^*_\mu$ itself, the slope is the opposite of the kernelized Stein discrepancy. This is
the identity that SVGD uses.

{{SVGD.kl_steepest_descent_direction | Theorem A.8 (v)}}

```informal SVGD.kl_steepest_descent_direction
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Then,
$$\nabla_\varepsilon \mathrm{KL}\big((I_d + \varepsilon (\varphi^*_\mu)_\Phi)_\#\mu \,\|\, \pi\big)\big|_{\varepsilon = 0} = -\mathfrak{K}(\mu \mid \pi).$$
```

```proof SVGD.kl_steepest_descent_direction
By Theorem A.8 (ii) with $f = \varphi^*_\mu$, then [Theorem A.7 (iii)](#SVGD.steepest_trajectory_ksd),
$$\nabla_\varepsilon \mathrm{KL}\big((I_d + \varepsilon (\varphi^*_\mu)_\Phi)_\#\mu \,\|\, \pi\big)\big|_{\varepsilon = 0} = -\langle \varphi^*_\mu, \varphi^*_\mu \rangle_{\mathcal{H}} = -\|\varphi^*_\mu\|_{\mathcal{H}}^2 = -\mathfrak{K}(\mu \mid \pi).$$
Theorem A.7 (iii) applies, as $H_0$ is a Hilbert space and $\mu \in \mathcal{P}(\Omega)$ (see the proof
of Theorem A.8 (i)). This concludes the proof.
```

## The mean-field SVGD flow

The flow $(T_t)_{t \ge 0}$ of Theorems A.11 and 3.1 is driven by the update directions of its own push-forwards. It satisfies
$$\frac{d}{dt} T_t(x) = (\varphi^*_{\mu_t})_\Phi\big(T_t(x)\big), \qquad \mu_t = (T_t)_\#\mu.$$
[Serre2025] assumes that such a flow exists. The formalization constructs it for every $\mu \in \mathcal{P}(\Omega)$, under the standing assumptions with $H_0$ a Hilbert space, and with no Lipschitz condition on the score $s$.

We describe the flow by the curve $m : \mathbb{R} \to \mathcal{H}$ of its update directions. Recall that the trajectories of $m$ are the global solutions $X^m_{t_0, x} = \operatorname{sol}_v(t_0, x)$ of $\alpha' = v(t, \alpha)$, where $v(t, y) = m(t)_\Phi(y)$. Recall also that $\operatorname{sol}_v(t_0, x)$ is a solution with $\alpha(t_0) = x$, chosen with the axiom of choice, or the constant curve $x$ if there is none. We write $X^m_{t_0, \cdot}(t)$ for the map $x \mapsto X^m_{t_0, x}(t)$. The flow of $m$ is $T_t = X^m_{0, \cdot}(t)$, and the mean-field equation reads $m(t) = \varphi^*_{\mu_t}$ for $t \ge 0$.

{{SVGD.IsMeanFieldCurve | Definition}}

```informal SVGD.IsMeanFieldCurve
Let $H_0$ be a real inner product space, $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $\mu$ a measure on $\mathbb{R}^d$. A curve $m : \mathbb{R} \to \mathcal{H}$ solves the mean-field SVGD equation from $\mu$ if
$$\forall t \ge 0, \quad m(t) = \varphi^*_{(T_t)_\#\mu}, \qquad T_t : x \mapsto X^m_{0, x}(t).$$
Here, $T_t$ is the flow of the vector field of $m$, and $(T_t)_\#\mu$ is the push-forward of $\mu$ by $T_t$. By convention, if $T_t$ is not $\mu$-almost everywhere measurable, $(T_t)_\#\mu$ is $0$ when $\mu = 0$ and an arbitrary Dirac mass otherwise. The update direction $\varphi^*_\nu = \int \xi_x \, d\nu(x)$ is a Bochner integral, equal to $0$ if $\xi$ is not $\nu$-integrable or if $\mathcal{H}$ is not complete. The definition requires no regularity of $m$.
```

The right-hand side of the equation depends on $m$ through its flow. Thus, the equation is a fixed point equation on the curve $m$. Under the standing assumptions, with $H_0$ a Hilbert space and $\mu \in \mathcal{P}(\Omega)$, it has a continuous bounded solution (see the [existence theorem](#SVGD.exists_meanField) below). The uniqueness of this solution is not claimed. The mean-field SVGD curve picks one of them.

{{SVGD.meanFieldCurve | Definition}}

```informal SVGD.meanFieldCurve
Let $H_0$ be a real inner product space, $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $\mu$ a measure on $\mathbb{R}^d$. The mean-field SVGD curve $m : \mathbb{R} \to \mathcal{H}$ from $\mu$ is defined as follows. Consider the curves $\tilde m : \mathbb{R} \to \mathcal{H}$ that are continuous, bounded, i.e.
$$\exists B \ge 0, \ \forall t \in \mathbb{R}, \quad \|\tilde m(t)\|_{\mathcal{H}} \le B,$$
and that solve the mean-field SVGD equation from $\mu$. If such a curve exists, then $m$ is one of them, chosen with the axiom of choice. Otherwise, $m$ is the zero curve $t \mapsto 0$.
```

{{SVGD.meanFieldFlow | Definition}}

```informal SVGD.meanFieldFlow
Let $H_0$ be a real inner product space, $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $\mu$ a measure on $\mathbb{R}^d$. Let $m$ be the mean-field SVGD curve from $\mu$. The mean-field SVGD flow from $\mu$ is the flow of the vector field of $m$, from time $0$,
$$T_t(x) = X^m_{0, x}(t), \qquad t \in \mathbb{R}, \ x \in \mathbb{R}^d.$$
We write $\mu_t = (T_t)_\#\mu$.
```

The curve $m$ is continuous and bounded in all cases, including when it takes its default value $0$. Thus, under the standing assumptions, its flow starts at the identity and its maps are homeomorphisms of $\Omega$. These facts do not require $\mu \in \mathcal{P}(\Omega)$.

{{SVGD.continuous_meanFieldCurve | Lemma}}

```informal SVGD.continuous_meanFieldCurve | Continuity of the mean-field SVGD curve
Let $H_0$ be a real inner product space, $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $\mu$ a measure on $\mathbb{R}^d$. Then the mean-field SVGD curve $m$ from $\mu$ is continuous.
```

```proof SVGD.continuous_meanFieldCurve
If a continuous bounded solution of the mean-field SVGD equation from $\mu$ exists, then $m$ is one of them, hence continuous. Otherwise, $m = 0$, which is continuous.
```

{{SVGD.exists_norm_meanFieldCurve_le | Lemma}}

```informal SVGD.exists_norm_meanFieldCurve_le | Boundedness of the mean-field SVGD curve
Let $H_0$ be a real inner product space, $\Phi : \mathbb{R}^d \to H_0$, $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$ and $\mu$ a measure on $\mathbb{R}^d$. Then the mean-field SVGD curve $m$ from $\mu$ is bounded, i.e.
$$\exists B \ge 0, \ \forall t \in \mathbb{R}, \quad \|m(t)\|_{\mathcal{H}} \le B.$$
```

```proof SVGD.exists_norm_meanFieldCurve_le
If a continuous bounded solution of the mean-field SVGD equation from $\mu$ exists, then $m$ is one of them, hence bounded. Otherwise, $m = 0$, and $B = 0$ works.
```

{{SVGD.meanFieldFlow_zero | Lemma}}

```informal SVGD.meanFieldFlow_zero
Assume the standing assumptions for $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$ and $C$. Let $\mu$ be a measure on $\mathbb{R}^d$ and $T_t$ the mean-field SVGD flow from $\mu$. Then
$$\forall x \in \mathbb{R}^d, \quad T_0(x) = x.$$
```

```proof SVGD.meanFieldFlow_zero
Let $m$ be the mean-field SVGD curve from $\mu$. By the two previous lemmas, $m$ is continuous and bounded by some $B \ge 0$. Let $v(t, y) = m(t)_\Phi(y)$ be its vector field. For every $y$, $t \mapsto v(t, y) = P_{m(t)}(\Phi(y))$ is continuous, as $m$ is continuous and the [pairing](#SVGD.pairing) $h \mapsto P_h$ is $1$-Lipschitz for the operator norm. As $\Phi$ is $K$-Lipschitz, the Cauchy–Schwarz inequality gives, for all $t$, $y$ and $y'$,
$$\|v(t, y) - v(t, y')\| \le \|m(t)\|_{\mathcal{H}} \, \|\Phi(y) - \Phi(y')\|_{H_0} \le BK \, \|y - y'\|.$$
Thus, $v$ is continuous in time and $BK$-Lipschitz in space, uniformly in time. By the global Cauchy–Lipschitz theorem, $\alpha' = v(t, \alpha)$ has a solution on $\mathbb{R}$ with $\alpha(0) = x$. Hence, by [definition](#SVGD.trajectory), $X^m_{0, x} = \operatorname{sol}_v(0, x)$ is such a solution, and $T_0(x) = X^m_{0, x}(0) = x$.
```

{{SVGD.exists_homeomorph_meanFieldFlow | Lemma}}

```informal SVGD.exists_homeomorph_meanFieldFlow | The mean-field SVGD flow maps are homeomorphisms of $\Omega$
Assume the standing assumptions for $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$ and $C$. Let $\mu$ be a measure on $\mathbb{R}^d$, $T_t$ the mean-field SVGD flow from $\mu$ and $t \in \mathbb{R}$. Then there exists a homeomorphism $e : \Omega \to \Omega$ such that
$$\forall x \in \Omega, \quad e(x) = T_t(x).$$
That is, $T_t$ restricts to a homeomorphism of $\Omega$.
```

```proof SVGD.exists_homeomorph_meanFieldFlow
Let $m$ be the mean-field SVGD curve from $\mu$. By the lemmas above, $m$ is continuous and bounded by some $B \ge 0$. Thus, its vector field $v(\tau, y) = m(\tau)_\Phi(y)$ is continuous in time and $BK$-Lipschitz in space (see the proof of the [previous lemma](#SVGD.meanFieldFlow_zero)). We use two properties of its trajectories.

First, $T_t = X^m_{0, \cdot}(t)$ is a homeomorphism of $\mathbb{R}^d$, with inverse $y \mapsto X^m_{t, y}(0)$. By uniqueness of the solutions, the trajectory through $T_t(x)$ at time $t$ is $X^m_{0, x}$, and the trajectory through $X^m_{t, y}(0)$ at time $0$ is $X^m_{t, y}$. Thus, $X^m_{t, T_t(x)}(0) = x$ and $T_t(X^m_{t, y}(0)) = y$. Both maps are continuous, since Grönwall's inequality gives, for all times $t_0, t_1$ and all $x, y$,
$$\|X^m_{t_0, x}(t_1) - X^m_{t_0, y}(t_1)\| \le e^{BK |t_1 - t_0|} \, \|x - y\|.$$

Second, a trajectory that meets $\Omega$ stays in $\Omega$ at all times. As $\Phi$ vanishes on the frontier of $\Omega$, every point of the frontier is a zero of every field $v(\tau, \cdot)$. Let $\alpha$ be a trajectory with $\alpha(t_0) \in \Omega$ and $\alpha(t_1) \notin \Omega$. The connected set $\alpha([t_0, t_1])$, or $\alpha([t_1, t_0])$, meets $\Omega$ and its complement, hence the frontier of $\Omega$. Thus, $\alpha$ passes through a common zero of the fields, and it is constant by uniqueness of the solutions. Then $\alpha(t_0) = \alpha(t_1)$, which is a contradiction.

Apply the second property to $X^m_{0, x}$, which takes the value $x$ at time $0$ and $T_t(x)$ at time $t$, and to $X^m_{t, T_t(x)}$, which takes the same values. We have that $x \in \Omega \iff T_t(x) \in \Omega$. Hence, the homeomorphism $T_t$ of $\mathbb{R}^d$ restricts to a homeomorphism $e$ of $\Omega$, which concludes the proof.
```

We now prove that the mean-field SVGD equation has a solution. On a compact time interval $[a, b]$, a solution from $\nu \in \mathcal{P}(\Omega)$ at time $a$ is a fixed point of the map $G : g \mapsto \big(t \mapsto \varphi^*_{(X^g_{a, \cdot}(t))_\#\nu}\big)$. On the curves with values in the compact closed convex hull of $\xi(\Omega)$, the map $G$ is continuous, and its images are equicontinuous and lie in this hull. The value of $G g$ at time $t$ only depends on $g$ before $t$. Thus, $G$ has a fixed point by Tonelli's argument. The solutions on the intervals $[n, n + 1]$ are then concatenated.

{{SVGD.exists_meanField | Theorem}}

```informal SVGD.exists_meanField | Existence of a solution of the mean-field SVGD equation on $[0, \infty)$
Assume the standing assumptions for $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$ and $C$, and let $H_0$ be a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$, i.e. $\mu$ is a probability measure on $\mathbb{R}^d$ with $x \in \Omega$ for $\mu$-almost every $x$. Let $\mathcal{K}$ be the closed convex hull of $\xi(\Omega) = \{\xi_x \mid x \in \Omega\}$ in $\mathcal{H}$. Then there exists a continuous curve $m : \mathbb{R} \to \mathcal{H}$, with $m(t) \in \mathcal{K}$ for every $t \in \mathbb{R}$, that solves the mean-field SVGD equation from $\mu$, i.e.
$$\forall t \ge 0, \quad m(t) = \varphi^*_{(T_t)_\#\mu}, \qquad T_t : x \mapsto X^m_{0, x}(t).$$
```

```proof SVGD.exists_meanField
The proof has four steps. First, we study the set $\mathcal{K}$. Next, we recall a fixed point theorem for causal maps. Then, we solve the equation on a compact time interval. Finally, we concatenate the solutions on the intervals $[n, n + 1]$.

**Step 1.** The set $\mathcal{K}$.

**Claim 1.** $\mathcal{K}$ is compact. By [Lemma A.6 (i)](#SVGD.xi_regularity_uniformContinuousOn), $x \mapsto \xi_x$ is uniformly continuous, hence continuous, on the compact set $\Omega$. Thus, $\xi(\Omega)$ is compact. As $H_0$ is a Hilbert space, so is $\mathcal{H} = H_0^d$. In a real Banach space, the closed convex hull of a compact set is compact. It is the closure of the convex hull, which is totally bounded as the convex hull of a totally bounded set. It is also complete, as a closed subset of a complete space.

**Claim 2.** For every $\nu \in \mathcal{P}(\Omega)$, $\varphi^*_\nu \in \mathcal{K}$. We have that $\varphi^*_\nu = \int \xi_x \, d\nu(x)$, where $\xi$ is $\nu$-integrable by [Lemma A.6 (iii)](#SVGD.xi_regularity_integrable). Also, $\xi_x \in \xi(\Omega) \subseteq \mathcal{K}$ for $\nu$-almost every $x$. As $\mathcal{K}$ is closed and convex and $\nu$ is a probability measure, the mean $\varphi^*_\nu$ lies in $\mathcal{K}$.

**Claim 3.** There is $B \ge 0$ such that $\|h\|_{\mathcal{H}} \le B$ for every $h \in \mathcal{K}$. By Claim 1, $\mathcal{K}$ is compact, hence bounded.

In the rest of the proof, $B$ is given by Claim 3.

**Step 2.** Fixed points of causal maps. We use the following theorem. It is Tonelli's proof of the Peano existence theorem, and it uses no other fixed point theorem. Let $Y$ be a metric space, $a \le b$ and $\mathcal{K}' \subseteq Y$ a nonempty compact set. Let $\mathcal{C}$ be the space of bounded continuous curves $g : [a, b] \to Y$, with the uniform distance $d_\infty$. Let $S = \{g \in \mathcal{C} \mid \forall t \in [a, b], \ g(t) \in \mathcal{K}'\}$ and $G : \mathcal{C} \to \mathcal{C}$. Assume that

(i) $G(S) \subseteq S$,

(ii) $G$ is continuous on $S$,

(iii) the family of curves $(G g)_{g \in S}$ is equicontinuous,

(iv) $G$ is causal, i.e. for all $g, g' \in S$ and $\tau \in [a, b]$, if $g(t) = g'(t)$ for every $t \in [a, \tau]$, then $G g(\tau) = G g'(\tau)$,

(v) $G g(a) = G g'(a)$ for all $g, g' \in S$.

Then $G$ has a fixed point $g \in S$.

Its proof goes as follows. As $[a, b]$ is compact, the family $(G g)_{g \in S}$ is uniformly equicontinuous. By the Arzelà–Ascoli theorem, the closure of $G(S)$ is compact. The set $S$ is closed, as $\mathcal{K}'$ is. Let $\operatorname{pr}(t) = \max(a, \min(t, b))$ be the projection of $t \in \mathbb{R}$ on $[a, b]$. For $h > 0$, let $D_h g = G g \circ \operatorname{pr}(\cdot - h)$ follow $G g$ with delay $h$. Then $D_h(S) \subseteq S$. By induction on $k \in \mathbb{N}$, for all $g, g' \in S$,
$$\forall t \in [a, b], \quad t < a + kh \implies D_h^k g(t) = D_h^k g'(t).$$
For the induction step, $D_h^{k+1} g(t) = G(D_h^k g)(\operatorname{pr}(t - h))$. If $t - h \le a$, then $\operatorname{pr}(t - h) = a$, and (v) applies. Otherwise, every $t' \le \operatorname{pr}(t - h)$ satisfies $t' \le t - h < a + kh$, and (iv) applies. Let $c \in \mathcal{K}'$, $g_0 \in S$ the constant curve equal to $c$, $N \in \mathbb{N}$ with $N > (b - a)/h$, and $u = D_h^N g_0$. As $b < a + Nh$, the induction with $D_h g_0$ and $g_0$ gives
$$D_h u = D_h^N (D_h g_0) = D_h^N g_0 = u.$$
Thus, for every $n \in \mathbb{N}$, there is $u_n \in S$ with $u_n = G u_n \circ \operatorname{pr}\big(\cdot - \frac{1}{n+1}\big)$. As $\operatorname{pr}$ is $1$-Lipschitz and $\operatorname{pr}(t) = t$ on $[a, b]$, we have that $|t - \operatorname{pr}(t - \frac{1}{n+1})| \le \frac{1}{n+1}$. By uniform equicontinuity, $d_\infty(G u_n, u_n) \to 0$. By compactness, a subsequence $G u_{\sigma(n)}$ converges to some $g$, and $g \in S$ as $S$ is closed and contains $G(S)$. Then $u_{\sigma(n)} \to g$, and $G u_{\sigma(n)} \to G g$ by (ii). Hence, $G g = g$ by uniqueness of the limit.

**Step 3.** A solution on a compact time interval.

**Claim 4.** Let $\nu \in \mathcal{P}(\Omega)$ and $a \le b$. There is a continuous curve $m : \mathbb{R} \to \mathcal{H}$, with $m(t) \in \mathcal{K}$ for every $t \in \mathbb{R}$, such that
$$\forall t \in [a, b], \quad m(t) = \varphi^*_{(X^m_{a, \cdot}(t))_\#\nu}.$$

As $\nu$ is a probability measure carried by $\Omega$, $\Omega$ is nonempty. Let $S$ be the set of bounded continuous curves $g : [a, b] \to \mathcal{H}$ with values in $\mathcal{K}$. For $g \in S$, let $\bar g = g \circ \operatorname{pr} : \mathbb{R} \to \mathcal{H}$ be its extension by constants, where $\operatorname{pr}$ is the projection on $[a, b]$. Then $\bar g$ is continuous, and bounded by $B$ by Claim 3. As in the proof that [the flow starts at the identity](#SVGD.meanFieldFlow_zero), its vector field is continuous in time and $BK$-Lipschitz in space. Thus, for every $t \in \mathbb{R}$, the map $X^{\bar g}_{a, \cdot}(t)$ is continuous. It maps $\Omega$ to $\Omega$, as $\Phi$ vanishes on the frontier of $\Omega$ (see the proof that [the flow maps are homeomorphisms of $\Omega$](#SVGD.exists_homeomorph_meanFieldFlow)).

For $g \in S$ and $t \in [a, b]$, let
$$F g(t) = \varphi^*_{(X^{\bar g}_{a, \cdot}(t))_\#\nu}.$$
The measure $(X^{\bar g}_{a, \cdot}(t))_\#\nu$ is a probability measure carried by $\Omega$. Thus, $F g(t) \in \mathcal{K}$ by Claim 2.

*Integrals against image measures.* We use the following estimate, which holds as $\Omega$ is compact and $\nu \in \mathcal{P}(\Omega)$. Let $f : \mathbb{R}^d \to \mathcal{H}$ be continuous on $\Omega$, and let $\psi_1, \psi_2 : \mathbb{R}^d \to \mathbb{R}^d$ be continuous maps with $\psi_1(\Omega) \subseteq \Omega$ and $\psi_2(\Omega) \subseteq \Omega$. Let $\varepsilon, \eta \in \mathbb{R}$ such that $\|f(x) - f(y)\| \le \varepsilon$ for all $x, y \in \Omega$ with $\|x - y\| < \eta$. Assume that $\|\psi_1(x) - \psi_2(x)\| < \eta$ for every $x \in \Omega$. Then
$$\Big\| \int f \, d(\psi_1)_\#\nu - \int f \, d(\psi_2)_\#\nu \Big\|_{\mathcal{H}} \le \varepsilon.$$
As $f$ is continuous on the compact set $\Omega$, and $\psi_i(x) \in \Omega$ for $\nu$-almost every $x$, the maps $f \circ \psi_1$ and $f \circ \psi_2$ are $\nu$-integrable. Thus, by the change of variables formula, the left-hand side is $\big\| \int \big(f(\psi_1(x)) - f(\psi_2(x))\big) \, d\nu(x) \big\|$. Its integrand has norm at most $\varepsilon$ for $\nu$-almost every $x$, and $\nu$ is a probability measure. We call this estimate (E).

*Equicontinuity.* Let $\varepsilon > 0$. There is $\delta > 0$ such that
$$\forall g \in S, \ \forall t, t' \in [a, b], \quad |t - t'| < \delta \implies \|F g(t) - F g(t')\|_{\mathcal{H}} < \varepsilon.$$
Recall that the curves $\bar g$ are continuous and bounded by $B$. By Lemma A.6 (i), there is $\eta > 0$ such that $\|\xi_x - \xi_y\| < \varepsilon / 2$ for all $x, y \in \Omega$ with $\|x - y\| < \eta$. Let $\delta = \eta / (BC + 1)$. The speed of the trajectories is $\|\bar g(\tau)_\Phi(y)\| \le \|\bar g(\tau)\|_{\mathcal{H}} \, \|\Phi(y)\|_{H_0} \le BC$. Thus, they are $BC$-Lipschitz in time, and for every $x$,
$$\|X^{\bar g}_{a, x}(t) - X^{\bar g}_{a, x}(t')\| \le BC \, |t - t'| \le \frac{BC \, \eta}{BC + 1} < \eta.$$
By (E), $\|F g(t) - F g(t')\| \le \varepsilon / 2 < \varepsilon$. In particular, $F g$ is continuous on $[a, b]$ for every $g \in S$.

For $g \in S$, let $G g = F g$, a bounded continuous curve on the compact interval $[a, b]$. For $g \notin S$, let $G g = g$, which plays no role. Then $G(S) \subseteq S$.

*Continuity.* We show that $G$ is continuous on $S$. Let $g \in S$ and $\varepsilon > 0$. By Lemma A.6 (i), there is $\eta > 0$ such that $\|\xi_x - \xi_y\| < \varepsilon / 2$ for all $x, y \in \Omega$ with $\|x - y\| < \eta$. For $\theta \in \mathbb{R}$ and $r \ge 0$, let
$$\gamma(\theta, r) = \begin{cases} \theta \, r & \text{if } BK = 0, \\ \dfrac{\theta}{BK} \big(e^{BKr} - 1\big) & \text{otherwise}, \end{cases}$$
be the Grönwall bound with zero initial distance. It is continuous in $\theta$, nondecreasing in $r$ for $\theta \ge 0$, and $\gamma(0, r) = 0$. Thus, there is $\delta > 0$ such that $\gamma(C \theta, b - a) < \eta$ for every $\theta \in [0, \delta)$. Let $g' \in S$ with $d_\infty(g', g) < \delta$. Then $\|\bar g'(\tau) - \bar g(\tau)\| \le d_\infty(g', g)$ for every $\tau \in \mathbb{R}$. Thus, the trajectory of $\bar g$ through $x$ is an approximate solution of the field of $\bar g'$, with error
$$\|\bar g(\tau)_\Phi(y) - \bar g'(\tau)_\Phi(y)\| \le \|\bar g(\tau) - \bar g'(\tau)\|_{\mathcal{H}} \, \|\Phi(y)\|_{H_0} \le C \, d_\infty(g', g),$$
and the field of $\bar g'$ is $BK$-Lipschitz. By Grönwall's inequality for approximate solutions, for all $t \in [a, b]$ and $x \in \Omega$,
$$\begin{aligned} \|X^{\bar g'}_{a, x}(t) - X^{\bar g}_{a, x}(t)\| &\le \gamma\big(C \, d_\infty(g', g), t - a\big) \\ &\le \gamma\big(C \, d_\infty(g', g), b - a\big) \\ &< \eta. \end{aligned}$$
By (E), $\|G g'(t) - G g(t)\| \le \varepsilon / 2$ for every $t \in [a, b]$. Hence, $d_\infty(G g', G g) \le \varepsilon / 2 < \varepsilon$.

*Causality.* Let $g, g' \in S$ and $\tau \in [a, b]$ with $g = g'$ on $[a, \tau]$. Then $\bar g = \bar g'$ on $[a, \tau]$. Two continuous curves bounded by $B$ that agree between times $a$ and $\tau$ have the same trajectories from $a$ to $\tau$, by uniqueness of the solutions. Thus, $X^{\bar g}_{a, \cdot}(\tau) = X^{\bar g'}_{a, \cdot}(\tau)$, and $G g(\tau) = G g'(\tau)$. Finally, $X^{\bar g}_{a, x}(a) = x$ for every $x$, so $G g(a) = \varphi^*_\nu$ for every $g \in S$.

*Fixed point.* The set $\mathcal{K}$ is compact by Claim 1. It is nonempty, as it contains $\xi(\Omega)$ and $\Omega \ne \emptyset$. Thus, the theorem of Step 2 applies, with $Y = \mathcal{H}$ and $\mathcal{K}' = \mathcal{K}$. Its hypotheses (i) to (v) are the properties of $G$ proved above, and (iii) follows from the equicontinuity. It gives $g \in S$ with $G g = g$. Let $m = \bar g$. Then $m$ is continuous, and $m(t) = g(\operatorname{pr}(t)) \in \mathcal{K}$ for every $t \in \mathbb{R}$. For $t \in [a, b]$, we have that $\bar g(t) = g(t)$, so
$$m(t) = g(t) = G g(t) = \varphi^*_{(X^m_{a, \cdot}(t))_\#\nu},$$
which proves Claim 4.

**Step 4.** Concatenation. For every $n \in \mathbb{N}$ and every measure $\nu$ on $\mathbb{R}^d$, we choose a curve $m_{n, \nu} : \mathbb{R} \to \mathcal{H}$ as follows. If $\nu \in \mathcal{P}(\Omega)$, Claim 4 with $a = n$ and $b = n + 1$ gives a continuous curve $m_{n, \nu}$ with values in $\mathcal{K}$ such that
$$\forall t \in [n, n + 1], \quad m_{n, \nu}(t) = \varphi^*_{(X^{m_{n, \nu}}_{n, \cdot}(t))_\#\nu}.$$
Otherwise, $m_{n, \nu}$ is an arbitrary curve, which plays no role. We define the measures $\nu_n$ reached at the integer times, and the curves $m_n$, by induction,
$$\nu_0 = \mu, \qquad m_n = m_{n, \nu_n}, \qquad \nu_{n + 1} = \big(X^{m_n}_{n, \cdot}(n + 1)\big)_\#\nu_n.$$
By induction, $\nu_n \in \mathcal{P}(\Omega)$ for every $n$. First, $\nu_0 = \mu \in \mathcal{P}(\Omega)$. If $\nu_n \in \mathcal{P}(\Omega)$, then $m_n$ is continuous and bounded by $B$, and its trajectories stay in $\Omega$. Thus, $\nu_{n+1}$ is a probability measure carried by $\Omega$. Hence, every $m_n$ is continuous, with values in $\mathcal{K}$, bounded by $B$, and solves the equation on $[n, n + 1]$ from $\nu_n$ at time $n$.

Let $\lfloor t \rfloor_+ = \max(\lfloor t \rfloor, 0) \in \mathbb{N}$. The concatenated curve is
$$M(t) = m_{\lfloor t \rfloor_+}(t), \qquad t \in \mathbb{R}.$$

**Claim 5.** For every $n \in \mathbb{N}$, $M = m_n$ on $[n, n + 1]$. For $t \in [n, n + 1)$, we have that $\lfloor t \rfloor_+ = n$, so $M(t) = m_n(t)$. At $t = n + 1$, both curves are the update direction of $\nu_{n+1}$. As $X^{m_{n+1}}_{n+1, x}(n + 1) = x$ for every $x$, we have that
$$\begin{aligned} M(n + 1) = m_{n+1}(n + 1) &= \varphi^*_{(X^{m_{n+1}}_{n+1, \cdot}(n+1))_\#\nu_{n+1}} \\ &= \varphi^*_{\nu_{n+1}} \\ &= \varphi^*_{(X^{m_n}_{n, \cdot}(n+1))_\#\nu_n} \\ &= m_n(n + 1). \end{aligned}$$

We also have that $M = m_0$ on $(-\infty, 1]$, as $\lfloor t \rfloor_+ = 0$ for $t < 1$, and by Claim 5 at $t = 1$. Thus, $M$ is continuous by the following gluing lemma. A function on $\mathbb{R}$ that agrees with a continuous function $f_0$ on $(-\infty, 1]$, and with a continuous function $f_n$ on $[n, n + 1]$ for every $n \in \mathbb{N}$, is continuous. As $M(t) = m_{\lfloor t \rfloor_+}(t) \in \mathcal{K}$ for every $t \in \mathbb{R}$, $M$ is bounded by $B$.

**Claim 6.** For $n \in \mathbb{N}$ and $t \in [n, n + 1]$,
$$(X^M_{0, \cdot}(t))_\#\mu = \big(X^{m_n}_{n, \cdot}(t)\big)_\#\big((X^M_{0, \cdot}(n))_\#\mu\big).$$
By the flow property, $X^M_{0, x}(t) = X^M_{n, X^M_{0, x}(n)}(t)$ for every $x$. As $M = m_n$ on $[n, t]$ by Claim 5, we have that $X^M_{n, y}(t) = X^{m_n}_{n, y}(t)$ for every $y$. Thus, $X^M_{0, \cdot}(t) = X^{m_n}_{n, \cdot}(t) \circ X^M_{0, \cdot}(n)$. Both maps are continuous, so the push-forward by this composition is the composition of the push-forwards.

**Claim 7.** For every $n \in \mathbb{N}$, $(X^M_{0, \cdot}(n))_\#\mu = \nu_n$. We proceed by induction on $n$. For $n = 0$, $X^M_{0, x}(0) = x$ for every $x$, so the measure is $\mu = \nu_0$. If the claim holds for $n$, Claim 6 at $t = n + 1$ gives
$$(X^M_{0, \cdot}(n + 1))_\#\mu = \big(X^{m_n}_{n, \cdot}(n + 1)\big)_\#\nu_n = \nu_{n+1}.$$

Finally, let $t \ge 0$ and $n = \lfloor t \rfloor_+$, so that $t \in [n, n + 1]$. By Claim 5, the equation solved by $m_n$, Claim 7 and Claim 6, we have that
$$\begin{aligned} M(t) &= m_n(t) \\ &= \varphi^*_{(X^{m_n}_{n, \cdot}(t))_\#\nu_n} \\ &= \varphi^*_{(X^{m_n}_{n, \cdot}(t))_\#((X^M_{0, \cdot}(n))_\#\mu)} \\ &= \varphi^*_{(X^M_{0, \cdot}(t))_\#\mu}. \end{aligned}$$
Thus, $M$ is a continuous curve with values in $\mathcal{K}$ that solves the mean-field SVGD equation from $\mu$, which concludes the proof.
```

Thus, under the standing assumptions, with $H_0$ a Hilbert space and $\mu \in \mathcal{P}(\Omega)$, a continuous bounded solution exists. The mean-field SVGD curve is one of them. Its flow follows the update directions of its own push-forwards, as in [Serre2025].

{{SVGD.meanFieldCurve_eq_direction | Theorem}}

```informal SVGD.meanFieldCurve_eq_direction
Assume the standing assumptions for $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$ and $C$, and let $H_0$ be a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$. Let $m$ and $T_t$ be the mean-field SVGD curve and flow from $\mu$, and $\mu_t = (T_t)_\#\mu$. Then
$$\forall t \ge 0, \quad m(t) = \varphi^*_{\mu_t}.$$
```

```proof SVGD.meanFieldCurve_eq_direction
By the [previous theorem](#SVGD.exists_meanField), there is a continuous curve with values in the closed convex hull $\mathcal{K}$ of $\xi(\Omega)$ that solves the mean-field SVGD equation from $\mu$. It is bounded, as $\mathcal{K}$ is bounded (Claim 3 in the proof of the [previous theorem](#SVGD.exists_meanField)). Thus, a continuous bounded solution exists, and $m$ is one of them, chosen with the axiom of choice. As $T_t = X^m_{0, \cdot}(t)$, the equation solved by $m$ reads $m(t) = \varphi^*_{(T_t)_\#\mu} = \varphi^*_{\mu_t}$ for every $t \ge 0$.
```

{{SVGD.hasDerivAt_meanFieldFlow | Theorem}}

```informal SVGD.hasDerivAt_meanFieldFlow
Assume the standing assumptions for $\Omega$, $\pi$, $p$, $s$, $\Phi$, $K$ and $C$, and let $H_0$ be a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$, $T_t$ the mean-field SVGD flow from $\mu$, and $\mu_t = (T_t)_\#\mu$. Let $x \in \mathbb{R}^d$ and $t \ge 0$. Then the map $\tau \mapsto T_\tau(x)$, from $\mathbb{R}$ to $\mathbb{R}^d$, is differentiable at $t$, and
$$\frac{d}{dt} T_t(x) = (\varphi^*_{\mu_t})_\Phi\big(T_t(x)\big).$$
```

```proof SVGD.hasDerivAt_meanFieldFlow
Let $m$ be the mean-field SVGD curve from $\mu$. It is [continuous](#SVGD.continuous_meanFieldCurve) and [bounded](#SVGD.exists_norm_meanFieldCurve_le) by some $B \ge 0$. Thus, its vector field is continuous in time and $BK$-Lipschitz in space. As in the proof that [the flow starts at the identity](#SVGD.meanFieldFlow_zero), $\alpha' = m(\tau)_\Phi(\alpha)$ has a solution on $\mathbb{R}$ through $x$ at time $0$. Hence, $\tau \mapsto T_\tau(x) = X^m_{0, x}(\tau)$ is such a solution, and it is differentiable at $t$ with
$$\frac{d}{dt} T_t(x) = m(t)_\Phi\big(T_t(x)\big).$$
As $t \ge 0$, we have that $m(t) = \varphi^*_{\mu_t}$ by the [previous theorem](#SVGD.meanFieldCurve_eq_direction), which concludes the proof.
```

## The time derivative of the Kullback–Leibler divergence

Along a solution of the mean-field equation, the particles follow $\varphi^*_{\mu_t}$, the direction of
steepest descent of Theorem A.8. Thus, the Kullback–Leibler divergence to $\pi$ decreases at rate
$\mathfrak{K}(\mu_t \mid \pi)$. The proof is Lagrangian. It transports $\pi$ backwards along the flow,
and needs neither a density for $\mu_t$ nor the continuity equation.

{{SVGD.time_derivative_kl' | Theorem A.11′ (i)}}

```informal SVGD.time_derivative_kl'
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let
$B \ge 0$, and let $m : \mathbb{R} \to \mathcal{H}$ be continuous with $\|m(t)\|_{\mathcal{H}} \le B$ for
every $t \in \mathbb{R}$. For $t \in \mathbb{R}$, let $T_t(x) = X^m_{0, x}(t)$ and
$\mu_t = (T_t)_\#\mu$. Assume that $m$ solves the mean-field equation from $\mu$, i.e.
$$\forall t \ge 0, \quad m(t) = \varphi^*_{\mu_t}.$$
For $t \in \mathbb{R}$, let $F(t) = \mathrm{KL}(\mu_t \,\|\, \pi)$ if this divergence is finite, and
$F(t) = 0$ otherwise. Then, for every $t \ge 0$, $F : \mathbb{R} \to \mathbb{R}$ is differentiable at
$t$ and
$$F'(t) = -\mathfrak{K}(\mu_t \mid \pi).$$
The derivative is two-sided, also at $t = 0$.
```

```proof SVGD.time_derivative_kl'
We first show that $\mu_t \in \mathcal{P}(\Omega)$ for every $t \in \mathbb{R}$, i.e. that $\mu_t$ is a
probability measure with $x \in \Omega$ for $\mu_t$-almost every $x$. As in the proof of
Theorem A.8 (i), $\mathrm{KL}(\mu \,\|\, \pi) < \infty$ gives $\mu \ll \pi$, so $\mu$ is carried by
$\Omega$. The vector fields $m(\tau)_\Phi$ are
$BK$-Lipschitz, and they vanish on $\partial \Omega$, as $\Phi$ does. Thus, a trajectory that starts in
$\Omega$ at time $0$ is in $\Omega$ at every time $t \in \mathbb{R}$, forward or backward. Indeed, let $x \in \Omega$ and assume that $X^m_{0, x}(t) \notin \Omega$. The
image by $X^m_{0, x}$ of the interval between $0$ and $t$ is connected. It meets $\Omega$ and its
complement, so it meets $\partial \Omega$ at some time $\tau$. Then, $X^m_{0, x}$ passes through
$X^m_{0, x}(\tau)$, a common zero of the fields. By uniqueness of the solutions, it is constant. Thus,
$X^m_{0, x}(t) = x \in \Omega$, a contradiction. As $T_t$ is
continuous, $\mu_t = (T_t)_\#\mu$ is carried by $\Omega$. It is a
probability measure, as $\mu$ is.

The proof rests on the following general dissipation formula along a flow. Let $E$, $\mathrm{vol}$, $\Omega$, $p$, $s$
and $\pi = p \cdot \mathrm{vol}|_\Omega$ be as in the first variation formula of the proof of
Theorem A.8 (i). Let $v : \mathbb{R} \times E \to E$ be a time-dependent vector field. Assume that
$t \mapsto v(t, y)$ is continuous for every $y \in E$, and that every $v(t, \cdot)$ is $K'$-Lipschitz,
for a common $K' \ge 0$. Assume that every $v(t, \cdot)$ is differentiable, with a derivative
$Dv(t, y)$ jointly continuous in $(t, y)$. Assume that $v(t, y) = 0$ for every $t \in \mathbb{R}$ and
$y \in \partial \Omega$. Let $\alpha : E \times \mathbb{R} \to E$ be a flow of $v$ from time $0$, i.e.
$$\forall x \in E, \forall t \in \mathbb{R}, \quad \partial_t \alpha(x, t) = v(t, \alpha(x, t)), \quad \alpha(x, 0) = x.$$
Let $\mu$ be a finite measure on $E$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. For $t \in \mathbb{R}$,
let $F_\alpha(t) = \mathrm{KL}(\alpha(\cdot, t)_\#\mu \,\|\, \pi)$ if this divergence is finite, and
$F_\alpha(t) = 0$ otherwise. Then, for every $t_0 \in \mathbb{R}$, $F_\alpha$ is differentiable at
$t_0$, with
$$F_\alpha'(t_0) = -\int \big( s(y)(v(t_0, y)) + \operatorname{div} v(t_0, \cdot)(y) \big) \, d\big(\alpha(\cdot, t_0)_\#\mu\big)(y).$$

This formula is proved as follows. Let $t \in \mathbb{R}$. The flow map $\alpha(\cdot, t)$ is a
homeomorphism of $E$, and it maps $\Omega$ onto $\Omega$. It is differentiable,
and its derivative solves the variational equation
$\partial_t D\alpha(\cdot, t)(x) = Dv(t, \alpha(x, t)) \circ D\alpha(\cdot, t)(x)$. By Jacobi's formula, its Jacobian determinant
$J_t(x) = \det D\alpha(\cdot, t)(x)$ solves Liouville's equation
$\partial_t J_t(x) = \operatorname{div} v(t, \cdot)(\alpha(x, t)) \, J_t(x)$, with $J_0(x) = 1$. As $v(t, \cdot)$ is $K'$-Lipschitz, we have that
$|\operatorname{div} v(t, \cdot)| \le \|\operatorname{tr}\| K'$. Here $\|\operatorname{tr}\|$ is the
operator norm of the trace. If $J_t(x) \le 0$ for some $t$, then $J_\tau(x) = 0$ for some $\tau$, by
the intermediate value theorem. By uniqueness of the solutions of this linear equation,
$\tau \mapsto J_\tau(x)$ would then vanish identically, which contradicts $J_0(x) = 1$. Thus,
$J_t(x) > 0$. Then, Liouville's formula in logarithmic form gives
$\partial_t \log J_t(x) = \operatorname{div} v(t, \cdot)(\alpha(x, t))$. By the mean value inequality,
$|\log J_t(x)| \le \|\operatorname{tr}\| K' |t|$. Thus,
$\log J_t$ is bounded, hence $\mu$-integrable. The transport formula
(see the proof of [Theorem A.8 (i)](#SVGD.kl_steepest_descent_hasDerivAt)) then gives, for every
$t \in \mathbb{R}$,
$$F_\alpha(t) = \mathrm{KL}(\mu \,\|\, \pi) - \int G(t, x) \, d\mu(x), \quad G(t, x) = \log p(\alpha(x, t)) - \log p(x) + \log J_t(x).$$
We differentiate under the integral sign on $(t_0 - 1, t_0 + 1)$. The function $G(t_0, \cdot)$ is
$\mu$-integrable. Indeed, $\log p$ is continuous on the compact set $\Omega$, which carries $\mu$ and
is mapped into itself by $\alpha(\cdot, t_0)$, and $\log J_{t_0}$ is bounded. Let $x \in \Omega$, which
holds for $\mu$-almost every $x$. Then, $\alpha(x, t) \in \Omega$ for every $t$. If $x$ is in the
interior of $\Omega$, so is $\alpha(x, t)$ for every $t$. Then, the chain rule gives
$\partial_t \log p(\alpha(x, t)) = s(\alpha(x, t))(v(t, \alpha(x, t)))$. Otherwise, $x \in \partial \Omega$.
Then, the trajectory through $x$ is constant and $v(t, x) = 0$, so
both sides vanish. With Liouville's formula in logarithmic form, we obtain
$$\partial_t G(t, x) = s(\alpha(x, t))(v(t, \alpha(x, t))) + \operatorname{div} v(t, \cdot)(\alpha(x, t)).$$
For $|t - t_0| < 1$, this derivative is bounded by $S V + \|\operatorname{tr}\| K'$. Here $S$ bounds
$\|s\|$ on $\Omega$, and $V$ bounds $\|v\|$ on the compact set $[t_0 - 1, t_0 + 1] \times \Omega$. Such
a $V$ exists, as $v$ is jointly continuous, being continuous in time and $K'$-Lipschitz in space. The measurability conditions are routine. Thus,
$t \mapsto \int G(t, x) \, d\mu(x)$ is differentiable at $t_0$, with derivative
$\int \partial_t G(t_0, x) \, d\mu(x)$. Finally, the change of variables $y = \alpha(x, t_0)$ turns this
integral against $\mu$ into the integral against $\alpha(\cdot, t_0)_\#\mu$ in the formula.

We apply this formula with $E = \mathbb{R}^d$, $\mathrm{vol} = \lambda$, $v(t, y) = m(t)_\Phi(y)$ and
$\alpha(x, t) = X^m_{0, x}(t) = T_t(x)$. Then,
$F_\alpha = F$. The hypotheses on $\Omega$, $p$ and $s$ are the standing assumptions, and $\mu$ is a
probability measure. The map $t \mapsto m(t)_\Phi(y)$ is continuous, as $m$ is. Every $m(t)_\Phi$ is $BK$-Lipschitz, as
$\|m(t)\|_{\mathcal{H}} \le B$ and $\Phi$ is $K$-Lipschitz. For $h \in \mathcal{H}$, let
$P_h : H_0 \to \mathbb{R}^d$ be the continuous linear map $u \mapsto (\langle h_i, u \rangle_{H_0})_i$,
so that $h_\Phi = P_h \circ \Phi$. The derivative of $m(t)_\Phi$ is
$D(m(t)_\Phi)(y) = P_{m(t)} \circ D\Phi(y)$. It is jointly
continuous in $(t, y)$, as $m$ is continuous and $\Phi$ is $C^1$. The fields vanish on $\partial \Omega$, as $\Phi$
does. As they are continuous in time and Lipschitz in space, $X^m_{0, x}$ solves
$\partial_t X^m_{0, x}(t) = m(t)_\Phi(X^m_{0, x}(t))$ with $X^m_{0, x}(0) = x$. Thus, for every $t \in \mathbb{R}$, $F$ is
differentiable at $t$ and
$$F'(t) = -\int \big( s(y)(m(t)_\Phi(y)) + \operatorname{div} m(t)_\Phi(y) \big) \, d\mu_t(y) = -\mathbb{E}_{y \sim \mu_t}[\mathcal{A}_\pi m(t)(y)].$$

Now, let $t \ge 0$. As $\mu_t \in \mathcal{P}(\Omega)$ and $H_0$ is a Hilbert space, Theorem A.7 applies
to $\mu_t$. The mean-field equation gives $m(t) = \varphi^*_{\mu_t}$. We obtain
$$\begin{aligned} \mathbb{E}_{y \sim \mu_t}[\mathcal{A}_\pi m(t)(y)] &= \langle m(t), \varphi^*_{\mu_t} \rangle_{\mathcal{H}} \quad (\text{Theorem A.7 (i)}) \\ &= \langle m(t), m(t) \rangle_{\mathcal{H}} = \|m(t)\|_{\mathcal{H}}^2 \quad (\text{mean-field equation}) \\ &= \|\varphi^*_{\mu_t}\|_{\mathcal{H}}^2 \quad (\text{mean-field equation}) \\ &= \mathfrak{K}(\mu_t \mid \pi) \quad (\text{Theorem A.7 (iii)}). \end{aligned}$$
Therefore,
$F'(t) = -\mathfrak{K}(\mu_t \mid \pi)$, which concludes the proof.
```

Along the mean-field SVGD flow, $m$ is the mean-field curve. It solves the mean-field equation as
soon as $\mu \in \mathcal{P}(\Omega)$, which follows from $\mathrm{KL}(\mu \,\|\, \pi) < \infty$.

{{SVGD.time_derivative_kl | Theorem A.11 (i)}}

```informal SVGD.time_derivative_kl
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let
$(T_t)_{t \in \mathbb{R}}$ be the [mean-field SVGD flow](#SVGD.meanFieldFlow) from $\mu$, and
$\mu_t = (T_t)_\#\mu$. For $t \in \mathbb{R}$, let $F(t) = \mathrm{KL}(\mu_t \,\|\, \pi)$ if this
divergence is finite, and $F(t) = 0$ otherwise. Then, for every $t \ge 0$,
$F : \mathbb{R} \to \mathbb{R}$ is differentiable at $t$ and
$$F'(t) = -\mathfrak{K}(\mu_t \mid \pi).$$
The derivative is two-sided, also at $t = 0$.
```

```proof SVGD.time_derivative_kl
Let $m$ be the [mean-field SVGD curve](#SVGD.meanFieldCurve) from $\mu$, so that $T_t(x) = X^m_{0, x}(t)$
by definition. The curve $m$ is [continuous](#SVGD.continuous_meanFieldCurve) and [bounded](#SVGD.exists_norm_meanFieldCurve_le), i.e. there is
$B \ge 0$ such that $\|m(t)\|_{\mathcal{H}} \le B$ for every $t \in \mathbb{R}$. Both facts hold without any hypothesis, as
$m$ is $0$ when the mean-field equation has no continuous bounded solution. As
$\mathrm{KL}(\mu \,\|\, \pi) < \infty$, $\mu$ is carried by $\Omega$ (see the proof of
Theorem A.11′ (i)). Thus, $\mu \in \mathcal{P}(\Omega)$. Then, the mean-field equation from $\mu$ has a
continuous solution with values in the closed convex hull of $\xi(\Omega)$, by the [existence theorem](#SVGD.exists_meanField).
This hull is compact, hence bounded, so this solution is bounded. The curve $m$ is then such a
solution, i.e. $m(t) = \varphi^*_{\mu_t}$ for every $t \ge 0$.
Theorem A.11′ (i) applied to $m$ concludes the proof.
```

As the kernelized Stein discrepancy is nonnegative, the Kullback–Leibler divergence is
non-increasing along the flow. This is the second part of Theorem A.11.

{{SVGD.time_derivative_kl_antitoneOn' | Theorem A.11′ (ii)}}

```informal SVGD.time_derivative_kl_antitoneOn'
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let
$B \ge 0$, and let $m : \mathbb{R} \to \mathcal{H}$ be continuous with $\|m(t)\|_{\mathcal{H}} \le B$ for
every $t \in \mathbb{R}$. For $t \in \mathbb{R}$, let $T_t(x) = X^m_{0, x}(t)$ and
$\mu_t = (T_t)_\#\mu$. Assume that $m(t) = \varphi^*_{\mu_t}$ for every $t \ge 0$. For
$t \in \mathbb{R}$, let $F(t) = \mathrm{KL}(\mu_t \,\|\, \pi)$ if this divergence is finite, and
$F(t) = 0$ otherwise. Then, $F$ is non-increasing on $[0, \infty)$, i.e.
$$\forall t_1, t_2 \in [0, \infty), \quad t_1 \le t_2 \implies F(t_2) \le F(t_1).$$
```

```proof SVGD.time_derivative_kl_antitoneOn'
By Theorem A.11′ (i), $F$ is differentiable at every $t \ge 0$, with
$F'(t) = -\mathfrak{K}(\mu_t \mid \pi)$. Thus, $F$ is continuous on $[0, \infty)$ and differentiable on
its interior $(0, \infty)$. The kernelized Stein discrepancy is a real supremum of squares, which is
$0$ if the family is unbounded. Therefore, $\mathfrak{K}(\nu \mid \pi) \ge 0$ for every measure $\nu$
([nonnegativity of the KSD](#SVGD.ksd_nonneg)). Hence, $F'(t) \le 0$ for every $t > 0$. By the mean value theorem on the convex set
$[0, \infty)$, $F$ is non-increasing on $[0, \infty)$, which concludes
the proof.
```

{{SVGD.time_derivative_kl_antitoneOn | Theorem A.11 (ii)}}

```informal SVGD.time_derivative_kl_antitoneOn
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, and let $H_0$ be a Hilbert space.
Let $\mu$ be a probability measure on $\mathbb{R}^d$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let
$(T_t)_{t \in \mathbb{R}}$ be the [mean-field SVGD flow](#SVGD.meanFieldFlow) from $\mu$, and
$\mu_t = (T_t)_\#\mu$. For $t \in \mathbb{R}$, let $F(t) = \mathrm{KL}(\mu_t \,\|\, \pi)$ if this
divergence is finite, and $F(t) = 0$ otherwise. Then, $F$ is non-increasing on $[0, \infty)$, i.e.
$$\forall t_1, t_2 \in [0, \infty), \quad t_1 \le t_2 \implies F(t_2) \le F(t_1).$$
```

```proof SVGD.time_derivative_kl_antitoneOn
As in the proof of Theorem A.11 (i), the mean-field curve $m$ from $\mu$ is continuous and bounded by
some $B \ge 0$. As
$\mathrm{KL}(\mu \,\|\, \pi) < \infty$, we have that $\mu \in \mathcal{P}(\Omega)$ (see the proof of
Theorem A.11′ (i)). Thus, $m$ solves the mean-field equation from $\mu$. Moreover, $T_t(x) = X^m_{0, x}(t)$ by definition.
Theorem A.11′ (ii) applied to $m$ concludes the proof.
```

## Convergence

Under a universality condition on the kernel, the kernelized Stein discrepancy vanishes on $\mathcal{P}(\Omega)$ only at $\pi$. This condition is the analog, for the Stein operator, of the universality of a kernel.

{{SVGD.IsSteinUniversal | Definition A.9}}

```informal SVGD.IsSteinUniversal
Let $\Omega \subseteq \mathbb{R}^d$ and $s : \mathbb{R}^d \to (\mathbb{R}^d)^*$. Let $H_0$ be a real inner product space and $\Phi : \mathbb{R}^d \to H_0$. Let $C(\Omega, \mathbb{R})$ be the space of continuous functions from $\Omega$ to $\mathbb{R}$, with the compact-open topology, i.e. the topology of uniform convergence on the compact subsets of $\Omega$. The kernel $k(x, y) = \langle \Phi(x), \Phi(y) \rangle$ is *Stein-universal* on $\Omega$ if the set
$$\big\{ \psi \in C(\Omega, \mathbb{R}) \;\big|\; \exists f \in \mathcal{H}, \exists c \in \mathbb{R}, \forall x \in \Omega, \ \psi(x) = \mathcal{A}_\pi f(x) + c \big\}$$
is dense in $C(\Omega, \mathbb{R})$. Here, $\mathcal{A}_\pi f = \mathcal{A}_s (f_\Phi)$ depends on $\pi$ only through its score $s$. Its divergence term is $0$ at the points where $f_\Phi$ is not differentiable.

When $\Omega$ is compact, as under the standing assumptions, this topology is that of uniform convergence on $\Omega$. The kernel is then Stein-universal if and only if
$$\forall \psi \in C(\Omega, \mathbb{R}), \forall \varepsilon > 0, \exists f \in \mathcal{H}, \exists c \in \mathbb{R}, \ \mathcal{A}_\pi f|_\Omega \in C(\Omega, \mathbb{R}) \text{ and } \sup_{x \in \Omega} \big|\psi(x) - \mathcal{A}_\pi f(x) - c\big| < \varepsilon.$$
Under the standing assumptions, $\mathcal{A}_\pi f$ is continuous on $\Omega$ for every $f \in \mathcal{H}$ (see the [continuity of the Stein operator](#SVGD.continuousOn_steinOperator)).

The constants $c$ are needed. Under the standing assumptions, with $H_0$ a Hilbert space, $\mathbb{E}_{x \sim \pi}[\mathcal{A}_\pi f(x)] = 0$ for every $f \in \mathcal{H}$. This follows from Theorem A.7 (i) and (iii), as $\mathfrak{K}(\pi \mid \pi) = 0$ (see the proof of Proposition 3.2). Thus, the functions $\mathcal{A}_\pi f$ alone only approximate functions with zero mean under $\pi$. Integrating against $\pi$ then shows that this definition is equivalent to the formulation of Definition A.9 in [Serre2025], i.e.
$$\forall \psi \in C(\Omega, \mathbb{R}), \forall \varepsilon > 0, \exists f \in \mathcal{H}, \ \sup_{x \in \Omega} \big|\psi(x) - \mathbb{E}_{y \sim \pi}[\psi(y)] - \mathcal{A}_\pi f(x)\big| \le \varepsilon.$$
This equivalence is not formalized.
```

A Stein-universal kernel makes the kernelized Stein discrepancy a valid discrepancy on $\mathcal{P}(\Omega)$. In [Serre2025], the direct implication relies on Stein's identity. The formalization uses Theorem A.8 (i) instead, which needs no Stein class assumption on $\varphi^*_\pi$.

{{SVGD.ksd_valid_discrepancy | Proposition 3.2}}

```informal SVGD.ksd_valid_discrepancy
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Suppose that the kernel is Stein-universal on $\Omega$. Let $\nu \in \mathcal{P}(\Omega)$, i.e. let $\nu$ be a probability measure on $\mathbb{R}^d$ such that $x \in \Omega$ for $\nu$-almost every $x$. Then,
$$\nu = \pi \iff \mathfrak{K}(\nu \mid \pi) = 0.$$
```

```proof SVGD.ksd_valid_discrepancy
First, $\pi \in \mathcal{P}(\Omega)$. By the standing assumptions, $\pi$ is a probability measure. As $\pi = p \cdot \lambda|_\Omega$ is absolutely continuous with respect to $\lambda|_\Omega$, it gives no mass to $\mathbb{R}^d \setminus \Omega$, i.e. $x \in \Omega$ for $\pi$-almost every $x$. Here, $\Omega$ is measurable, as it is compact.

**The discrepancy of $\pi$ is null.** Let's show that $\mathfrak{K}(\pi \mid \pi) = 0$. For $\varepsilon \in \mathbb{R}$, let
$$h(\varepsilon) = \mathrm{KL}\big((I_d + \varepsilon\, (\varphi^*_\pi)_\Phi)_\# \pi \,\big\|\, \pi\big),$$
seen as a real number, where $\infty$ is mapped to $0$. Then, $h \ge 0$ and $h(0) = \mathrm{KL}(\pi \,\|\, \pi) = 0$. Thus, $h$ has a minimum at $0$. As $\mathrm{KL}(\pi \,\|\, \pi) = 0 < \infty$, [Theorem A.8 (i)](#SVGD.kl_steepest_descent_hasDerivAt), applied to $\pi$ and $\varphi^*_\pi$, shows that $h$ is differentiable at $0$, with
$$h'(0) = -\langle \varphi^*_\pi, \varphi^*_\pi \rangle_{\mathcal{H}}.$$
By Fermat's theorem, $h'(0) = 0$. As $\pi \in \mathcal{P}(\Omega)$, [Theorem A.7 (iii)](#SVGD.steepest_trajectory_ksd) gives
$$\mathfrak{K}(\pi \mid \pi) = \|\varphi^*_\pi\|_{\mathcal{H}}^2 = \langle \varphi^*_\pi, \varphi^*_\pi \rangle_{\mathcal{H}} = -h'(0) = 0.$$
Stein's identity (Lemma A.3) would also give this result, but it requires $\varphi^*_\pi$ to be in the Stein class of $\pi$.

**Direct implication.** If $\nu = \pi$, then $\mathfrak{K}(\nu \mid \pi) = \mathfrak{K}(\pi \mid \pi) = 0$.

**Converse implication.** Assume that $\mathfrak{K}(\nu \mid \pi) = 0$. We first show the following claim. Let $\rho \in \mathcal{P}(\Omega)$ such that $\mathfrak{K}(\rho \mid \pi) = 0$. Let $g : \mathbb{R}^d \to \mathbb{R}$ be bounded and continuous, $f \in \mathcal{H}$ and $c, \varepsilon \in \mathbb{R}$ such that
$$\forall x \in \Omega, \ |g(x) - \mathcal{A}_\pi f(x) - c| \le \varepsilon.$$
Then, $|\mathbb{E}_{x \sim \rho}[g(x)] - c| \le \varepsilon$.

Let's prove the claim. By [Theorem A.7 (iii)](#SVGD.steepest_trajectory_ksd), $\|\varphi^*_\rho\|_{\mathcal{H}}^2 = \mathfrak{K}(\rho \mid \pi) = 0$. Thus, $\varphi^*_\rho = 0$. By [Theorem A.7 (i)](#SVGD.steepest_trajectory_integral), we have that
$$\mathbb{E}_{x \sim \rho}[\mathcal{A}_\pi f(x)] = \langle f, \varphi^*_\rho \rangle_{\mathcal{H}} = 0.$$
The function $g$ is $\rho$-integrable, as it is bounded and continuous and $\rho$ is finite. The function $\mathcal{A}_\pi f$ is [continuous](#SVGD.continuousOn_steinOperator) on the compact set $\Omega$, which carries $\rho$. Thus, $\mathcal{A}_\pi f$ is also $\rho$-integrable. As $\rho(\mathbb{R}^d) = 1$, the linearity of the integral gives
$$\mathbb{E}_{x \sim \rho}[g(x)] - c = \mathbb{E}_{x \sim \rho}[g(x) - \mathcal{A}_\pi f(x) - c].$$
As $x \in \Omega$ for $\rho$-almost every $x$, the absolute value of the integrand is at most $\varepsilon$, $\rho$-almost everywhere. Therefore, $|\mathbb{E}_{x \sim \rho}[g(x)] - c| \le \varepsilon \, \rho(\mathbb{R}^d) = \varepsilon$, which proves the claim.

Now, let $g : \mathbb{R}^d \to \mathbb{R}$ be bounded and continuous. Let's show that $\mathbb{E}_{x \sim \nu}[g(x)] = \mathbb{E}_{x \sim \pi}[g(x)]$. It is sufficient to show that the distance between these two numbers is at most $\varepsilon$, for every $\varepsilon > 0$. Let $\varepsilon > 0$. As $\Omega$ is compact, $C(\Omega, \mathbb{R})$ is a metric space for the uniform distance on $\Omega$, and the restriction $g|_\Omega$ lies in it. By Stein-universality, there exist $f \in \mathcal{H}$ and $c \in \mathbb{R}$ such that $\mathcal{A}_\pi f + c$ is continuous on $\Omega$, at uniform distance less than $\varepsilon / 2$ from $g|_\Omega$. In particular,
$$\forall x \in \Omega, \ |g(x) - \mathcal{A}_\pi f(x) - c| \le \frac{\varepsilon}{2}.$$
We apply the claim to $\rho = \nu$, as $\mathfrak{K}(\nu \mid \pi) = 0$, and to $\rho = \pi$, as $\mathfrak{K}(\pi \mid \pi) = 0$. Thus,
$$\begin{aligned} \big|\mathbb{E}_{x \sim \nu}[g(x)] - \mathbb{E}_{x \sim \pi}[g(x)]\big| &\le \big|\mathbb{E}_{x \sim \nu}[g(x)] - c\big| + \big|\mathbb{E}_{x \sim \pi}[g(x)] - c\big| \\ &\le \frac{\varepsilon}{2} + \frac{\varepsilon}{2} = \varepsilon. \end{aligned}$$
Finally, $\nu$ and $\pi$ are finite measures on the metric space $\mathbb{R}^d$ that give the same integral to every bounded continuous function. Two such measures are equal. Hence, $\nu = \pi$, which concludes the proof.
```

The proof of Theorem 3.1 has three steps. First, Theorem A.11 and Barbalat's lemma [Khalil2002] show that $\mathfrak{K}(\mu_t \mid \pi) \to 0$. Next, the discrepancy of every weak cluster point of $(\mu_t)_{t \ge 0}$ is null. Finally, Proposition 3.2 identifies such a cluster point with $\pi$. Barbalat's lemma requires the discrepancy to be uniformly continuous along the flow. This holds for every continuous bounded curve of $\mathcal{H}$, whether it solves the mean-field equation or not.

{{SVGD.ksd_uniform_continuity' | Lemma B.4′}}

```informal SVGD.ksd_uniform_continuity'
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$. Let $B \ge 0$ and let $m : \mathbb{R} \to \mathcal{H}$ be a continuous curve such that $\|m(t)\|_{\mathcal{H}} \le B$ for every $t \in \mathbb{R}$. For $t \in \mathbb{R}$, let $\mu_t = (X^m_{0, \cdot}(t))_\# \mu$ be the push-forward of $\mu$ by $x \mapsto X^m_{0, x}(t)$. Then, the map
$$t \mapsto \mathfrak{K}(\mu_t \mid \pi)$$
is uniformly continuous on $\mathbb{R}$.
```

```proof SVGD.ksd_uniform_continuity'
We first show that $\mu_t \in \mathcal{P}(\Omega)$ for every $t \in \mathbb{R}$. The map $x \mapsto X^m_{0, x}(t)$ is continuous. Thus, $\mu_t$ is a probability measure. For every $\tau \in \mathbb{R}$, the vector field $m(\tau)_\Phi$ is $BK$-Lipschitz, and it vanishes on the frontier of $\Omega$, as $\Phi$ does. Thus, the trajectories that start in $\Omega$ stay in $\Omega$, i.e. $X^m_{0, x}(t) \in \Omega$ for every $x \in \Omega$. As $x \in \Omega$ for $\mu$-almost every $x$, we have that $y \in \Omega$ for $\mu_t$-almost every $y$.

Let $D \in \mathbb{R}$ such that $\forall x \in \Omega, \|\xi_x\|_{\mathcal{H}} \le D$, given by [Lemma A.6 (ii)](#SVGD.xi_regularity_exists_bound).

**Steps 1 and 2.** Let's show that $t \mapsto \varphi^*_{\mu_t}$ is uniformly continuous from $\mathbb{R}$ to $\mathcal{H}$. By definition, $\varphi^*_{\mu_t} = \int \xi_y \, d\mu_t(y)$. We use the following result. Let $\Omega$ be compact, and let $\Phi$ be $K$-Lipschitz, bounded by $C$ and zero on the frontier of $\Omega$. Let $\mu \in \mathcal{P}(\Omega)$, $E$ a real normed space, $F : \mathbb{R}^d \to E$ uniformly continuous on $\Omega$, and $\varepsilon > 0$. There exists $\delta > 0$ such that, for every continuous curve $m'$ of $\mathcal{H}$ bounded by $B$ and all $a, t, r \in \mathbb{R}$,
$$|t - r| < \delta \implies \Big\| \int F \, d\big(X^{m'}_{a, \cdot}(t)\big)_\# \mu - \int F \, d\big(X^{m'}_{a, \cdot}(r)\big)_\# \mu \Big\| < \varepsilon.$$
Its proof follows Steps 1 and 2 of [Serre2025]. As $\|m'(\tau)_\Phi(y)\|_2 \le \|m'(\tau)\|_{\mathcal{H}} \|\Phi(y)\| \le BC$, the mean value inequality shows that the trajectories are $BC$-Lipschitz in time. Let $\eta > 0$ such that $\|F(x) - F(y)\| < \varepsilon / 2$ for all $x, y \in \Omega$ with $\|x - y\|_2 < \eta$, and let $\delta = \eta / (BC + 1)$. If $|t - r| < \delta$, then $\|X^{m'}_{a, x}(t) - X^{m'}_{a, x}(r)\|_2 < \eta$ for every $x \in \mathbb{R}^d$. When $x \in \Omega$, these two points lie in $\Omega$, so that $\|F(X^{m'}_{a, x}(t)) - F(X^{m'}_{a, x}(r))\| \le \varepsilon / 2$. As $\mu$ is a probability measure carried by $\Omega$, the change of variables formula then bounds the distance between the two integrals by $\varepsilon / 2 < \varepsilon$.

By [Lemma A.6 (i)](#SVGD.xi_regularity_uniformContinuousOn), $x \mapsto \xi_x$ is uniformly continuous on $\Omega$. Applying this result to $F = \xi$, $m' = m$ and $a = 0$ shows that $t \mapsto \varphi^*_{\mu_t}$ is uniformly continuous.

**Step 3.** Let's show that $t \mapsto \mathfrak{K}(\mu_t \mid \pi)$ is uniformly continuous. As $\mu_t \in \mathcal{P}(\Omega)$, [Theorem A.7 (iii)](#SVGD.steepest_trajectory_ksd) gives
$$\forall t \in \mathbb{R}, \ \mathfrak{K}(\mu_t \mid \pi) = \|\varphi^*_{\mu_t}\|_{\mathcal{H}}^2.$$
The norm is $1$-Lipschitz, so $t \mapsto \|\varphi^*_{\mu_t}\|_{\mathcal{H}}$ is uniformly continuous. By [Lemma A.6 (iv)](#SVGD.xi_regularity_norm_direction_le), it takes its values in $[0, D]$. By Heine's theorem, the continuous map $x \mapsto x^2$ is uniformly continuous on the compact interval $[0, D]$. Thus, the composition $t \mapsto \|\varphi^*_{\mu_t}\|_{\mathcal{H}}^2 = \mathfrak{K}(\mu_t \mid \pi)$ is uniformly continuous on $\mathbb{R}$, which concludes the proof.
```

Along the mean-field SVGD flow, Lemma B.4′ applies to the mean-field curve.

{{SVGD.ksd_uniform_continuity | Lemma B.4}}

```informal SVGD.ksd_uniform_continuity
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Let $\mu \in \mathcal{P}(\Omega)$. Let $(T_t)_{t \in \mathbb{R}}$ be the [mean-field SVGD flow](#SVGD.meanFieldFlow) from $\mu$, and let $\mu_t = (T_t)_\# \mu$. Then, the map
$$t \mapsto \mathfrak{K}(\mu_t \mid \pi)$$
is uniformly continuous on $\mathbb{R}$.
```

```proof SVGD.ksd_uniform_continuity
Let $m$ be the [mean-field SVGD curve](#SVGD.meanFieldCurve) from $\mu$. By definition of the flow, $T_t(x) = X^m_{0, x}(t)$. The curve $m$ is [continuous](#SVGD.continuous_meanFieldCurve), and [bounded](#SVGD.exists_norm_meanFieldCurve_le) by some $B \ge 0$, i.e. $\forall t \in \mathbb{R}, \|m(t)\|_{\mathcal{H}} \le B$. These two properties hold by construction of $m$, even if the mean-field equation had no solution, as $m = 0$ in that case. Lemma B.4′ applied to $m$ concludes the proof.
```

Combined with Theorem A.11′ and Barbalat's lemma, Lemma B.4′ shows that the discrepancy tends to $0$ along every continuous bounded solution of the mean-field equation from $\mu$, when $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Theorem A.11′ needs this hypothesis, which Theorem 3.1 of [Serre2025] does not state. From now on, it replaces $\mu \in \mathcal{P}(\Omega)$, which it implies.

{{SVGD.ksd_convergence' | Corollary B.5′}}

```informal SVGD.ksd_convergence'
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Let $\mu$ be a probability measure on $\mathbb{R}^d$ such that $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let $B \ge 0$ and let $m : \mathbb{R} \to \mathcal{H}$ be a continuous curve such that $\|m(t)\|_{\mathcal{H}} \le B$ for every $t \in \mathbb{R}$. Let $\mu_t = (X^m_{0, \cdot}(t))_\# \mu$ for $t \in \mathbb{R}$. Suppose that $m$ solves the mean-field equation from $\mu$, i.e.
$$\forall t \ge 0, \ m(t) = \varphi^*_{\mu_t}.$$
Then,
$$\mathfrak{K}(\mu_t \mid \pi) \xrightarrow[t \to \infty]{} 0.$$
```

```proof SVGD.ksd_convergence'
We first show that $\mu \in \mathcal{P}(\Omega)$. As $\mathrm{KL}(\mu \,\|\, \pi) < \infty$, $\mu$ is absolutely continuous with respect to $\pi$. As shown in the proof of Proposition 3.2, $\pi$ gives no mass to $\mathbb{R}^d \setminus \Omega$. Thus, neither does $\mu$, i.e. $x \in \Omega$ for $\mu$-almost every $x$.

For $t \in \mathbb{R}$, let $F(t) = \mathrm{KL}(\mu_t \,\|\, \pi)$, seen as a real number, where $\infty$ is mapped to $0$, and let $G(t) = \mathfrak{K}(\mu_t \mid \pi)$. We use the following form of Barbalat's lemma. Let $a, c \in \mathbb{R}$ and $u, v : \mathbb{R} \to \mathbb{R}$. Suppose that, for every $t \ge a$, $u$ has derivative $-v(t)$ at $t$ within $[a, \infty)$, $u(t) \ge c$ and $v(t) \ge 0$. Suppose also that $v$ is uniformly continuous on $[a, \infty)$. Then, $v(t) \to 0$ as $t \to \infty$. Indeed, $u$ is non-increasing and bounded below on $[a, \infty)$, so it has a limit at $\infty$. Barbalat's lemma then applies. It states that the derivative of a function with a limit at $\infty$ tends to $0$, if it is uniformly continuous on $[a, \infty)$. Lemma 8.2 of [Khalil2002] states it for a uniformly continuous function with a convergent integral, and [Serre2025] applies it in this form to $G$. Thus, $-v(t) \to 0$.

We apply this result with $a = c = 0$, $u = F$ and $v = G$. By [Theorem A.11′ (i)](#SVGD.time_derivative_kl'), for every $t \ge 0$, $F$ is differentiable at $t$, with $F'(t) = -G(t)$. We also have that $F \ge 0$ and $G \ge 0$ ([nonnegativity of the KSD](#SVGD.ksd_nonneg)). As $\mu \in \mathcal{P}(\Omega)$, Lemma B.4′ shows that $G$ is uniformly continuous on $\mathbb{R}$, hence on $[0, \infty)$. Therefore, $G(t) \to 0$ as $t \to \infty$, which concludes the proof.
```

{{SVGD.ksd_convergence | Corollary B.5}}

```informal SVGD.ksd_convergence
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Let $\mu$ be a probability measure on $\mathbb{R}^d$ such that $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let $(T_t)_{t \in \mathbb{R}}$ be the [mean-field SVGD flow](#SVGD.meanFieldFlow) from $\mu$, and let $\mu_t = (T_t)_\# \mu$. Then,
$$\mathfrak{K}(\mu_t \mid \pi) \xrightarrow[t \to \infty]{} 0.$$
```

```proof SVGD.ksd_convergence
As shown in the proof of Corollary B.5′, $\mu \in \mathcal{P}(\Omega)$. Let $m$ be the [mean-field SVGD curve](#SVGD.meanFieldCurve) from $\mu$, so that $T_t(x) = X^m_{0, x}(t)$. It is [continuous](#SVGD.continuous_meanFieldCurve) and [bounded](#SVGD.exists_norm_meanFieldCurve_le) by some $B \ge 0$. As $\mu \in \mathcal{P}(\Omega)$, the mean-field equation has a continuous solution with values in the closed convex hull of $\{\xi_x \mid x \in \Omega\}$, by the [existence theorem](#SVGD.exists_meanField). This hull is compact, hence bounded. Thus, a continuous bounded solution exists, and $m$ is one of them by definition, i.e.
$$\forall t \ge 0, \ m(t) = \varphi^*_{\mu_t}.$$
Corollary B.5′ applied to $m$ concludes the proof.
```

Next, the discrepancy of every weak cluster point of the flow is null. The weak convergence $\mu_{t_n} \rightharpoonup \nu$ is tested against every function $g : \mathbb{R}^d \to \mathbb{R}$ continuous on $\Omega$. All the measures involved are carried by the compact set $\Omega$, on which $g$ is bounded. Thus, these integrals are well defined. For measures carried by $\Omega$, this is the weak convergence of [Serre2025], whose test functions are the continuous functions on $\Omega$.

{{SVGD.cluster_points' | Lemma B.6′}}

```informal SVGD.cluster_points'
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Let $\mu$ be a probability measure on $\mathbb{R}^d$ such that $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let $B \ge 0$ and let $m : \mathbb{R} \to \mathcal{H}$ be a continuous curve such that $\|m(t)\|_{\mathcal{H}} \le B$ for every $t \in \mathbb{R}$. Let $\mu_t = (X^m_{0, \cdot}(t))_\# \mu$ for $t \in \mathbb{R}$, and suppose that $m(t) = \varphi^*_{\mu_t}$ for every $t \ge 0$. Let $(t_n)_{n \in \mathbb{N}}$ be a real sequence such that $t_n \to \infty$, and let $\nu \in \mathcal{P}(\Omega)$ such that, for every function $g : \mathbb{R}^d \to \mathbb{R}$ continuous on $\Omega$,
$$\mathbb{E}_{x \sim \mu_{t_n}}[g(x)] \xrightarrow[n \to \infty]{} \mathbb{E}_{x \sim \nu}[g(x)].$$
Then,
$$\mathfrak{K}(\nu \mid \pi) = 0.$$
```

```proof SVGD.cluster_points'
As shown in the proof of Corollary B.5′, $\mu \in \mathcal{P}(\Omega)$. Thus, as shown in the proof of Lemma B.4′, $\mu_\tau \in \mathcal{P}(\Omega)$ for every $\tau \in \mathbb{R}$. We compute the limit of the sequence
$$a_n = \langle \varphi^*_\nu, \varphi^*_{\mu_{t_n}} \rangle_{\mathcal{H}}$$
in two ways.

**First limit.** As $\mu_{t_n} \in \mathcal{P}(\Omega)$, [Theorem A.7 (i)](#SVGD.steepest_trajectory_integral) gives $a_n = \mathbb{E}_{x \sim \mu_{t_n}}[\mathcal{A}_\pi \varphi^*_\nu(x)]$. The function $\mathcal{A}_\pi \varphi^*_\nu$ is [continuous](#SVGD.continuousOn_steinOperator) on $\Omega$. Thus, by hypothesis, and by Theorem A.7 (i) at $\nu \in \mathcal{P}(\Omega)$,
$$a_n = \mathbb{E}_{x \sim \mu_{t_n}}[\mathcal{A}_\pi \varphi^*_\nu(x)] \xrightarrow[n \to \infty]{} \mathbb{E}_{x \sim \nu}[\mathcal{A}_\pi \varphi^*_\nu(x)] = \langle \varphi^*_\nu, \varphi^*_\nu \rangle_{\mathcal{H}} = \|\varphi^*_\nu\|_{\mathcal{H}}^2.$$

**Second limit.** By Corollary B.5′, and by [Theorem A.7 (iii)](#SVGD.steepest_trajectory_ksd) at $\mu_\tau \in \mathcal{P}(\Omega)$,
$$\|\varphi^*_{\mu_\tau}\|_{\mathcal{H}}^2 = \mathfrak{K}(\mu_\tau \mid \pi) \xrightarrow[\tau \to \infty]{} 0.$$
As the square root is continuous at $0$, $\|\varphi^*_{\mu_\tau}\|_{\mathcal{H}} \to 0$, i.e. $\varphi^*_{\mu_\tau} \to 0$ in $\mathcal{H}$ as $\tau \to \infty$. As $t_n \to \infty$, $\varphi^*_{\mu_{t_n}} \to 0$. By continuity of the inner product, $a_n \to \langle \varphi^*_\nu, 0 \rangle_{\mathcal{H}} = 0$. In [Serre2025], the same limit follows from the Cauchy–Schwarz inequality $|a_n| \le \|\varphi^*_\nu\|_{\mathcal{H}} \, \mathfrak{K}(\mu_{t_n} \mid \pi)^{1/2}$.

**Conclusion.** By uniqueness of the limit, $\|\varphi^*_\nu\|_{\mathcal{H}}^2 = 0$. By Theorem A.7 (iii) at $\nu$,
$$\mathfrak{K}(\nu \mid \pi) = \|\varphi^*_\nu\|_{\mathcal{H}}^2 = 0,$$
which concludes the proof.
```

{{SVGD.cluster_points | Lemma B.6}}

```informal SVGD.cluster_points
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Let $\mu$ be a probability measure on $\mathbb{R}^d$ such that $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let $(T_t)_{t \in \mathbb{R}}$ be the [mean-field SVGD flow](#SVGD.meanFieldFlow) from $\mu$, and let $\mu_t = (T_t)_\# \mu$. Let $(t_n)_{n \in \mathbb{N}}$ be a real sequence such that $t_n \to \infty$, and let $\nu \in \mathcal{P}(\Omega)$ such that, for every function $g : \mathbb{R}^d \to \mathbb{R}$ continuous on $\Omega$,
$$\mathbb{E}_{x \sim \mu_{t_n}}[g(x)] \xrightarrow[n \to \infty]{} \mathbb{E}_{x \sim \nu}[g(x)].$$
Then,
$$\mathfrak{K}(\nu \mid \pi) = 0.$$
```

```proof SVGD.cluster_points
Let $m$ be the [mean-field SVGD curve](#SVGD.meanFieldCurve) from $\mu$, so that $T_t(x) = X^m_{0, x}(t)$. As in the proof of Corollary B.5, $m$ is continuous, bounded by some $B \ge 0$, and solves the mean-field equation from $\mu$. Lemma B.6′ applied to $m$ concludes the proof.
```

We can now prove the main result. Under Stein-universality, the flow converges weakly to the target, for the same notion of weak convergence as in Lemma B.6. Every sequence of times $t_n \to \infty$ has a subsequence along which $\mu_{t_n}$ converges weakly, by Prokhorov's theorem. By Lemma B.6′ and Proposition 3.2, its limit is $\pi$.

{{SVGD.weak_convergence' | Theorem 3.1′}}

```informal SVGD.weak_convergence'
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Suppose that the kernel is Stein-universal on $\Omega$. Let $\mu$ be a probability measure on $\mathbb{R}^d$ such that $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let $B \ge 0$ and let $m : \mathbb{R} \to \mathcal{H}$ be a continuous curve such that $\|m(t)\|_{\mathcal{H}} \le B$ for every $t \in \mathbb{R}$. Let $\mu_t = (X^m_{0, \cdot}(t))_\# \mu$ for $t \in \mathbb{R}$, and suppose that $m(t) = \varphi^*_{\mu_t}$ for every $t \ge 0$. Then, for every function $g : \mathbb{R}^d \to \mathbb{R}$ continuous on $\Omega$,
$$\mathbb{E}_{x \sim \mu_t}[g(x)] \xrightarrow[t \to \infty]{} \mathbb{E}_{x \sim \pi}[g(x)].$$
```

```proof SVGD.weak_convergence'
Let $g : \mathbb{R}^d \to \mathbb{R}$ be continuous on $\Omega$. As shown in the proof of Corollary B.5′, $\mu \in \mathcal{P}(\Omega)$.

**Probability measures on $\Omega$.** Let $\iota : \Omega \to \mathbb{R}^d$ be the inclusion. As $\Omega$ is compact, it is measurable, and $\iota$ is a measurable embedding. Let $\mathcal{M}_1(\Omega)$ be the set of probability measures on the compact metric space $\Omega$, with the topology of weak convergence. Let $\bar\mu$ be the measure on $\Omega$ defined by $\bar\mu(A) = \mu(A)$ for every measurable $A \subseteq \Omega$. Then, $\iota_\# \bar\mu = \mu|_\Omega = \mu$, as $\mu$ is carried by $\Omega$. Moreover, $\bar\mu(\Omega) = \mu(\Omega) = 1$, so that $\bar\mu \in \mathcal{M}_1(\Omega)$.

For $t \in \mathbb{R}$, the map $x \mapsto X^m_{0, x}(t)$ restricts to a homeomorphism $S_t$ of $\Omega$, as $\Phi$ vanishes on the frontier of $\Omega$. Let $u_t = (S_t)_\# \bar\mu \in \mathcal{M}_1(\Omega)$. As $\iota \circ S_t = X^m_{0, \cdot}(t) \circ \iota$, we have that
$$\begin{aligned} \iota_\# u_t &= (\iota \circ S_t)_\# \bar\mu = \big(X^m_{0, \cdot}(t) \circ \iota\big)_\# \bar\mu \\ &= \big(X^m_{0, \cdot}(t)\big)_\# \iota_\# \bar\mu = \big(X^m_{0, \cdot}(t)\big)_\# \mu = \mu_t. \end{aligned}$$

**Weak convergence on $\Omega$.** Let $(\rho_n)_{n \in \mathbb{N}}$ be a sequence of $\mathcal{M}_1(\Omega)$ that converges to $\rho \in \mathcal{M}_1(\Omega)$. Let's show that, for every $h : \mathbb{R}^d \to \mathbb{R}$ continuous on $\Omega$,
$$\int h \, d(\iota_\# \rho_n) \xrightarrow[n \to \infty]{} \int h \, d(\iota_\# \rho).$$
As $\Omega$ is compact, $h \circ \iota$ is a bounded continuous function on $\Omega$. By the characterization of weak convergence by bounded continuous functions, $\int_\Omega h \circ \iota \, d\rho_n \to \int_\Omega h \circ \iota \, d\rho$. Moreover, $\int h \, d(\iota_\# \rho') = \int_\Omega h \circ \iota \, d\rho'$ for every $\rho' \in \mathcal{M}_1(\Omega)$, by the change of variables formula for the measurable embedding $\iota$.

**Extraction.** The filter of the limit $t \to \infty$ in $\mathbb{R}$ is countably generated. Thus, it is sufficient to show that every real sequence $(t_n)_{n \in \mathbb{N}}$ with $t_n \to \infty$ has a subsequence along which $\mathbb{E}_{x \sim \mu_t}[g(x)] \to \mathbb{E}_{x \sim \pi}[g(x)]$. Let $(t_n)_{n \in \mathbb{N}}$ be such a sequence. As $\Omega$ is compact, $\mathcal{M}_1(\Omega)$ is compact by Prokhorov's theorem. As $\Omega$ is a separable metric space, the Lévy–Prokhorov metric metrizes $\mathcal{M}_1(\Omega)$. Thus, $\mathcal{M}_1(\Omega)$ is sequentially compact, and there exist a strictly increasing $\psi : \mathbb{N} \to \mathbb{N}$ and $\bar\nu \in \mathcal{M}_1(\Omega)$ such that $u_{t_{\psi(n)}} \to \bar\nu$ as $n \to \infty$.

**The limit is $\pi$.** Let $\nu = \iota_\# \bar\nu$. It is a probability measure on $\mathbb{R}^d$, carried by $\Omega$, i.e. $\nu \in \mathcal{P}(\Omega)$. As $\psi$ is strictly increasing, $t_{\psi(n)} \to \infty$. By the two previous paragraphs, for every $h : \mathbb{R}^d \to \mathbb{R}$ continuous on $\Omega$,
$$\mathbb{E}_{x \sim \mu_{t_{\psi(n)}}}[h(x)] = \int h \, d(\iota_\# u_{t_{\psi(n)}}) \xrightarrow[n \to \infty]{} \int h \, d(\iota_\# \bar\nu) = \mathbb{E}_{x \sim \nu}[h(x)].$$
Thus, Lemma B.6′ applied to the sequence $(t_{\psi(n)})_{n \in \mathbb{N}}$ gives $\mathfrak{K}(\nu \mid \pi) = 0$. By Proposition 3.2, $\nu = \pi$. Taking $h = g$ in the last display gives
$$\mathbb{E}_{x \sim \mu_{t_{\psi(n)}}}[g(x)] \xrightarrow[n \to \infty]{} \mathbb{E}_{x \sim \pi}[g(x)],$$
which concludes the proof.
```

{{SVGD.weak_convergence | Theorem 3.1}}

```informal SVGD.weak_convergence
Let $\Omega, \pi, p, s, \Phi, K, C$ satisfy the standing assumptions, with $H_0$ a Hilbert space. Suppose that the kernel is Stein-universal on $\Omega$. Let $\mu$ be a probability measure on $\mathbb{R}^d$ such that $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let $(T_t)_{t \in \mathbb{R}}$ be the [mean-field SVGD flow](#SVGD.meanFieldFlow) from $\mu$, and let $\mu_t = (T_t)_\# \mu$. Then, for every function $g : \mathbb{R}^d \to \mathbb{R}$ continuous on $\Omega$,
$$\mathbb{E}_{x \sim \mu_t}[g(x)] \xrightarrow[t \to \infty]{} \mathbb{E}_{x \sim \pi}[g(x)].$$
```

```proof SVGD.weak_convergence
Let $m$ be the [mean-field SVGD curve](#SVGD.meanFieldCurve) from $\mu$, so that $T_t(x) = X^m_{0, x}(t)$. As in the proof of Corollary B.5, $m$ is continuous, bounded by some $B \ge 0$, and solves the mean-field equation from $\mu$. Theorem 3.1′ applied to $m$ concludes the proof.
```

## A kernel that satisfies every hypothesis

This section is not in [Serre2025]. It builds a kernel that satisfies all the hypotheses of Theorem 3.1 in dimension $d = 1$, on $\Omega = [-1, 1]$, for every admissible target.

We identify $\mathbb{R}^1$ with $\mathbb{R}$ through $y \mapsto y_0$, where $y_0$ is the only coordinate of $y$. Let $e_0 \in \mathbb{R}^1$ be the unit vector with $(e_0)_0 = 1$. Then, $y = y_0 e_0$ and $\|y\| = |y_0|$ for every $y \in \mathbb{R}^1$. The domain $[-1, 1]$ is the closed unit ball of $\mathbb{R}^1$, i.e.

$$\Omega = \{y \in \mathbb{R}^1 \mid \|y\| \le 1\} = \{y \in \mathbb{R}^1 \mid -1 \le y_0 \le 1\}.$$

Its frontier is the sphere $\{y \in \mathbb{R}^1 \mid |y_0| = 1\} = \{-e_0, e_0\}$. A score is a map $s : \mathbb{R}^1 \to (\mathbb{R}^1)^*$, and $s(x)(e_0)$ is a real number.

The kernel is

$$k(x, y) = \sum_{n \in \mathbb{N}} w_n^2\, \chi(x_0)\, R_n(x_0)\, \chi(y_0)\, R_n(y_0),$$

with the feature map $\Phi : y \mapsto (w_n\, \chi(y_0)\, R_n(y_0))_{n \in \mathbb{N}} \in \ell^2(\mathbb{N}, \mathbb{R})$, recalled below. The polynomial $R_n$ is the primitive of $t \mapsto t^n - m_n$ that vanishes at $-1$ and $1$. Thus, it is a multiple of $1 - t^2$, and $k$ is a weighted kernel $(1 - x_0^2)(1 - y_0^2)\, k_0(x, y)$ on $\Omega$ (this remark is not formalized). The cutoff $\chi$ equals $1$ on $[-2, 2]$ and has a compact support. It makes the feature map bounded and Lipschitz on $\mathbb{R}^1$, and the weights $w_n$ make the series of the feature map converge in $C^1$. As the $R_n$ vanish at $\pm 1$, so does the feature map.

Stein-universality only needs a score $s$ continuous on $\Omega$. Let $\rho$ be the projection of $\mathbb{R}$ onto $[-1, 1]$, and let $\sigma(t) = s(\rho(t) e_0)(e_0)$ for $t \in \mathbb{R}$. It is continuous on $\mathbb{R}$, although $s$ is only continuous on $\Omega$. Let $\varphi$ be continuous on $\Omega$ and $\tilde\varphi(t) = \varphi(\rho(t) e_0)$. The one-dimensional Stein equation $\sigma u + u' = \tilde\varphi - c$ has a solution with $u(-1) = u(1) = 0$. By the Weierstrass theorem, $u'$ is uniformly close to a polynomial $q = \sum_n q_n t^n$ on $[-1, 1]$. Then, $R = \sum_n q_n R_n$ is close to $u$ in $C^1([-1, 1])$. Let $f \in \mathcal{H}$ with $f_\Phi(y) = \chi(y_0) R(y_0)\, e_0$. As $\chi = 1$ near $[-1, 1]$, its Stein operator plus $c$ is $x \mapsto \sigma(x_0) R(x_0) + R'(x_0) + c$ on $\Omega$. Thus, it is uniformly close to $\varphi$ on $\Omega$.

In dimension $d \ge 2$, a kernel of this form cannot vanish on the frontier of a box and be Stein-universal. Indeed, $\xi_y = 0$ at a corner $y$ of the box (this remark is not formalized). Weighted kernels on domains with a $C^2$ frontier are not formalized either.

The cutoff is a smooth bump function.

{{SVGD.intervalCutoff | Definition}}

```informal SVGD.intervalCutoff | The cutoff function $\chi$
The cutoff $\chi : \mathbb{R} \to \mathbb{R}$ is a smooth bump function with center $0$, inner radius $2$ and outer radius $3$. It is defined by $\chi(t) = \beta_{3/2}(t/2)$, where $(\beta_R)_{R \in \mathbb{R}}$ is a family of functions $\beta_R : \mathbb{R} \to [0, 1]$ chosen once and for all with the axiom of choice. Every $\beta_R$ is even. For $R > 1$, $\beta_R = 1$ on $[-1, 1]$ and $\beta_R(t) \neq 0 \iff |t| < R$. Moreover, $(R, t) \mapsto \beta_R(t)$ is $C^\infty$ on $(1, \infty) \times \mathbb{R}$. Nothing else is known about $\beta$, so $\chi$ is not an explicit function. These properties give that $\chi$ is $C^\infty$ on $\mathbb{R}$, even, with $0 \le \chi \le 1$, and
$$\chi(t) = 1 \text{ if } |t| \le 2, \qquad \chi(t) \neq 0 \iff |t| < 3.$$
In particular, the closed support of $\chi$ is the compact set $[-3, 3]$.
```

The functions of the feature map are built from the following polynomials.

{{SVGD.intervalPoly | Definition}}

```informal SVGD.intervalPoly | The polynomials $R_n$
For $n \in \mathbb{N}$, let
$$m_n = \frac{1 - (-1)^{n+1}}{2(n+1)}.$$
The polynomial function $R_n : \mathbb{R} \to \mathbb{R}$ is defined by
$$R_n(t) = \frac{t^{n+1} - (-1)^{n+1}}{n+1} - m_n\, (t + 1).$$
```

The constant $m_n$ is the mean of $t^n$ on $[-1, 1]$ (this remark is not formalized). We show in the proofs below that $R_n(-1) = R_n(1) = 0$ and $R_n'(t) = t^n - m_n$. Thus, $R_n$ is the primitive of $t \mapsto t^n - m_n$ that vanishes at $-1$ and $1$.

The feature map is the [feature map of a sequence of functions](#SVGD.seqFeatureMap), which we recall. Let $g = (g_n)_{n \in \mathbb{N}}$ be a sequence of functions $g_n : \mathbb{R} \to \mathbb{R}$. Its [weights](#SVGD.seqWeight) are

$$w_n = \frac{2^{-n}}{1 + M_n}, \qquad M_n = \sup_{t \in \mathbb{R}} \big(|g_n(t)| + |g_n'(t)|\big),$$

where $g_n'(t) = 0$ if $g_n$ is not differentiable at $t$, and $M_n = 0$ if the supremum is infinite. For $t \in \mathbb{R}$, $\Phi_g(t) \in \ell^2(\mathbb{N}, \mathbb{R})$ is the sum of the series

$$\Phi_g(t) = \sum_{n \in \mathbb{N}} w_n\, g_n(t)\, \mathbb{1}_{\{n\}},$$

where $\mathbb{1}_{\{n\}}$ is the sequence equal to $1$ at $n$ and to $0$ elsewhere, and $\Phi_g(t) = 0$ if the series is not summable.

{{SVGD.intervalFeatureMap | Definition}}

```informal SVGD.intervalFeatureMap | A Stein-universal kernel on $[-1, 1]$
Let $\chi$ be the cutoff and $(R_n)_{n \in \mathbb{N}}$ the polynomials defined above. Let $g = (g_n)_{n \in \mathbb{N}}$ with $g_n = \chi R_n : \mathbb{R} \to \mathbb{R}$, and let $(w_n)_{n \in \mathbb{N}}$ be its weights. The feature map $\Phi : \mathbb{R}^1 \to \ell^2(\mathbb{N}, \mathbb{R})$ is defined by
$$\Phi(y) = \Phi_g(y_0) = \sum_{n \in \mathbb{N}} w_n\, \chi(y_0)\, R_n(y_0)\, \mathbb{1}_{\{n\}}.$$
Its Hilbert space is $H_0 = \ell^2(\mathbb{N}, \mathbb{R})$ and its kernel is $k(x, y) = \langle \Phi(x), \Phi(y) \rangle$.
```

No default value is involved. Every $g_n$ is $C^1$ with a compact support (see the proof of the next proposition), so $M_n$ is finite and $w_n \big(|g_n| + |g_n'|\big) \le 2^{-n}$. Hence, the series converges, $\Phi(y) = (w_n\, \chi(y_0)\, R_n(y_0))_{n \in \mathbb{N}}$, and

$$k(x, y) = \sum_{n \in \mathbb{N}} w_n^2\, \chi(x_0)\, R_n(x_0)\, \chi(y_0)\, R_n(y_0).$$

This series converges, as $w_n |\chi(t) R_n(t)| \le 2^{-n}$ for every $t \in \mathbb{R}$.

The feature map satisfies the assumptions on the kernel, with $K = C = 2$.

{{SVGD.admissibleFeatureMap_intervalFeatureMap | Proposition}}

```informal SVGD.admissibleFeatureMap_intervalFeatureMap | The kernel on $[-1, 1]$ is admissible
Let $\Omega = [-1, 1] \subseteq \mathbb{R}^1$ and let $\Phi : \mathbb{R}^1 \to \ell^2(\mathbb{N}, \mathbb{R})$ be the feature map defined above. Then, $\Phi$ satisfies the [assumptions on the kernel](#SVGD.AdmissibleFeatureMap) on $\Omega$ with $K = C = 2$. That is, $\Phi$ is $C^1$ on $\mathbb{R}^1$,
$$\forall y, z \in \mathbb{R}^1, \ \|\Phi(y) - \Phi(z)\| \le 2\, \|y - z\|, \qquad \forall y \in \mathbb{R}^1, \ \|\Phi(y)\| \le 2,$$
and $\Phi(y) = 0$ for every $y$ in the frontier of $\Omega$.
```

```proof SVGD.admissibleFeatureMap_intervalFeatureMap
We first show two claims on the functions $g_n = \chi R_n$.

**Claim 1.** For every $n \in \mathbb{N}$, $R_n(-1) = R_n(1) = 0$. We have that $R_n(-1) = \big((-1)^{n+1} - (-1)^{n+1}\big)/(n+1) - m_n \cdot 0 = 0$ and
$$R_n(1) = \frac{1 - (-1)^{n+1}}{n+1} - 2 m_n = \frac{1 - (-1)^{n+1}}{n+1} - \frac{1 - (-1)^{n+1}}{n+1} = 0.$$

**Claim 2.** For every $n \in \mathbb{N}$, $g_n$ is $C^1$ and $t \mapsto |g_n(t)| + |g_n'(t)|$ is bounded above on $\mathbb{R}$. The cutoff $\chi$ is $C^\infty$ and $R_n$ is a polynomial, so $g_n = \chi R_n$ is $C^1$. As $\chi$ has a compact support, so does $g_n$, and so does its derivative $g_n'$. Thus, $|g_n| + |g_n'|$ is continuous with a compact support, hence bounded above.

By Claim 2, the general properties of the [feature map](#SVGD.seqFeatureMap) $\Phi_g$ apply to $g = (g_n)_{n \in \mathbb{N}}$. Their proofs rely on $w_n \big(|g_n| + |g_n'|\big) \le 2^{-n}$. Thus, the terms of the series $\Phi_g = \sum_n w_n g_n \mathbb{1}_{\{n\}}$ and of the series of its derivatives are bounded by $2^{-n}$, and $\sum_n 2^{-n} = 2$. They give that $\Phi_g$ is $C^1$, by termwise differentiation. They also give that $\|\Phi_g(t)\| \le 2$ for every $t \in \mathbb{R}$, and that $\Phi_g$ is $2$-Lipschitz by the mean value inequality, as $\|D\Phi_g\| \le 2$. We have that $\Phi(y) = \Phi_g(y_0)$ for every $y \in \mathbb{R}^1$.

**Regularity.** The map $y \mapsto y_0$ is linear and continuous, hence $C^1$. Thus, $\Phi$ is $C^1$ as a composition of $C^1$ maps.

**Lipschitz constant.** For $y, z \in \mathbb{R}^1$, $|y_0 - z_0| \le \|y - z\|$, so $y \mapsto y_0$ is $1$-Lipschitz. Thus, $\Phi$ is $2 \cdot 1 = 2$-Lipschitz.

**Bound.** For $y \in \mathbb{R}^1$, $\|\Phi(y)\| = \|\Phi_g(y_0)\| \le 2$.

**Frontier.** As $1 \neq 0$, the frontier of the closed ball $\Omega$ is the sphere $\{y \in \mathbb{R}^1 \mid \|y\| = 1\} = \{y \in \mathbb{R}^1 \mid |y_0| = 1\}$. Let $y$ be in the frontier of $\Omega$. Then, $y_0 = 1$ or $y_0 = -1$. In both cases, $g_n(y_0) = \chi(y_0) R_n(y_0) = 0$ for every $n$, by Claim 1. Thus, every term of the series $\Phi_g(y_0)$ vanishes, and $\Phi(y) = \Phi_g(y_0) = 0$, which concludes the proof.
```

The kernel is Stein-universal for every score continuous on $\Omega$. The score does not need to be the score of a density, nor to be continuous outside $\Omega$.

{{SVGD.isSteinUniversal_intervalFeatureMap | Theorem}}

```informal SVGD.isSteinUniversal_intervalFeatureMap | The kernel on $[-1, 1]$ is Stein-universal
Let $\Omega = [-1, 1] \subseteq \mathbb{R}^1$, let $\Phi : \mathbb{R}^1 \to \ell^2(\mathbb{N}, \mathbb{R})$ be the feature map defined above, and let $\mathcal{H} = \ell^2(\mathbb{N}, \mathbb{R})^1$. Let $s : \mathbb{R}^1 \to (\mathbb{R}^1)^*$ be continuous on $\Omega$. Then, the kernel of $\Phi$ is Stein-universal on $\Omega$ for the score $s$ (Definition A.9), i.e. the set
$$\big\{\psi \in C(\Omega, \mathbb{R}) \;\big|\; \exists f \in \mathcal{H}, \exists c \in \mathbb{R}, \forall x \in \Omega, \ \psi(x) = \mathcal{A}_s(f_\Phi)(x) + c\big\}$$
is dense in $C(\Omega, \mathbb{R})$, for the topology of uniform convergence on $\Omega$.
```

```proof SVGD.isSteinUniversal_intervalFeatureMap
For $x \in \mathbb{R}^1$, we have that $x \in \Omega \iff x_0 \in [-1, 1]$, as $\|x\| = |x_0|$.

**Reduction to $\mathbb{R}$.** Let $\rho : \mathbb{R} \to [-1, 1]$, $\rho(t) = \max(-1, \min(1, t))$, be the projection onto $[-1, 1]$, and let $\iota : \mathbb{R} \to \mathbb{R}^1$, $\iota(t) = \rho(t)\, e_0$. Then, $\iota$ is continuous, $\iota(t) \in \Omega$ for every $t \in \mathbb{R}$, and $\iota(x_0) = x_0 e_0 = x$ for every $x \in \Omega$. Let
$$\sigma : \mathbb{R} \to \mathbb{R}, \qquad \sigma(t) = s(\iota(t))(e_0).$$
As $s$ is continuous on $\Omega$ and $\iota$ is continuous with values in $\Omega$, $\sigma$ is continuous on $\mathbb{R}$. Let $\varphi \in C(\Omega, \mathbb{R})$ and $\varepsilon > 0$. It is sufficient to find $\psi$ in the set of the statement with $\operatorname{dist}(\varphi, \psi) < \varepsilon$. Let $\tilde\varphi : \mathbb{R} \to \mathbb{R}$, $\tilde\varphi(t) = \varphi(\iota(t))$, which is continuous.

**The Stein equation.** By a lemma on first-order linear differential equations, applied to $\sigma$, $\tilde\varphi$, $a = -1$ and $b = 1$, there are $c \in \mathbb{R}$ and $u : \mathbb{R} \to \mathbb{R}$, differentiable on $\mathbb{R}$, such that $u(-1) = u(1) = 0$ and
$$\forall t \in \mathbb{R}, \quad u'(t) = \tilde\varphi(t) - c - \sigma(t)\, u(t).$$
This lemma states that such $c$ and $u$ exist for all continuous $\sigma, \tilde\varphi : \mathbb{R} \to \mathbb{R}$ and all $a, b \in \mathbb{R}$. Its proof takes the integrating factor $W(t) = \exp\big(\int_0^t \sigma\big)$, $c = \int_a^b W \tilde\varphi \big/ \int_a^b W$ and $u(t) = W(t)^{-1} \int_a^t W (\tilde\varphi - c)$. As $u$ is differentiable, $u$ and $u' = \tilde\varphi - c - \sigma u$ are continuous on $\mathbb{R}$. As $\sigma$ is continuous on the compact $[-1, 1]$, there is $S \in \mathbb{R}$ with $|\sigma(t)| \le S$ for every $t \in [-1, 1]$. Let
$$\delta = \frac{\varepsilon}{2\, (2 + 4 |S|)} > 0.$$

**Polynomial approximation.** By the Weierstrass approximation theorem, there is a polynomial $q$ such that
$$\forall t \in [-1, 1], \quad |q(t) - u'(t)| < \delta.$$
Let $N = \deg q + 1$, where $\deg 0 = 0$ by convention, so that $q(t) = \sum_{n < N} q_n t^n$, where the $q_n$ are the coefficients of $q$. Let
$$m_q = \sum_{n < N} q_n\, m_n, \qquad R(t) = \sum_{n < N} q_n\, R_n(t).$$

**Claim 3.** For every $n \in \mathbb{N}$ and $t \in \mathbb{R}$, $R_n'(t) = t^n - m_n$. The derivative of $t \mapsto (t^{n+1} - (-1)^{n+1})/(n+1)$ is $(n+1) t^n / (n+1) = t^n$, and that of $t \mapsto m_n (t + 1)$ is $m_n$.

By Claim 3, $R$ is differentiable on $\mathbb{R}$ with
$$R'(t) = \sum_{n < N} q_n (t^n - m_n) = q(t) - m_q.$$
Thus, the function $R - u$ satisfies, for every $t \in \mathbb{R}$,
$$(R - u)'(t) = \big(q(t) - u'(t)\big) - m_q.$$
We have that $R(\pm 1) - u(\pm 1) = 0$, by Claim 1 of the proof of the [Proposition above](#SVGD.admissibleFeatureMap_intervalFeatureMap) and $u(\pm 1) = 0$. The function $q - u'$ is continuous with $|q - u'| \le \delta$ on $[-1, 1]$.

**Claim 4.** Let $F, e : \mathbb{R} \to \mathbb{R}$ and $a, \delta \in \mathbb{R}$. Assume that $F$ is differentiable on $\mathbb{R}$ with $F' = e - a$, that $e$ is continuous, that $F(-1) = F(1) = 0$, and that $|e(t)| \le \delta$ for every $t \in [-1, 1]$. Then, $|a| \le \delta$. By the fundamental theorem of calculus,
$$\int_{-1}^1 e(\tau)\, d\tau - 2a = \int_{-1}^1 \big(e(\tau) - a\big)\, d\tau = F(1) - F(-1) = 0.$$
As $|e| \le \delta$ on $[-1, 1]$, $\big|\int_{-1}^1 e(\tau)\, d\tau\big| \le \delta\, |1 - (-1)| = 2\delta$. Thus, $2|a| \le 2\delta$, i.e. $|a| \le \delta$.

Claim 4, applied to $F = R - u$, $e = q - u'$ and $a = m_q$, gives that $|m_q| \le \delta$.

**An element of $\mathcal{H}$.** Let $G : \mathbb{R} \to \mathbb{R}$ be defined by
$$G(t) = \sum_{n < N} q_n\, \chi(t)\, R_n(t) = \sum_{n < N} q_n\, g_n(t).$$
By Claim 2 of the proof of the [Proposition above](#SVGD.admissibleFeatureMap_intervalFeatureMap), there is $h \in \ell^2(\mathbb{N}, \mathbb{R})$ such that $\langle h, \Phi_g(t) \rangle = G(t)$ for every $t \in \mathbb{R}$, namely $h = \sum_{n < N} (q_n / w_n) \mathbb{1}_{\{n\}}$, as $\langle \mathbb{1}_{\{n\}}, \Phi_g(t) \rangle = w_n g_n(t)$ and $w_n > 0$. Thus,
$$\forall y \in \mathbb{R}^1, \quad \langle h, \Phi(y) \rangle = \langle h, \Phi_g(y_0) \rangle = G(y_0).$$
By Claim 2, $G$ is $C^1$ as a finite sum of $C^1$ functions.

**Claim 5.** For every $t \in \mathbb{R}$ with $|t| \le 2$, $\chi(t) = 1$. This is a property of the [bump function](#SVGD.intervalCutoff) $\chi$, as $t$ lies in the closed ball of center $0$ and of radius $2$, its inner radius.

Let $t \in [-1, 1]$ and $\tau \in (t - 1, t + 1)$. Then, $|\tau| < 2$, so $\chi(\tau) = 1$ by Claim 5, and $G(\tau) = R(\tau)$. Thus, $G = R$ on a neighborhood of $t$, so that, for every $t \in [-1, 1]$,
$$G(t) = R(t), \qquad G'(t) = R'(t) = q(t) - m_q.$$

Let $f = (h) \in \mathcal{H}$, the element of $\mathcal{H} = \ell^2(\mathbb{N}, \mathbb{R})^1$ whose only component is $h$. We compute its Stein operator.

**Claim 6.** Let $H_0$ be a real inner product space, $\Psi : \mathbb{R}^1 \to H_0$, $s : \mathbb{R}^1 \to (\mathbb{R}^1)^*$, $h \in H_0$, and $G : \mathbb{R} \to \mathbb{R}$ differentiable, such that $\langle h, \Psi(y) \rangle = G(y_0)$ for every $y \in \mathbb{R}^1$. Let $f = (h) \in H_0^1$. Then, for every $x \in \mathbb{R}^1$,
$$\mathcal{A}_s(f_\Psi)(x) = s(x)(e_0)\, G(x_0) + G'(x_0).$$
We have that $f_\Psi(y) = \langle h, \Psi(y) \rangle e_0 = G(y_0)\, e_0$ for every $y \in \mathbb{R}^1$. By the chain rule, the derivative of $f_\Psi$ at $x$ is the linear map $v \mapsto G'(x_0)\, v_0\, e_0$. As the divergence on $\mathbb{R}^1$ is $\operatorname{div} f_\Psi(x) = \big(Df_\Psi(x)\, e_0\big)_0$, we have that $\operatorname{div} f_\Psi(x) = G'(x_0)$. Thus,
$$\mathcal{A}_s(f_\Psi)(x) = s(x)\big(G(x_0)\, e_0\big) + \operatorname{div} f_\Psi(x) = s(x)(e_0)\, G(x_0) + G'(x_0).$$

By Claim 6, applied to $\Psi = \Phi$, $h$ and $G$, we have that
$$\forall x \in \mathbb{R}^1, \quad \mathcal{A}_s(f_\Phi)(x) = s(x)(e_0)\, G(x_0) + G'(x_0).$$
As $s$ is continuous on $\Omega$ and $G$ is $C^1$, the map $x \mapsto \mathcal{A}_s(f_\Phi)(x) + c$ is continuous on $\Omega$. Let $\psi \in C(\Omega, \mathbb{R})$ be its restriction to $\Omega$. By definition, $\psi$ is in the set of the statement, with $f$ and $c$.

**The estimate.** As $\Omega$ is compact, the distance of $C(\Omega, \mathbb{R})$ is the uniform distance. Thus, as $\varepsilon/2 < \varepsilon$, it is sufficient to show that $|\varphi(x) - \psi(x)| \le \varepsilon/2$ for every $x \in \Omega$. We need a last estimate.

**Claim 7.** Under the assumptions of Claim 4, $|F(t)| \le 4\delta$ for every $t \in [-1, 1]$. By Claim 4, $|a| \le \delta$. By the fundamental theorem of calculus and $F(-1) = 0$, we have that $F(t) = \int_{-1}^t \big(e(\tau) - a\big)\, d\tau$. For $\tau \in (-1, t]$, $\tau \in [-1, 1]$, so $|e(\tau) - a| \le |e(\tau)| + |a| \le 2\delta$. Thus, as $0 \le 2|a| \le 2\delta$ and $|t + 1| \le 2$,
$$|F(t)| \le 2\delta\, |t - (-1)| \le 2\delta \cdot 2 = 4\delta.$$

Let $x \in \Omega$ and $t = x_0 \in [-1, 1]$. As $\iota(t) = x$, we have that $s(x)(e_0) = \sigma(t)$ and $\varphi(x) = \tilde\varphi(t)$. By the choice of $S$, $|\sigma(t)| \le S \le |S|$. By Claim 7, applied to $F = R - u$, $e = q - u'$ and $a = m_q$, $|R(t) - u(t)| \le 4\delta$. As $G(t) = R(t)$ and $G'(t) = q(t) - m_q$, we have that $\psi(x) = \sigma(t) R(t) + \big(q(t) - m_q\big) + c$. As $u'(t) = \tilde\varphi(t) - c - \sigma(t) u(t)$, we have that
$$\begin{aligned} |\varphi(x) - \psi(x)| &= \big|\tilde\varphi(t) - \big(\sigma(t) R(t) + (q(t) - m_q) + c\big)\big| \\ &= \big|-\big(q(t) - u'(t) - m_q\big) - \sigma(t) \big(R(t) - u(t)\big)\big| \\ &\le |q(t) - u'(t) - m_q| + |\sigma(t)|\, |R(t) - u(t)| \\ &\le 2\delta + |S| \cdot 4\delta \\ &= \varepsilon / 2, \end{aligned}$$
where the fourth line uses $|q(t) - u'(t) - m_q| \le |q(t) - u'(t)| + |m_q| \le 2\delta$. Thus, $\operatorname{dist}(\varphi, \psi) \le \varepsilon/2 < \varepsilon$, which concludes the proof.
```

Thus, Theorem 3.1 applies on $[-1, 1]$ with this kernel, for every admissible target. There is no hypothesis on the kernel left. As in Theorem 3.1, $\mu$ is not assumed to be carried by $\Omega$.

{{SVGD.weak_convergence_intervalFeatureMap | Corollary}}

```informal SVGD.weak_convergence_intervalFeatureMap | Weak convergence of SVGD on $[-1, 1]$
Let $\Omega = [-1, 1] \subseteq \mathbb{R}^1$ and let $\Phi : \mathbb{R}^1 \to \ell^2(\mathbb{N}, \mathbb{R})$ be the feature map defined above. Let $\pi$ be a measure on $\mathbb{R}^1$, $p : \mathbb{R}^1 \to \mathbb{R}$ and $s : \mathbb{R}^1 \to (\mathbb{R}^1)^*$. Assume that $\pi$ is an [admissible target](#SVGD.AdmissibleTarget) on $\Omega$ with density $p$ and score $s$. That is, $\pi = p \cdot \lambda|_\Omega$ is a probability measure, $p$ is measurable, continuous on $\Omega$ and positive on $\Omega$, $\log p$ has derivative $s(x)$ at every $x$ in the interior of $\Omega$, and $s$ is continuous on $\Omega$. Let $\mu$ be a probability measure on $\mathbb{R}^1$ with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$. Let $T_t$ be the [mean-field SVGD flow](#SVGD.meanFieldFlow) from $\mu$ for the kernel of $\Phi$ and the score $s$, and let $\mu_t = (T_t)_\# \mu$. Then, for every $g : \mathbb{R}^1 \to \mathbb{R}$ continuous on $\Omega$,
$$\int g \, d\mu_t \xrightarrow[t \to \infty]{} \int g \, d\pi.$$
```

```proof SVGD.weak_convergence_intervalFeatureMap
We apply Theorem 3.1 with $d = 1$, $\Omega = [-1, 1]$, $H_0 = \ell^2(\mathbb{N}, \mathbb{R})$, which is a Hilbert space, the feature map $\Phi$, and $K = C = 2$. The standing assumptions hold. Indeed, $\Omega$ is compact as a closed ball of $\mathbb{R}^1$, and $\pi$ is an admissible target by hypothesis. By the [Proposition above](#SVGD.admissibleFeatureMap_intervalFeatureMap), $\Phi$ satisfies the assumptions on the kernel with $K = C = 2$. As $\pi$ is admissible, its score $s$ is continuous on $\Omega$. Thus, the kernel of $\Phi$ is Stein-universal on $\Omega$, by the [Theorem above](#SVGD.isSteinUniversal_intervalFeatureMap). As $\mu$ is a probability measure with $\mathrm{KL}(\mu \,\|\, \pi) < \infty$ and $g$ is continuous on $\Omega$, Theorem 3.1 gives the result.
```

```informal 𝓗[d, H₀] | The space $\mathcal{H}$
Let $H_0$ be a real inner product space. Then $\mathcal{H} = H_0^d$ is the product of $d$ copies of
$H_0$, with the inner product
$$\langle f, g \rangle_{\mathcal{H}} = \sum_{i=1}^d \langle f_i, g_i \rangle_{H_0}.$$
```

```informal divergence | The divergence
Let $\mathbb{K}$ be a nontrivially normed field and $E$ a normed space over $\mathbb{K}$. For
$f : E \to E$ and $x \in E$,
$$\operatorname{div} f(x) = \operatorname{tr} Df(x),$$
where $Df(x)$ is the Fréchet derivative of $f$ at $x$, equal to $0$ if $f$ is not differentiable
at $x$, and the trace is equal to $0$ if $E$ is not finite-dimensional. If $E = \mathbb{R}^d$ and
$f$ is differentiable at $x$, then $\operatorname{div} f(x) = \sum_{i=1}^d \partial_i f_i(x)$.
```

```informal ContinuousLinearMap.traceCLM | The trace
Let $\mathbb{K}$ be a complete nontrivially normed field and $E$ a finite-dimensional Hausdorff
topological vector space over $\mathbb{K}$. Let $\mathcal{L}(E)$ be the space of continuous linear
maps from $E$ to $E$. The trace
$$\operatorname{tr} : \mathcal{L}(E) \to \mathbb{K}, \qquad A \mapsto \operatorname{tr} A$$
is a continuous linear map. Its continuity is automatic, as $\mathcal{L}(E)$ is finite-dimensional.
```

```informal ODE.globalSolution | The global solution of an ODE
Let $E$ be a real normed space and $v : \mathbb{R} \times E \to E$ a time-dependent vector field.
An integral curve of $v$ is a curve $\alpha : \mathbb{R} \to E$, differentiable at every
$t \in \mathbb{R}$, with $\alpha'(t) = v(t, \alpha(t))$. Let $t_0 \in \mathbb{R}$ and $x \in E$. If
$v$ has an integral curve $\alpha$ with $\alpha(t_0) = x$, then $\operatorname{sol}_v(t_0, x)$ is one
of them, chosen with the axiom of choice. Otherwise, $\operatorname{sol}_v(t_0, x)$ is the constant
curve $t \mapsto x$.
```

```informal SVGD.pairing | The pairing $P_h$
Let $H_0$ be a real inner product space and $h = (h_1, \dots, h_d) \in H_0^d$. The pairing of $h$ is
the continuous linear map
$$P_h : H_0 \to \mathbb{R}^d, \qquad u \mapsto \big(\langle h_1, u \rangle, \dots, \langle h_d, u \rangle\big).$$
```

```informal SVGD.toVectorField | The vector field $h_\Phi$
Let $\Phi : \mathbb{R}^d \to H_0$ and $h = (h_1, \dots, h_d) \in H_0^d$. The vector field of $h$ is
$$h_\Phi : \mathbb{R}^d \to \mathbb{R}^d, \qquad y \mapsto P_h(\Phi(y)) = \big(\langle h_1, \Phi(y) \rangle, \dots, \langle h_d, \Phi(y) \rangle\big).$$
If $H_0$ is the RKHS of the kernel $k(x, y) = \langle \Phi(x), \Phi(y) \rangle$ and
$\Phi(y) = k(\cdot, y)$, then $h_\Phi(y) = (h_1(y), \dots, h_d(y))$ by the reproducing property.
```

```informal SVGD.trajectory | The trajectories $X^m_{s, x}$
Let $\Phi : \mathbb{R}^d \to H_0$, $m : \mathbb{R} \to H_0^d$ a curve, $s \in \mathbb{R}$ and
$x \in \mathbb{R}^d$. The trajectory of $m$ through $x$ at time $s$ is
$$X^m_{s, x} = \operatorname{sol}_v(s, x), \qquad v(t, y) = m(t)_\Phi(y).$$
Thus, if $v$ has an integral curve through $x$ at time $s$, then $X^m_{s, x}$ is such a curve.
That is, $X^m_{s, x}(s) = x$ and $\frac{d}{dt} X^m_{s, x}(t) = m(t)_\Phi\big(X^m_{s, x}(t)\big)$ for
every $t \in \mathbb{R}$.
```

```informal SVGD.seqWeight | The weights $w_n$
Let $E$ be a real normed space and $(g_n)_{n \in \mathbb{N}}$ a sequence of functions
$g_n : E \to \mathbb{R}$. For $n \in \mathbb{N}$,
$$w_n = \frac{2^{-n}}{1 + M_n}, \qquad M_n = \sup_{x \in E} \big(|g_n(x)| + \|Dg_n(x)\|\big),$$
where $Dg_n(x) = 0$ if $g_n$ is not differentiable at $x$, and $M_n = 0$ if the supremum is infinite.
```

```informal SVGD.seqFeatureMap | The feature map of a sequence of functions
Let $E$ be a real normed space, $(g_n)_{n \in \mathbb{N}}$ a sequence of functions
$g_n : E \to \mathbb{R}$ and $(w_n)_{n \in \mathbb{N}}$ their [weights](#SVGD.seqWeight), defined above. For $x \in E$,
$$\Phi_g(x) = \big(w_n\, g_n(x)\big)_{n \in \mathbb{N}} \in \ell^2(\mathbb{N}, \mathbb{R})$$
if this sequence is square-summable, and $\Phi_g(x) = 0$ otherwise. It is square-summable if every
$g_n$ is bounded with a bounded derivative, as then $|w_n\, g_n(x)| \le 2^{-n}$.
```
