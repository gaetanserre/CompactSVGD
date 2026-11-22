# SBS — a Mathlib-style formalization of Stein Boltzmann Sampling on a compact domain

Lean 4 formalization of the theory of *Stein Boltzmann Sampling* (Serré, Kalogeratos, Vayatis,
AISTATS 2025), i.e. the mean-field analysis of SVGD on a compact set `Ω ⊆ ℝᵈ`. The numbering is the
one of `main_v2.tex`. The code is written as if it were to be merged into Mathlib: general
statements, Mathlib namespaces and naming conventions, one file per object, module docstrings,
no `sorry`, and both Mathlib linters (`lake exe runLinter SBS`, `lake exe lint-style SBS`) pass.

```
lake exe cache get
lake build
```

The project depends on Mathlib and on [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
(Lean `v4.37.0-rc1`). Mathlib is pinned to the commit of Tau Ceti's manifest; bump both together.
Tau Ceti is used in two places: the divergence theorem on balls
(`TauCeti.setIntegral_ball_trace_fderiv`, in `DivergenceTheorem/Ball.lean`) and Schauder's
fixed-point theorem (`TauCeti.schauderFixedPoint_closedConvex_continuousOn`, in
`SVGD/MeanField.lean`). `lake build` compiles the Tau Ceti modules it needs from source, in about a
minute. Every other file depends on Mathlib only.

## Contents

| File | Content |
|---|---|
| `SBS/Analysis/Normed/Module/Trace.lean` | `ContinuousLinearMap.trace`: the trace as a continuous linear form |
| `SBS/Analysis/Calculus/Divergence.lean` | `divergence 𝕜 f x := trace (fderiv 𝕜 f x)`, coordinates, linearity, product rule, change of variables, regularity |
| `SBS/MeasureTheory/Integral/DivergenceTheorem/WholeSpace.lean` | `∫ div f = 0` on the whole space, compact support and `tsupport ⊆ s` versions |
| `SBS/MeasureTheory/Integral/DivergenceTheorem/Box.lean` | `boxFlux a b f = ∮_{∂[a,b]} f · n dS` and `∫_{[a,b]} div f = boxFlux a b f` |
| `SBS/MeasureTheory/Integral/DivergenceTheorem/Ball.lean` | `ballFlux μ c R f = ∮_{sphere c R} f · n dS` and `∫_{ball c R} div f = ballFlux μ c R f` (Tau Ceti) |
| `SBS/MeasureTheory/Measure/Lebesgue/EqHaar.lean` | `ball x r =ᵐ[μ] closedBall x r` for an additive Haar measure |
| `SBS/Probability/Stein/Operator.lean` | `steinOperator s φ x = s x (φ x) + div φ x`, key identity `p * 𝒜_s φ = div (p • φ)` |
| `SBS/Probability/Stein/Class.lean` | `steinClass μ p : Submodule ℝ (E → E)` and sufficient conditions |
| `SBS/Probability/Stein/Box.lean` | on a box, Stein class ⟺ zero boundary flux (the paper's Definition A.2) |
| `SBS/Probability/Stein/Ball.lean` | on a ball, open or closed, Stein class ⟺ zero flux through the sphere |
| `SBS/Probability/Stein/Identity.lean` | **Lemma A.3** (Stein's identity) and its converse |
| `SBS/Analysis/ODE/Global.lean` | global solutions for bounded Lipschitz fields; invariance of a closed set whose frontier consists of equilibria |
| `SBS/Topology/Order/Gluing.lean` | gluing continuous functions along the intervals `[n, n + 1]` |
| `SBS/Probability/SVGD/Basic.lean` | `toVectorField Φ h`, `ξₓ = steinFeature Φ s x`, `φ*_ν = direction Φ s ν`; `⟪h, ξₓ⟫ = 𝒜_s h (x)` |
| `SBS/Probability/SVGD/Regularity.lean` | Lemma A.6: `ξ` continuous, bounded, uniformly continuous on `Ω`; `φ*_ν` lies in the compact `closedConvexHull (ξ '' Ω)` |
| `SBS/Probability/SVGD/Trajectory.lean` | trajectories of the vector field of a curve `m : ℝ → 𝓗`: existence, uniqueness, flow property, invariance of `Ω`, Grönwall estimates |
| `SBS/Probability/SVGD/MeanField.lean` | `AdmissibleFeatureMap`; McKean–Vlasov equation on `[a, b]` by Schauder's theorem |
| `SBS/Probability/SVGD/Flow.lean` | **the mean-field SVGD flow on `[0, ∞)`** (`SVGD.exists_flow`) |

## Lemma A.3 (Stein's identity)

> **Paper.** Let `μ ∈ 𝒫₂(Ω)` (density in `H¹(Ω)` with support `Ω`, `Ω` smooth) and let `φ ∈ 𝒮(μ)`,
> i.e. `φ ∈ H¹(Ω)` and `∮_{∂Ω} μ φ · n dS = 0`. Then `E_μ[𝒜_μ φ] = 0`.

**Lean** (`ProbabilityTheory.integral_steinOperator_eq_zero`).

```lean
theorem integral_steinOperator_eq_zero
    (hp : AEMeasurable p μ) (hp₀ : 0 ≤ᵐ[μ] p)
    (hs : ∀ᵐ x ∂μ, HasFDerivAt p (p x • s x) x) (hφ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x)
    (hφS : φ ∈ steinClass μ p) :
    ∫ x, steinOperator s φ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (p x)) = 0
```

The Lean statement is more general than the paper on every axis.

| Paper | Lean |
|---|---|
| `ℝᵈ` | any finite-dimensional real normed space `E` |
| Lebesgue measure on a smooth `Ω` | any measure `μ` (a domain is `volume.restrict Ω`, no regularity of `∂Ω`) |
| `μ` probability measure | `μ.withDensity p` any measure |
| density in `H¹`, `supp = Ω` | `p ≥ 0` a.e., a.e. differentiable, may vanish |
| score `∇ log μ` | any score `s` with `Dp = p • s` a.e. (`∇ log p` is one, see `integral_steinOperator_fderiv_log_eq_zero`) |
| `φ ∈ H¹`, `∮ μ φ · n = 0` | `φ` a.e. differentiable, `φ ∈ steinClass μ p` |

The Stein class is defined by the Gauss–Green form of the boundary condition:
`p • φ` is a.e. differentiable, `div (p • φ)` is integrable and `∫ div (p • φ) dμ = 0`. With a regular
boundary, the divergence theorem turns this integral into `∮_{∂Ω} p φ · n dS`. This definition is
the weakest possible one: `mem_steinClass_iff_integral_steinOperator_eq_zero` shows that the Stein
class is exactly the set of fields that satisfy Stein's identity. The geometric content is in the
sufficient conditions:

* whole space: `p • φ` differentiable, integrable, with integrable derivative
  (`mem_steinClass_of_integrable`);
* `tsupport (p • φ) ⊆ Ω` (`mem_steinClass_restrict_of_tsupport_subset`,
  `mem_steinClass_restrict_of_hasCompactSupport`);
* `Ω = [a, b]` a box: Stein class ⟺ `∮_{∂[a,b]} p φ · n dS = 0` (`mem_steinClass_Icc_iff`). This is
  the paper's definition, on the domains where SBS is run.
* `Ω` a ball, open or closed, in any finite-dimensional inner product space with any additive Haar
  measure: Stein class ⟺ `∮_{sphere c R} p φ · n dS = 0` (`mem_steinClass_ball_iff`,
  `mem_steinClass_closedBall_iff`).

Not covered: Sobolev regularity. For `d ≥ 2`, an `H¹` function need not be differentiable almost
everywhere, so the statement uses Fréchet derivatives. This is enough for SBS, where `π` and every
field of `𝓗` are `C¹`.

## Part 1: the mean-field SVGD flow

```lean
theorem SVGD.exists_flow (hΦ : AdmissibleFeatureMap Φ Ω K C) (hΩ : IsCompact Ω)
    (hs : ContinuousOn s Ω) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    ∃ T : ℝ → E → E, (∀ x, T 0 x = x) ∧
      (∀ t, 0 ≤ t → ∃ e : Ω ≃ₜ Ω, ∀ x : Ω, (e x : E) = T t x) ∧
      ∀ x, ∀ t, 0 ≤ t →
        HasDerivAt (T · x) (toVectorField Φ (direction Φ s (μ.map (T t))) (T t x)) t
```

This is the flow that Theorem 3.1 assumes: `∂ₜ Tₜ(x) = φ*_{μₜ}(Tₜ(x))`, `T₀ = id`, `μₜ = (Tₜ)#μ`,
and each `Tₜ` restricts to a homeomorphism of `Ω`. The hypotheses are split as follows.

| On | Hypothesis | Role |
|---|---|---|
| the target `π` | its score `s` is **continuous on `Ω`** (e.g. `π ∝ e^{-κ f}` with `f ∈ C¹`) | `ξ` continuous, hence bounded and uniformly continuous on `Ω` |
| the domain `Ω` | **compact** | `ξ(Ω)` and its closed convex hull compact; Arzelà–Ascoli |
| the initial law `μ` | probability measure concentrated on `Ω` | no density needed |
| the kernel `Φ` | `C¹`, Lipschitz, bounded, `Φ = 0` on `frontier Ω` | trajectories exist globally and stay in `Ω` |

No Lipschitz condition on the score, no regularity of `∂Ω`, no density for `μ`. The price is
uniqueness: the McKean–Vlasov equation is solved by Schauder's fixed-point theorem on each
`[n, n + 1]`, in the Banach space of bounded continuous curves `[n, n + 1] → 𝓗`, and the pieces are
concatenated. The conditions on `Φ` only matter near `Ω`, so they can be met by modifying `Φ` away
from `Ω`.

## Roadmap for the full formalization

The theory has two parts, linked by Theorem A.11.

1. **Construction of the flow.** Existence of `(Tₜ)_{t ≥ 0}` with `∂ₜ Tₜ(x) = φ*_{μₜ}(Tₜ(x))`,
   `μₜ = (Tₜ)#μ₀` and `Tₜ(Ω) = Ω`. The paper assumes this flow (hypothesis of Theorem 3.1).
2. **Bridge, Theorem A.11.** `∂ₜ KL(μₜ ‖ π) = -𝔎(μₜ | π)`.
3. **Analysis of the measure flow.** Barbalat, cluster points, Proposition 3.2, Theorem 3.1. This
   part is already formalized in the paper's repository, with Theorem A.11 as a hypothesis.

### Proposed hypotheses

| | Hypothesis | Why |
|---|---|---|
| H0 | `Ω ⊆ ℝᵈ` compact, `λ(Ω) > 0` | no smoothness or connectedness of `Ω` is needed |
| H1 | `π ∝ e^{-V} 𝟙_Ω` with `V ∈ C¹(ℝᵈ)` (`V = κ f`) | score `-DV` continuous |
| H2 | `Φ : ℝᵈ → 𝓗₀` of class `C¹`, `k(x, y) = ⟪Φ x, Φ y⟫` | `y ↦ φ*_ν(y)` is `C¹`, so the flow is `C¹` |
| H3 | `Φ = 0` on `∂Ω` | `φ*_ν = 0` on `∂Ω` for every `ν`, so `Ω` and its interior are invariant |
| H4 | dropped | Part 1 uses Schauder's theorem instead of Picard–Lindelöf, at the cost of uniqueness |
| H5 | `KL(μ₀ ‖ π) < ∞` | replaces `𝒫₂(Ω)`: no `H¹` density, no full support |
| H6 | `k` Stein-universal (Definition A.9) | Proposition 3.2 |

Comments.

* The paper's hypotheses are too weak mainly because of H3. With a kernel that does not vanish on
  `∂Ω` (e.g. the RBF kernel), the repulsive term `∇ₓ k` makes `φ*_μ` point outward at boundary
  points in general. Then the flow leaves `Ω`, and the hypotheses of Theorem 3.1 cannot be met.
  Definition A.4 (`k(·, x) ∈ 𝒮(μ) ∩ 𝒮(π)` for every `μ ∈ 𝒫₂(Ω)`) forces `k(·, x) = 0` on `∂Ω` as
  soon as `𝒫₂(Ω)` contains densities with arbitrary boundary values. H3 is compatible with H6 if `k`
  vanishes at order exactly one on `∂Ω` (weighted kernels `k(x, y) = w(x) w(y) k₀(x, y)`).
* H4 (`DV`, `DΦ` Lipschitz) would give uniqueness of the flow by Picard–Lindelöf. It is not needed:
  existence holds with a continuous score, and Theorem 3.1 holds for every solution.
* **Theorem A.11 does not need the transport equation (A.10).** In Lagrangian coordinates,
  `KL(μₜ ‖ π) = ∫ log p₀ - log det DTₜ - log π ∘ Tₜ dμ₀`, Liouville's formula
  `∂ₜ log det DTₜ = (div φ*_{μₜ}) ∘ Tₜ` and the chain rule give
  `∂ₜ KL(μₜ ‖ π) = -∫ 𝒜_π φ*_{μₜ} dμₜ = -‖φ*_{μₜ}‖²_𝓗`. This needs H5 only: no integration by parts,
  no Stein identity with respect to `μₜ`, no regularity of the densities of `μₜ`, no smooth `∂Ω`.
* **No stochastic calculus is needed.** The mean-field SVGD dynamics is a deterministic ODE. Its PDE
  is a first-order continuity equation (no diffusion term, it is not a Fokker–Planck equation), which
  follows from the chain rule. The limit `N → ∞` of Theorem 3.4 is a deterministic stability
  estimate (Dobrushin) plus the law of large numbers for the initial sample.
* Lemma A.3 is only used for `𝔎(π | π) = 0`, which Theorem 3.1 does not use. It also follows from
  Theorem A.11 and `KL ≥ 0` at `μ₀ = π`.

### Next steps

1. ~~Part 1: existence of the mean-field flow~~ (`SVGD.exists_flow`).
2. Theorem A.11 in Lagrangian coordinates: `C¹` dependence of `Tₜ` on `x`, Liouville's formula
   `∂ₜ det DTₜ = (div φ*_{μₜ}) ∘ Tₜ · det DTₜ`, change of variables, `klDiv`.
3. Port Part 2 from the paper's repository on top of `SVGD.exists_flow`, with Theorem A.11 proved
   instead of assumed.
4. Stein class criterion for fields vanishing on `∂Ω`, for an arbitrary compact `Ω`.
