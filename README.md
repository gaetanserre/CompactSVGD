# SBS — a formalization of Stein Variational Gradient Descent on a compact domain

Lean 4 formalization of the mean-field theory of Stein Variational Gradient Descent (SVGD) on a
compact set `Ω ⊆ ℝᵈ`, following the theoretical part of *Stein Boltzmann Sampling* (Serré,
Kalogeratos, Vayatis, AISTATS 2025). The numbering is the one of `main_v2.tex`. The code is
written as if it were to be merged into Mathlib: general statements, Mathlib namespaces and
naming conventions, one file per object, module docstrings, no `sorry`, and both Mathlib linters
(`lake exe runLinter SBS`, `lake exe lint-style SBS`) pass.

```
lake exe cache get
lake build
```

The project depends on Mathlib and on [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
(Lean `v4.37.0-rc1`). Mathlib is pinned to the commit of Tau Ceti's manifest; bump both together.
Tau Ceti provides:

* the divergence theorem on balls (`TauCeti.setIntegral_ball_trace_fderiv`, in
  `DivergenceTheorem/Ball.lean`);
* Schauder's fixed-point theorem (`TauCeti.schauderFixedPoint_closedConvex_continuousOn`, in
  `SVGD/MeanField.lean`);
* the smoothness of the determinant and Jacobi's formula (`ContinuousLinearMap.contDiff_det`,
  `Matrix.hasDerivAt_det_one_add_smul`, in `FDeriv/DetIdAddSMul.lean` and
  `Stein/FirstVariation.lean`), and the measurability of Jacobian determinants
  (`TauCeti.measurable_det_fderiv`);
* the global solutions of nonautonomous Lipschitz ODEs (`ODE.nonautonomousSolution`, in
  `ODE/FlowHomeomorph.lean` and `ODE/FlowJacobian.lean`);
* the invariance of the Kullback–Leibler divergence under measurable equivalences
  (`MeasureTheory.Measure.klDiv_map_measurableEquiv`, in `KullbackLeibler/Reweighting.lean`).

`lake build` compiles the Tau Ceti modules it needs from source, in about a minute.

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
| `SBS/Analysis/ODE/Global.lean` | global solutions for bounded Lipschitz fields; trajectories through equilibria are constant; invariance of a closed set whose frontier consists of equilibria, and of its interior |
| `SBS/Topology/Order/Gluing.lean` | gluing continuous functions along the intervals `[n, n + 1]` |
| `SBS/Probability/SVGD/Basic.lean` | `toVectorField Φ h`, `ξₓ = steinFeature Φ s x`, `φ*_ν = direction Φ s ν`; `⟪h, ξₓ⟫ = 𝒜_s h (x)` |
| `SBS/Probability/SVGD/Regularity.lean` | Lemma A.6: `ξ` continuous, bounded, uniformly continuous on `Ω`; `φ*_ν` lies in the compact `closedConvexHull (ξ '' Ω)` |
| `SBS/Probability/SVGD/Trajectory.lean` | trajectories of the vector field of a curve `m : ℝ → 𝓗`: existence, uniqueness, flow property, time-`t` maps are homeomorphisms of `ℝᵈ`, invariance of `Ω`, Grönwall estimates |
| `SBS/Probability/SVGD/MeanField.lean` | `AdmissibleFeatureMap`; McKean–Vlasov equation on `[a, b]` by Schauder's theorem |
| `SBS/Probability/SVGD/Flow.lean` | **the mean-field SVGD flow on `[0, ∞)`** (`SVGD.exists_flow`) |
| `SBS/Analysis/InnerProductSpace/UnitBall.lean` | `v / ‖v‖` is the unique maximizer of `⟪·, v⟫` on the unit ball; `⨆_{‖h‖ ≤ 1} ⟪h, v⟫² = ‖v‖²` |
| `SBS/Probability/SVGD/SteinDiscrepancy.lean` | **Theorem A.7**: `E_ν[𝒜_s h] = ⟪h, φ*_ν⟫`, `𝔎(ν) = ‖φ*_ν‖²`, `φ*_ν / ‖φ*_ν‖` is the unique steepest direction |
| `SBS/Analysis/Normed/PerturbationOfIdentity.lean` | `x ↦ x + ε • v x` is a homeomorphism for `|ε| Lip(v) < 1`, mapping `Ω` onto `Ω` when `v = 0` on `frontier Ω` |
| `SBS/Analysis/Calculus/FDeriv/DetIdAddSMul.lean` | Jacobi's formula: `t ↦ det (id + t • A)` has derivative `trace A` at `0` (Tau Ceti) |
| `SBS/InformationTheory/KullbackLeibler/Reweighting.lean` | `KL(e#μ ‖ ν) = KL(μ ‖ e⁻¹#ν)` for measurable equivalences; KL against a reweighted reference measure, and its finiteness |
| `SBS/MeasureTheory/Function/Jacobian.lean` | `e⁻¹#(p · vol\|_Ω)` has density `(p ∘ e) · det De / p` with respect to `p · vol\|_Ω` |
| `SBS/InformationTheory/KullbackLeibler/Transport.lean` | `KL(e#μ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ e - log p + log det De) dμ` for a measurable equivalence `e` mapping `Ω` onto `Ω`; `KL(e#μ ‖ π) < ∞` |
| `SBS/Probability/Stein/FirstVariation.lean` | first variation of the KL divergence: `∂ε KL((I + ε v)#μ ‖ π)|_{ε=0} = -E_μ[𝒜_s v]` |
| `SBS/Probability/SVGD/SteepestDescent.lean` | **Theorem A.8**: `φ*_μ / ‖φ*_μ‖` is the unique steepest descent direction of `KL(· ‖ π)` in the unit ball of `𝓗`, and the first variation along `φ*_μ` is `-𝔎(μ)` |
| `SBS/Analysis/ODE/InitialCondition.lean` | differentiability of a flow with respect to the initial condition, in both time directions: `D(α · t) = J t`, where `J` solves the variational equation |
| `SBS/Analysis/ODE/Liouville.lean` | Liouville's formula `(det J)' = trace A · det J` for `J' = A ∘ J`; positivity and log-Lipschitz bound for solutions of `f' = c f` |
| `SBS/Analysis/ODE/FlowHomeomorph.lean` | the time-`t` map of a uniformly Lipschitz field is a homeomorphism, mapping `Ω` onto `Ω` when the field vanishes on `frontier Ω` (Tau Ceti) |
| `SBS/Analysis/ODE/FlowJacobian.lean` | the Jacobian of a flow: variational equation, `∂ₜ det D(α · t) = div vₜ ∘ (α · t) · det D(α · t)`, `det > 0`, `|log det| ≤ ‖trace‖ K |t|` |
| `SBS/Probability/Stein/Dissipation.lean` | dissipation of the KL divergence along any flow: `∂ₜ KL(μₜ ‖ π) = -E_{μₜ}[𝒜_s vₜ]`, and `KL(μₜ ‖ π) < ∞` |
| `SBS/Probability/SVGD/Dissipation.lean` | **Theorem A.11**: `∂ₜ KL(μₜ ‖ π) = -𝔎(μₜ)` along the mean-field SVGD flow, `KL(μₜ ‖ π) = KL(μ ‖ π) - ∫₀ᵗ 𝔎(μ_τ) dτ`, monotonicity |

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

## Theorems A.7 and A.8: why SVGD moves along `φ*`

For `h ∈ 𝓗`, write `𝒜_s h` for the Stein operator applied to the vector field of `h`.

* **A.7** (`SVGD/SteinDiscrepancy.lean`). `E_ν[𝒜_s h] = ⟪h, φ*_ν⟫`, so the kernelized Stein
  discrepancy `𝔎(ν) = sup_{‖h‖ ≤ 1} E_ν[𝒜_s h]²` equals `‖φ*_ν‖²`, and `φ*_ν / ‖φ*_ν‖` is the unique
  direction of the unit ball along which Stein's identity is most violated (when `φ*_ν ≠ 0`).
* **A.8** (`SVGD/SteepestDescent.lean`). The first variation
  `klFirstVariation Φ π μ h = ∂ε KL((I + ε h)#μ ‖ π)|_{ε=0}` equals `-⟪h, φ*_μ⟫`. Hence
  `φ*_μ / ‖φ*_μ‖` is the unique minimizer on the unit ball, with minimum `-‖φ*_μ‖`, and the first
  variation along `φ*_μ` is `-𝔎(μ)`.

The hypotheses of A.8 are those of Part 1 together with a density for the target:
`π = p · λ|_Ω` with `p` continuous and positive on `Ω`, `log p` differentiable in the interior of `Ω`
with derivative `s`, and `KL(μ ‖ π) < ∞`. No density is needed for `μ`, and no regularity of `∂Ω`.
The proof transports `π` backwards instead of `μ` forwards: `KL(Tε#μ ‖ π) = KL(μ ‖ Tε⁻¹#π)`, and
`Tε⁻¹#π` has density `(p ∘ Tε) · det DTε / p` with respect to `π` by the change of variables formula.
This transport formula holds for any measurable equivalence `e` that is differentiable on `Ω`, maps
`Ω` onto `Ω`, and has a positive Jacobian determinant with `μ`-integrable logarithm
(`InformationTheory.toReal_klDiv_map_eq`). The same formula gives Theorem A.11.

## Theorem A.11: the KL divergence decreases along SVGD

```lean
theorem SVGD.hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction
    (hΦ : AdmissibleFeatureMap Φ Ω K C) (hΩ : IsCompact Ω)
    (hπ : π = (volume.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x))
    (hp : Measurable p) (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x)
    (hμ : klDiv μ π ≠ ∞) (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ Real.log (p y)) (s x) x)
    (hsc : ContinuousOn s Ω)
    (hmφ : ∀ t, 0 ≤ t → m t = direction Φ s (μ.map (trajectory Φ m 0 · t)))
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal)
      (-kernelSteinDiscrepancy Φ s (μ.map (trajectory Φ m 0 · t))) t
```

The curve `m` is the one given by `SVGD.exists_meanField`, so `μₜ = (Tₜ)#μ` with
`Tₜ = trajectory Φ m 0 · t` is the mean-field SVGD flow of Part 1. The hypotheses are those of A.8:
nothing is assumed on `μₜ`. The file also proves that `KL(μₜ ‖ π)` stays finite
(`SVGD.klDiv_map_trajectory_ne_top`), the integrated form
`KL(μₜ ‖ π) = KL(μ ‖ π) - ∫₀ᵗ 𝔎(μ_τ) dτ` (`SVGD.toReal_klDiv_map_trajectory_eq`), that
`t ↦ KL(μₜ ‖ π)` is antitone on `[0, ∞)`, and that `∫₀ᵗ 𝔎(μ_τ) dτ ≤ KL(μ ‖ π)`
(`SVGD.integral_kernelSteinDiscrepancy_le`), with `τ ↦ 𝔎(μ_τ)` integrable on `[0, t]`. The last
bound is what the analysis of Part 2 needs.

The proof is Lagrangian and does not use Theorem A.10 (the transport equation).

1. The flow maps `Tₜ` are homeomorphisms of `ℝᵈ` mapping `Ω` onto `Ω`, for every `t ∈ ℝ`
   (`ODE.isHomeomorph_flow`, `ODE.image_flow_eq`).
2. `x ↦ Tₜ x` is differentiable and `DTₜ x` solves the variational equation
   `∂ₜ DTₜ x = Dvₜ(Tₜ x) ∘ DTₜ x` (`ODE.hasDerivAt_fderiv_flow`). By Liouville's formula,
   `∂ₜ det DTₜ x = div vₜ (Tₜ x) · det DTₜ x`, so `det DTₜ x > 0` and `|log det DTₜ x| ≤ ‖trace‖ K |t|`.
3. The transport formula gives
   `KL(μₜ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ Tₜ - log p + log det DTₜ) dμ` at every time.
4. The time derivative of the integrand is `𝒜_s vₜ ∘ Tₜ`. Trajectories through `frontier Ω` are
   constant and those through `interior Ω` stay in `interior Ω`, which is where `log p` is
   differentiable. Differentiation under the integral sign is dominated by
   `sup ‖s‖ · sup ‖v‖ + ‖trace‖ K`. Thus `∂ₜ KL(μₜ ‖ π) = -E_{μₜ}[𝒜_s vₜ]`
   (`InformationTheory.hasDerivAt_toReal_klDiv_map_flow`, for any flow).
5. By A.7, `E_{μₜ}[𝒜_s vₜ] = ⟪m t, φ*_{μₜ}⟫`, which is `‖φ*_{μₜ}‖² = 𝔎(μₜ)` when `m t = φ*_{μₜ}`.

## Roadmap for the full formalization

The theory has two parts, linked by Theorem A.11.

1. **Construction of the flow.** Existence of `(Tₜ)_{t ≥ 0}` with `∂ₜ Tₜ(x) = φ*_{μₜ}(Tₜ(x))`,
   `μₜ = (Tₜ)#μ₀` and `Tₜ(Ω) = Ω`. The paper assumes this flow (hypothesis of Theorem 3.1).
2. **Bridge, Theorem A.11.** `∂ₜ KL(μₜ ‖ π) = -𝔎(μₜ | π)`. Formalized
   (`SVGD.hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction`).
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
   ~~Theorems A.7 and A.8~~ (`SVGD.kernelSteinDiscrepancy_eq`, `SVGD.isMinOn_klFirstVariation`).
2. ~~Theorem A.11 in Lagrangian coordinates~~
   (`SVGD.hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction`, `SVGD.toReal_klDiv_map_trajectory_eq`).
3. Port Part 2 from the paper's repository on top of `SVGD.exists_flow`, with Theorem A.11 proved
   instead of assumed.
4. Stein class criterion for fields vanishing on `∂Ω`, for an arbitrary compact `Ω`.
