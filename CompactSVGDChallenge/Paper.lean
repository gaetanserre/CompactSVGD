/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Mean-field SVGD on a compact domain

This file formalizes the theory of SVGD developed in the appendix of the revised version of
*Stein Boltzmann Sampling* (G. Serré, A. Kalogeratos, N. Vayatis). It follows the appendix: every
definition and result of the paper appears here, in the paper's order, with its proof. The only
additions are the construction of the mean-field SVGD flow, which the AISTATS 2025 version
[Serre2025] assumes, the primed versions of the results along the flow, stated for every solution
of the mean-field equation, a Stein-universal kernel on `[-1, 1]` in the last section, and private
technical lemmas. The numbering is that of [Serre2025].

The general mathematics (divergence, global solutions of ODEs, Barbalat's lemma, Kullback–Leibler
divergence along a flow, ...) lives in `CompactSVGD/ForMathlib/`, and the vector fields of the
feature map and their trajectories in `CompactSVGD/FeatureMap/`. Their definitions are all gathered
in `CompactSVGD/Definitions.lean`; those used in the statements are recalled here by `example`s
proved by `rfl`.

The results on the Boltzmann distribution (Definition 2.1, Properties A.1, Theorems B.1 and B.2)
and the asymptotic convergence of SBS (Theorem 3.3) are not formalized.

## How to read this file

* **Appendix A.2.1, the standing assumptions.** `SVGD.StandingAssumptions Ω π p s Φ K C` fixes the
  space (`Ω` compact), the target (`π = p · λ|_Ω`, with a continuous score `s = ∇ log p`) and the
  kernel (`k(x, y) = ⟪Φ x, Φ y⟫` with an admissible feature map `Φ`). Most results take this single
  hypothesis `hS`, plus the additional hypotheses of each result, written explicitly.
* **Appendix A.2.2, Stein's method.** The Stein operator, the Stein class (Definition A.2) and
  Stein's identity (Lemma A.3).
* **Appendix A.2.3, the kernelized Stein discrepancy.** The product RKHS (Definition A.4), `ξ`,
  `φ*`, the KSD (Definition A.5), Lemma A.6, Theorems A.7 and A.8, Stein-universal kernels
  (Definition A.9), the existence of the mean-field SVGD flow, and the time derivative of the
  Kullback–Leibler divergence along it (Theorem A.11).
* **Appendix B, proofs.** Proposition 3.2, then Lemma B.4, Corollary B.5, Lemma B.6 and
  Theorem 3.1, in the order of the proof of Theorem 3.1.
* **A Stein-universal kernel on `[-1, 1]`** (not in [Serre2025]). An explicit kernel that satisfies
  all the hypotheses of Theorem 3.1 in dimension `1`, for every admissible target.

## Main statements

* `ProbabilityTheory.stein_identity`: Lemma A.3.
* `SVGD.steepest_trajectory_ksd`: Theorem A.7, `𝔎(μ ∣ π) = ‖φ*_μ‖²`.
* `SVGD.kl_steepest_descent_direction`: Theorem A.8.
* `SVGD.exists_meanField`, `SVGD.hasDerivAt_meanFieldFlow`: existence of the mean-field SVGD
  flow.
* `SVGD.time_derivative_kl`: Theorem A.11.
* `SVGD.ksd_valid_discrepancy`: Proposition 3.2.
* `SVGD.weak_convergence`: **Theorem 3.1**.
* `SVGD.admissibleFeatureMap_intervalFeatureMap`, `SVGD.isSteinUniversal_intervalFeatureMap`: the
  kernel of `SVGD.intervalFeatureMap` satisfies the hypotheses of Theorem 3.1 on `[-1, 1]`.
* `SVGD.weak_convergence_intervalFeatureMap`: Theorem 3.1 on `[-1, 1]` with this kernel.

## Notation

| Paper | Lean |
|---|---|
| `ℝᵈ`, `λ` | `EuclideanSpace ℝ (Fin d)`, `volume` |
| `μ ∈ 𝒫(Ω)` | `[IsProbabilityMeasure μ]` and `∀ᵐ x ∂μ, x ∈ Ω` |
| `π`, its density, `∇ log π` | `π`, `p`, `s` |
| `k(·, x)`, `H₀`, `𝓗 = H₀ᵈ` | `Φ x`, `H₀`, `𝓗[d, H₀]` |
| `f(y)`, for `f ∈ 𝓗` | `toVectorField Φ f y` |
| `𝒜_π f (x)` | `ProbabilityTheory.steinOperator s (toVectorField Φ f) x` |
| `𝒮(μ)` | `ProbabilityTheory.steinClass` |
| `ξ_x`, `φ*_μ` | `SVGD.steinFeature Φ s x`, `SVGD.direction Φ s μ` |
| `𝔎(μ ∣ π)` | `𝔎[Φ, s] μ`, i.e. `SVGD.kernelSteinDiscrepancy Φ s μ` |
| `∇_ε KL(T_ε(f)#μ ‖ π)∣_{ε=0}` | `SVGD.klFirstVariation Φ π μ f` |
| `m t = φ*_{μ_t}` for `t ≥ 0` (mean-field equation) | `SVGD.IsMeanFieldCurve Φ s μ m` |
| `T_t(x)`, `μ_t = (T_t)#μ` | `SVGD.meanFieldFlow Φ s μ t x`, `μ.map (SVGD.meanFieldFlow Φ s μ t)` |

## Implementation notes

The mean-field SVGD flow `(T_t)_{t ≥ 0}` of Theorems A.11 and 3.1 is described by the curve
`m : ℝ → 𝓗` of its update directions: `m` is continuous and bounded, its trajectories are
`T_t = trajectory Φ m 0 · t`, and the mean-field equation is `m t = φ*_{μ_t}` for `t ≥ 0`, where
`μ_t = (T_t)#μ`. Such a curve exists (`SVGD.exists_meanField`); `SVGD.meanFieldCurve Φ s μ` picks
one, and `SVGD.meanFieldFlow Φ s μ` is its flow. Its maps restrict to homeomorphisms of `Ω`. The
results along the flow are stated for `SVGD.meanFieldFlow`, and their primed versions (such as
`SVGD.weak_convergence'`) for every solution `m` of the mean-field equation.

## References

* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025]
* [Q. Liu, J. Lee, M. Jordan, *A Kernelized Stein Discrepancy for Goodness-of-fit Tests*][Liu2016]
* [Q. Liu, D. Wang, *Stein Variational Gradient Descent*][Liu2016SVGD]
* [Q. Liu, *Stein Variational Gradient Descent as Gradient Flow*][Liu2017]
* [C. Stein, *A bound for the error in the normal approximation to the distribution of a sum of
  dependent random variables*][Stein1972]
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InformationTheory ProbabilityTheory

open scoped NNReal ENNReal RealInnerProductSpace BoundedContinuousFunction

noncomputable section

/-! ## Appendix A.2.1: the standing assumptions -/

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- **The assumptions on the target** `π` (Section 3 of [Serre2025]): `π = p · λ|_Ω` is a
probability measure, where the density `p` is measurable, continuous and positive on `Ω`, and its
score `s` is the derivative of `log p` on the interior of `Ω` and is continuous on `Ω`. -/
structure AdmissibleTarget (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (π : Measure (EuclideanSpace ℝ (Fin d))) (p : EuclideanSpace ℝ (Fin d) → ℝ)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) : Prop where
  /-- `π` has density `p` with respect to the Lebesgue measure on `Ω`. -/
  eq_withDensity : π = (volume.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  /-- `π` is a probability measure, i.e. the density `p` is normalized. -/
  isProbabilityMeasure : IsProbabilityMeasure π
  /-- The density `p` is measurable. -/
  measurable : Measurable p
  /-- The density `p` is continuous on `Ω`. -/
  continuousOn : ContinuousOn p Ω
  /-- The density `p` is positive on `Ω`. -/
  pos : ∀ x ∈ Ω, 0 < p x
  /-- The score `s = ∇ log p` is the derivative of `log p` on the interior of `Ω`. -/
  hasFDerivAt_log : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ Real.log (p y)) (s x) x
  /-- The score `s` is continuous on `Ω`. -/
  continuousOn_score : ContinuousOn s Ω

/-- **The assumptions on the kernel** `k(x, y) = ⟪Φ x, Φ y⟫` (Appendix A.2 of [Serre2025]): the
feature map `Φ` is `C¹`, `K`-Lipschitz and bounded by `C`, and it vanishes on the frontier of `Ω`.
The last condition makes every function of `𝓗` vanish on the frontier of `Ω`, so that the
particles stay in `Ω`. -/
structure AdmissibleFeatureMap (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (K C : ℝ≥0) : Prop where
  /-- `Φ` is continuously differentiable. -/
  contDiff : ContDiff ℝ 1 Φ
  /-- `Φ` is `K`-Lipschitz. -/
  lipschitzWith : LipschitzWith K Φ
  /-- `Φ` is bounded by `C`. -/
  norm_le : ∀ y, ‖Φ y‖ ≤ C
  /-- `Φ` vanishes on the frontier of `Ω`. -/
  eq_zero_of_mem_frontier : ∀ y ∈ frontier Ω, Φ y = 0

/-- **The standing assumptions** (Section 3 and Appendix A.2 of [Serre2025]) on the space `Ω`, the
target `π = p · λ|_Ω` with score `s`, and the kernel given by the feature map `Φ`. -/
structure StandingAssumptions (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (π : Measure (EuclideanSpace ℝ (Fin d))) (p : EuclideanSpace ℝ (Fin d) → ℝ)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (Φ : EuclideanSpace ℝ (Fin d) → H₀) (K C : ℝ≥0) : Prop where
  /-- **The space.** The domain `Ω` is compact. -/
  isCompact : IsCompact Ω
  /-- **The target.** `π = p · λ|_Ω` satisfies `SVGD.AdmissibleTarget`. -/
  target : AdmissibleTarget Ω π p s
  /-- **The kernel.** The feature map `Φ` satisfies `SVGD.AdmissibleFeatureMap`. -/
  kernel : AdmissibleFeatureMap Φ Ω K C

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {π μ : Measure (EuclideanSpace ℝ (Fin d))}
  {p : EuclideanSpace ℝ (Fin d) → ℝ}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {Φ : EuclideanSpace ℝ (Fin d) → H₀} {K C B : ℝ≥0} {m : ℝ → 𝓗[d, H₀]}

/-- A measure at finite Kullback–Leibler divergence from `π` is carried by `Ω`. -/
private theorem StandingAssumptions.ae_mem (hS : StandingAssumptions Ω π p s Φ K C)
    (hKL : klDiv μ π ≠ ∞) : ∀ᵐ x ∂μ, x ∈ Ω :=
  sorry

/-- The flow of a bounded continuous curve of `𝓗` keeps the measures carried by `Ω` on `Ω`. -/
private theorem StandingAssumptions.ae_map_trajectory_mem
    (hS : StandingAssumptions Ω π p s Φ K C) (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ω) (t : ℝ) :
    ∀ᵐ y ∂μ.map (trajectory Φ m 0 · t), y ∈ Ω :=
  sorry

end SVGD

/-! ## Appendix A.2.2: Stein's method -/

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Stein operator** (Appendix A.2.2 of [Serre2025]) with score `s : E → E →L[ℝ] ℝ`, applied
to the vector field `φ : E → E`: `𝒜_s φ (x) = s x (φ x) + div φ (x)`. When `s` is the logarithmic
derivative of a density `p`, this is `𝒜_p φ = ∇ log p ᵀ φ + ∇ · φ`. -/
def steinOperator (s : E → StrongDual ℝ E) (φ : E → E) (x : E) : ℝ :=
  s x (φ x) + divergence ℝ φ x

/-- The divergence (`CompactSVGD/Definitions.lean`) is the trace of the derivative. -/
example (φ : E → E) (x : E) : divergence ℝ φ x = LinearMap.trace ℝ E (fderiv ℝ φ x) :=
  rfl

variable [MeasurableSpace E]

/-- **The Stein class** of the density `p` with respect to `μ` (Definition A.2 of [Serre2025]): the
vector fields `φ` such that `p • φ` is differentiable `μ`-almost everywhere, with a `μ`-integrable
divergence of integral `0`. With `μ = λ|_Ω` and a regular boundary `∂Ω`, the divergence theorem
turns the last condition into the boundary condition `∮_{∂Ω} p φ · n dS = 0` of Definition A.2 of
[Serre2025]. -/
def steinClass (μ : Measure E) (p : E → ℝ) : Set (E → E) :=
  {φ | (∀ᵐ x ∂μ, DifferentiableAt ℝ (p • φ) x) ∧
    Integrable (divergence ℝ (p • φ)) μ ∧ ∫ x, divergence ℝ (p • φ) x ∂μ = 0}

/-- **Stein's identity** (Lemma A.3 of [Serre2025]). Let `p ≥ 0` be a density with score `s`,
i.e. `Dp = p • s` holds `μ`-almost everywhere, and let `φ` be differentiable `μ`-almost everywhere
and in the Stein class of `p`. Then the Stein operator `𝒜_s φ` has zero mean under `p · μ`:
`E_{x ∼ p · μ}[𝒜_s φ (x)] = 0`. -/
theorem stein_identity [FiniteDimensional ℝ E] {μ : Measure E} {p : E → ℝ}
    {s : E → StrongDual ℝ E} {φ : E → E} (hp : AEMeasurable p μ) (hp₀ : 0 ≤ᵐ[μ] p)
    (hs : ∀ᵐ x ∂μ, HasFDerivAt p (p x • s x) x) (hφ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x)
    (hφS : φ ∈ steinClass μ p) :
    ∫ x, steinOperator s φ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (p x)) = 0 :=
  sorry

end ProbabilityTheory

/-! ## Appendix A.2.3: the kernelized Stein discrepancy -/

/-! ### Definition A.4: the product RKHS

The kernel is `k(x, y) = ⟪Φ x, Φ y⟫` and its RKHS is represented by the real Hilbert space `H₀`.
The product RKHS is `𝓗[d, H₀] = PiLp 2 fun _ : Fin d ↦ H₀`, with
`⟪f, g⟫_𝓗 = ∑ᵢ ⟪fᵢ, gᵢ⟫_{H₀}`, and `f ∈ 𝓗` acts on `ℝᵈ` as the vector field
`toVectorField Φ f : y ↦ (⟪fᵢ, Φ y⟫)ᵢ` (both in `CompactSVGD/Definitions.lean`).

The reproducing property `fᵢ(y) = ⟪fᵢ, k(·, y)⟫` thus holds by definition, and its derivative
form `∂ᵢ fᵢ(y) = ⟪fᵢ, ∂ᵢ k(·, y)⟫` follows from the differentiability of `Φ`; together they give
`𝒜_π f (x) = ⟪f, ξ_x⟫` (`SVGD.reproducing_property`). Nothing else is used about RKHS: neither the
uniqueness of the RKHS, nor the integral positive definiteness of `k`, nor the density of `H₀` in
`L²`. Every RKHS fits this setting, with its canonical feature map `x ↦ k(·, x)`. Conversely, `𝓗`
may contain elements whose vector field vanishes (those orthogonal to every `Φ y` and `∂ᵢ Φ y`);
they change neither `𝒜_π f`, nor the KSD, nor `φ*_μ`, nor Stein-universality. -/

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  {Φ : EuclideanSpace ℝ (Fin d) → H₀}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {Ω : Set (EuclideanSpace ℝ (Fin d))} {π μ ν : Measure (EuclideanSpace ℝ (Fin d))}
  {p : EuclideanSpace ℝ (Fin d) → ℝ} {K C B : ℝ≥0} {m : ℝ → 𝓗[d, H₀]}

/-- The product RKHS `𝓗` is the Hilbert sum of `d` copies of `H₀`. -/
example : 𝓗[d, H₀] = PiLp 2 fun _ : Fin d ↦ H₀ :=
  rfl

/-- `f ∈ 𝓗` acts on `ℝᵈ` as the vector field `y ↦ (⟪fᵢ, Φ y⟫)ᵢ = (⟪fᵢ, k(·, y)⟫)ᵢ`. -/
example (f : 𝓗[d, H₀]) (y : EuclideanSpace ℝ (Fin d)) :
    toVectorField Φ f y = WithLp.toLp 2 fun i ↦ ⟪f i, Φ y⟫ :=
  rfl

/-! ### The update direction and the kernelized Stein discrepancy -/

/-- The element `ξ_x = ∇ log π(x) k(·, x) + ∇_x k(·, x)` of `𝓗` (Appendix A.2.3 of [Serre2025]),
whose components are `(ξ_x)ᵢ = s x eᵢ • Φ x + ∂ᵢ Φ x`. -/
def steinFeature (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : 𝓗[d, H₀] :=
  WithLp.toLp 2 fun i ↦
    s x (EuclideanSpace.single i 1) • Φ x + fderiv ℝ Φ x (EuclideanSpace.single i 1)

/-- The update direction `φ*_μ = E_{x ∼ μ}[ξ_x]` of SVGD (Equation (3) and Appendix A.2.3 of
[Serre2025]). It is defined for every measure `μ`, with or without a density. -/
def direction (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : 𝓗[d, H₀] :=
  ∫ x, steinFeature Φ s x ∂μ

/-- **The kernelized Stein discrepancy** (Definition A.5 of [Serre2025]):
`𝔎(μ ∣ π) = sup_{‖f‖_𝓗 ≤ 1} E_{x ∼ μ}[𝒜_π f (x)]²`. The supremum is a real supremum, hence `0`
if the family is unbounded; it is finite for `μ ∈ 𝒫(Ω)` (Theorem A.7). -/
def kernelSteinDiscrepancy (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⨆ f : closedBall (0 : 𝓗[d, H₀]) 1, (∫ x, steinOperator s (toVectorField Φ f) x ∂μ) ^ 2

/-- The kernelized Stein discrepancy `𝔎(μ ∣ π)` of [Serre2025], written `𝔎[Φ, s] μ`: it depends on
the target `π` only through its score `s`. -/
scoped notation "𝔎[" Φ ", " s "]" => kernelSteinDiscrepancy Φ s

/-- The kernelized Stein discrepancy is nonnegative (Theorem A.11 of [Serre2025] uses it). -/
theorem ksd_nonneg (μ : Measure (EuclideanSpace ℝ (Fin d))) : 0 ≤ 𝔎[Φ, s] μ :=
  sorry

/-- **The reproducing property** (Appendix A.2.3 of [Serre2025]). For `f ∈ 𝓗`, the reproducing
properties `fᵢ(x) = ⟪fᵢ, k(·, x)⟫` and `∂ᵢ fᵢ(x) = ⟪fᵢ, ∂ᵢ k(·, x)⟫` give
`𝒜_π f (x) = ⟪f, ξ_x⟫_𝓗`. -/
theorem reproducing_property {x : EuclideanSpace ℝ (Fin d)} (hΦ : DifferentiableAt ℝ Φ x)
    (f : 𝓗[d, H₀]) : steinOperator s (toVectorField Φ f) x = ⟪f, steinFeature Φ s x⟫ :=
  sorry

/-! ### Lemma A.6: regularity of `ξ` -/

section KSD

variable (hS : StandingAssumptions Ω π p s Φ K C)
include hS

/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): `x ↦ ξ_x` is uniformly continuous from `Ω`
to `𝓗`. -/
theorem xi_regularity_uniformContinuousOn : UniformContinuousOn (steinFeature Φ s) Ω :=
  sorry

/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): `B = max_{x ∈ Ω} ‖ξ_x‖_𝓗` is finite. -/
theorem xi_regularity_exists_bound : ∃ B, ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B :=
  sorry

/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): for every finite measure `ν` on `Ω`,
`φ*_ν = ∫_Ω ξ_x dν(x)` is well defined in `𝓗`. -/
theorem xi_regularity_integrable [IsFiniteMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) :
    Integrable (steinFeature Φ s) ν :=
  sorry

omit hS in
/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): `‖φ*_ν‖_𝓗 ≤ B` for every `ν ∈ 𝒫(Ω)`, where
`B` bounds `‖ξ_x‖_𝓗` on `Ω`. -/
theorem xi_regularity_norm_direction_le {B : ℝ} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) : ‖direction Φ s ν‖ ≤ B :=
  sorry

/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): `‖φ*_ν(y)‖₂ ≤ B C` for every `ν ∈ 𝒫(Ω)` and
every `y`, where `B` bounds `‖ξ_x‖_𝓗` on `Ω` and `C` bounds `‖k(·, y)‖_{H₀} = ‖Φ y‖`. -/
theorem xi_regularity_norm_direction_apply_le {B : ℝ≥0}
    (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B) [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω)
    (y : EuclideanSpace ℝ (Fin d)) : ‖toVectorField Φ (direction Φ s ν) y‖ ≤ B * C :=
  sorry

/-- **Continuity of the Stein operator** (Appendix A.2.3 of [Serre2025]): for `f ∈ 𝓗`, `𝒜_π f` is
continuous on `Ω`. -/
theorem continuousOn_steinOperator (f : 𝓗[d, H₀]) :
    ContinuousOn (steinOperator s (toVectorField Φ f)) Ω :=
  sorry

/-! ### Theorem A.7: the steepest trajectory -/

section SteepestTrajectory

variable [CompleteSpace H₀] [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω)
include hμ

/-- **The steepest trajectory** (Theorem A.7 of [Serre2025]): for every `μ ∈ 𝒫(Ω)` and `f ∈ 𝓗`,
`E_{x ∼ μ}[𝒜_π f (x)] = ⟪f, φ*_μ⟫_𝓗`. -/
theorem steepest_trajectory_integral (f : 𝓗[d, H₀]) :
    ∫ x, steinOperator s (toVectorField Φ f) x ∂μ = ⟪f, direction Φ s μ⟫ :=
  sorry

/-- **The steepest trajectory** (Theorem A.7 of [Serre2025]): `φ*_μ / ‖φ*_μ‖_𝓗` maximizes
`f ↦ E_{x ∼ μ}[𝒜_π f (x)]` on the unit ball of `𝓗`. -/
theorem steepest_trajectory_isMaxOn :
    IsMaxOn (fun f : 𝓗[d, H₀] ↦ ∫ x, steinOperator s (toVectorField Φ f) x ∂μ)
      (closedBall 0 1) (‖direction Φ s μ‖⁻¹ • direction Φ s μ) :=
  sorry

/-- **The steepest trajectory** (Theorem A.7 of [Serre2025]):
`𝔎(μ ∣ π) = ‖φ*_μ‖²_𝓗`. -/
theorem steepest_trajectory_ksd : 𝔎[Φ, s] μ = ‖direction Φ s μ‖ ^ 2 :=
  sorry

/-- **The steepest trajectory** (Theorem A.7 of [Serre2025]):
`𝔎(μ ∣ π) = E_{x ∼ μ}[𝒜_π φ*_μ (x)]`. -/
theorem steepest_trajectory_ksd_eq_integral :
    𝔎[Φ, s] μ = ∫ x, steinOperator s (toVectorField Φ (direction Φ s μ)) x ∂μ :=
  sorry

end SteepestTrajectory

/-! ### Theorem A.8: the steepest descent of the Kullback–Leibler divergence -/

omit hS in
/-- The first variation of the Kullback–Leibler divergence to `π` at `μ` along `f ∈ 𝓗`
(Theorem A.8 of [Serre2025]): `∇_ε KL(T_ε(f)#μ ‖ π)|_{ε=0}`, where `T_ε(f) = I_d + ε f` and `f` acts
through its vector field. It is `0` if this map is not differentiable at `0`. -/
def klFirstVariation (Φ : EuclideanSpace ℝ (Fin d) → H₀) (π μ : Measure (EuclideanSpace ℝ (Fin d)))
    (f : 𝓗[d, H₀]) : ℝ :=
  deriv (fun ε : ℝ ↦ (klDiv (μ.map fun x ↦ x + ε • toVectorField Φ f x) π).toReal) 0

section KLSteepestDescent

variable [CompleteSpace H₀] [IsProbabilityMeasure μ] (hKL : klDiv μ π ≠ ∞)
include hKL

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): for a probability
measure `μ` with `KL(μ ‖ π) < ∞` and `f ∈ 𝓗`, the map `ε ↦ KL((I_d + ε f)#μ ‖ π)` is
differentiable at `0`, with derivative `-⟪f, φ*_μ⟫_𝓗`. -/
theorem kl_steepest_descent_hasDerivAt (f : 𝓗[d, H₀]) :
    HasDerivAt (fun ε : ℝ ↦ (klDiv (μ.map fun x ↦ x + ε • toVectorField Φ f x) π).toReal)
      (-⟪f, direction Φ s μ⟫) 0 :=
  sorry

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): the first variation of
`KL(· ‖ π)` at `μ` is the linear form `f ↦ -⟪f, φ*_μ⟫_𝓗`. -/
theorem kl_steepest_descent_eq_inner (f : 𝓗[d, H₀]) :
    klFirstVariation Φ π μ f = -⟪f, direction Φ s μ⟫ :=
  sorry

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): on the unit ball of `𝓗`,
the first variation of `KL(· ‖ π)` at `μ` is minimized at `φ*_μ / ‖φ*_μ‖_𝓗`. -/
theorem kl_steepest_descent_isMinOn :
    IsMinOn (klFirstVariation Φ π μ) (closedBall 0 1)
      (‖direction Φ s μ‖⁻¹ • direction Φ s μ) :=
  sorry

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): if `φ*_μ ≠ 0`, then
`φ*_μ / ‖φ*_μ‖_𝓗` is the only minimizer of the first variation of `KL(· ‖ π)` at `μ` on the unit
ball of `𝓗`. -/
theorem kl_steepest_descent_eq (hφ : direction Φ s μ ≠ 0) {f : 𝓗[d, H₀]}
    (hf : f ∈ closedBall 0 1)
    (hmin : klFirstVariation Φ π μ f =
      klFirstVariation Φ π μ (‖direction Φ s μ‖⁻¹ • direction Φ s μ)) :
    f = ‖direction Φ s μ‖⁻¹ • direction Φ s μ :=
  sorry

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): along `φ*_μ`,
`∇_ε KL((I_d + ε φ*_μ)#μ ‖ π)|_{ε=0} = -𝔎(μ ∣ π)`. -/
theorem kl_steepest_descent_direction :
    klFirstVariation Φ π μ (direction Φ s μ) = -𝔎[Φ, s] μ :=
  sorry

end KLSteepestDescent

end KSD

/-! ### Definition A.9: Stein-universal kernels -/

/-- **Stein-universal kernels** (Definition A.9 of [Serre2025], stated as a density). The kernel
is Stein-universal on `Ω` if the functions `𝒜_π f + c`, for `f ∈ 𝓗` and `c ∈ ℝ`, are dense in
`C(Ω, ℝ)`. As `Ω` is compact, the topology of `C(Ω, ℝ)` is that of uniform convergence on `Ω`.

The constants are needed. Under the standing assumptions, `E_π[𝒜_π f] = 0` for every `f ∈ 𝓗`
(by Theorem A.7, as `𝔎(π ∣ π) = 0`, see the proof of Proposition 3.2), so the functions `𝒜_π f`
alone only approximate functions with zero mean under `π`. Integrating against `π` then shows that
the definition is equivalent to the formulation of Definition A.9 of [Serre2025]: for every
`φ ∈ C(Ω, ℝ)`, `φ - E_π[φ]` is a uniform limit of functions `𝒜_π f` (not formalized). -/
def IsSteinUniversal (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Dense {φ : C(Ω, ℝ) | ∃ f : 𝓗[d, H₀], ∃ c : ℝ,
    ∀ x : Ω, φ x = steinOperator s (toVectorField Φ f) x + c}

/-! ### The mean-field SVGD flow

The flow `(T_t)_{t ≥ 0}` of Theorems A.11 and 3.1 of [Serre2025] is driven by the update directions
of its own push-forwards: `∂ₜ T_t(x) = φ*_{μ_t}(T_t(x))` with `μ_t = (T_t)#μ`. We describe it by
the curve `m : ℝ → 𝓗` of its update directions. The mean-field equation is then `m t = φ*_{μ_t}`
for `t ≥ 0`, where `T_t = trajectory Φ m 0 · t` is the flow of the vector field of `m`.

Under the standing assumptions, the mean-field equation has a solution (`SVGD.exists_meanField`),
with no Lipschitz condition on the score. It is a fixed point of `G : m ↦ (t ↦ φ*_{(Xᵐₜ)#ν})`,
where `Xᵐ` is the flow of `m`. The map `G` is continuous, its images are equicontinuous and lie in
the compact closed convex hull of `ξ(Ω)`, and `G m` at time `t` only depends on `m` before `t`, so
it has a fixed point on every compact interval by Tonelli's argument. The solutions on the
intervals `[n, n + 1]` are then concatenated. The uniqueness of the solution is not claimed:
`SVGD.meanFieldCurve` picks one of them, and the results below hold for it. -/

/-- The trajectories of a curve `m` in `𝓗` are the global solutions of
`x' = toVectorField Φ (m t) x` (`CompactSVGD/Definitions.lean`). -/
example (t₀ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m t₀ x = ODE.globalSolution (fun t ↦ toVectorField Φ (m t)) t₀ x :=
  rfl

open Classical in
/-- `ODE.globalSolution v t₀ x` (`CompactSVGD/Definitions.lean`) is a solution of `α' t = v t (α t)`
with `α t₀ = x`, chosen with the axiom of choice, or the constant curve `x` if there is none. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : ℝ → E → E) (t₀ : ℝ) (x : E) :
    ODE.globalSolution v t₀ x =
      if h : ∃ α : ℝ → E, α t₀ = x ∧ IsIntegralCurve α v then h.choose else fun _ ↦ x :=
  rfl

/-- **The mean-field SVGD equation** from `μ` for a curve `m : ℝ → 𝓗`: `m t = φ*_{μ_t}` for every
`t ≥ 0`, where `μ_t = (T_t)#μ` and `T_t = trajectory Φ m 0 · t` is the flow of the vector field of
`m`. -/
def IsMeanFieldCurve (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → 𝓗[d, H₀]) : Prop :=
  ∀ t, 0 ≤ t → m t = direction Φ s (μ.map (trajectory Φ m 0 · t))

/-- The mean-field SVGD equation, unfolded. -/
example :
    IsMeanFieldCurve Φ s μ m = ∀ t, 0 ≤ t → m t = direction Φ s (μ.map (trajectory Φ m 0 · t)) :=
  rfl

open Classical in
/-- **The mean-field SVGD curve** from `μ`: a continuous bounded solution `m : ℝ → 𝓗` of the
mean-field SVGD equation `SVGD.IsMeanFieldCurve Φ s μ m`, i.e. `m t = φ*_{μ_t}` for every `t ≥ 0`,
where `μ_t = (T_t)#μ` and `T_t = trajectory Φ m 0 · t`. Such a curve exists under the standing
assumptions for `μ ∈ 𝒫(Ω)` (`SVGD.exists_meanField`). As its uniqueness is not claimed, this
definition picks one with the axiom of choice; it is `0` if there is none. -/
def meanFieldCurve (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ → 𝓗[d, H₀] :=
  if h : ∃ m : ℝ → 𝓗[d, H₀], Continuous m ∧ (∃ B : ℝ≥0, ∀ t, ‖m t‖ ≤ B) ∧
      IsMeanFieldCurve Φ s μ m then h.choose else 0

/-- **The mean-field SVGD flow** `T_t` from `μ`: the trajectories, from time `0`, of the vector
field of the mean-field SVGD curve `SVGD.meanFieldCurve Φ s μ`. -/
def meanFieldFlow (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  trajectory Φ (meanFieldCurve Φ s μ) 0 x t

/-- The mean-field SVGD curve is continuous (so is its value `0` when there is no solution). -/
theorem continuous_meanFieldCurve : Continuous (meanFieldCurve Φ s μ) :=
  sorry

/-- The mean-field SVGD curve is bounded. -/
theorem exists_norm_meanFieldCurve_le : ∃ B : ℝ≥0, ∀ t, ‖meanFieldCurve Φ s μ t‖ ≤ B :=
  sorry

/-- **The mean-field SVGD flow starts at the identity**: `T_0 = I_d`. -/
theorem meanFieldFlow_zero (hS : StandingAssumptions Ω π p s Φ K C) (x : EuclideanSpace ℝ (Fin d)) :
    meanFieldFlow Φ s μ 0 x = x :=
  sorry

/-- **The mean-field SVGD flow maps are homeomorphisms of `Ω`.** -/
theorem exists_homeomorph_meanFieldFlow (hS : StandingAssumptions Ω π p s Φ K C) (t : ℝ) :
    ∃ e : Ω ≃ₜ Ω, ∀ x : Ω, (e x : EuclideanSpace ℝ (Fin d)) = meanFieldFlow Φ s μ t x :=
  sorry

section MeanFieldFlow

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
include hS

/-- The closed convex hull of `ξ(Ω)` is compact. -/
private theorem isCompact_closedConvexHull_steinFeature :
    IsCompact (closedConvexHull ℝ (steinFeature Φ s '' Ω)) :=
  sorry

/-- For every `ν ∈ 𝒫(Ω)`, `φ*_ν` lies in the closed convex hull of `ξ(Ω)`. -/
private theorem direction_mem_closedConvexHull [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) :
    direction Φ s ν ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω) :=
  sorry

/-- The closed convex hull of `ξ(Ω)` is bounded. -/
private theorem exists_norm_le_closedConvexHull_steinFeature :
    ∃ B : ℝ≥0, ∀ h ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω), ‖h‖ ≤ B :=
  sorry

/-- **Existence of a solution of the mean-field SVGD equation on a compact time interval.** Under
the standing assumptions, for every `ν ∈ 𝒫(Ω)` and every `a ≤ b`, there is a continuous curve `m`
with values in the closed convex hull of `ξ(Ω)` such that `m t = φ*_{(Xₜ)#ν}` for `t ∈ [a, b]`,
where `Xₜ = trajectory Φ m a · t`. -/
private theorem exists_meanField_Icc [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ m : ℝ → 𝓗[d, H₀], Continuous m ∧ (∀ t, m t ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω)) ∧
      ∀ t ∈ Icc a b, m t = direction Φ s (ν.map (trajectory Φ m a · t)) :=
  sorry

/-- **Existence of a solution of the mean-field SVGD equation on `[0, ∞)`.** Under the standing
assumptions, for every `μ ∈ 𝒫(Ω)`, there is a continuous curve `m` with values in the closed
convex hull of `ξ(Ω)` such that `m t = φ*_{(T_t)#μ}` for every `t ≥ 0`, where
`T_t = trajectory Φ m 0 · t`. -/
theorem exists_meanField [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    ∃ m : ℝ → 𝓗[d, H₀], Continuous m ∧ (∀ t, m t ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω)) ∧
      IsMeanFieldCurve Φ s μ m :=
  sorry

variable [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω)
include hμ

/-- **The mean-field SVGD curve solves the mean-field equation.** Under the standing assumptions,
for `μ ∈ 𝒫(Ω)`, `m t = φ*_{μ_t}` for every `t ≥ 0`, where `m = SVGD.meanFieldCurve Φ s μ` and
`μ_t = (T_t)#μ` along the flow `T_t = SVGD.meanFieldFlow Φ s μ t`. -/
theorem meanFieldCurve_eq_direction {t : ℝ} (ht : 0 ≤ t) :
    meanFieldCurve Φ s μ t = direction Φ s (μ.map (meanFieldFlow Φ s μ t)) :=
  sorry

/-- **The mean-field SVGD equation.** The particles follow the update direction of their law:
`∂ₜ T_t(x) = φ*_{μ_t}(T_t(x))` for `t ≥ 0`, where `μ_t = (T_t)#μ`. -/
theorem hasDerivAt_meanFieldFlow (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (meanFieldFlow Φ s μ · x)
      (toVectorField Φ (direction Φ s (μ.map (meanFieldFlow Φ s μ t))) (meanFieldFlow Φ s μ t x))
      t :=
  sorry

end MeanFieldFlow

/-! ### Theorem A.11: the time derivative of the Kullback–Leibler divergence -/

section TimeDerivativeKL

variable [CompleteSpace H₀]
variable (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure μ] (hKL : klDiv μ π ≠ ∞)
include hS hKL

/-- **Time derivative of the KL divergence**, for every solution of the mean-field equation (Theorem
A.11 of [Serre2025]). Let `m` be a continuous bounded solution of the mean-field equation from `μ`
(`SVGD.IsMeanFieldCurve Φ s μ m`), with flow `T_t = trajectory Φ m 0 · t`, and let `μ_t = (T_t)#μ`.
If `KL(μ ‖ π) < ∞`, then `d/dt KL(μ_t ‖ π) = -𝔎(μ_t ∣ π)` for every `t ≥ 0`. -/
theorem time_derivative_kl' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hmφ : IsMeanFieldCurve Φ s μ m) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal)
      (-𝔎[Φ, s] (μ.map (trajectory Φ m 0 · t))) t :=
  sorry

/-- **Time derivative of the KL divergence** (Theorem A.11 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` with
`KL(μ ‖ π) < ∞`, and let `μ_t = (T_t)#μ` along the mean-field SVGD flow. Then
`d/dt KL(μ_t ‖ π) = -𝔎(μ_t ∣ π)` for every `t ≥ 0`. -/
theorem time_derivative_kl {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (meanFieldFlow Φ s μ t)) π).toReal)
      (-𝔎[Φ, s] (μ.map (meanFieldFlow Φ s μ t))) t :=
  sorry

/-- **Time derivative of the KL divergence**, for every solution of the mean-field equation (Theorem
A.11 of [Serre2025]). Let `m` be a continuous bounded solution of the mean-field equation from `μ`
(`SVGD.IsMeanFieldCurve Φ s μ m`), with flow `T_t = trajectory Φ m 0 · t`, and let `μ_t = (T_t)#μ`.
If `KL(μ ‖ π) < ∞`, then `t ↦ KL(μ_t ‖ π)` is non-increasing on `[0, ∞)`, as `𝔎(μ_t ∣ π) ≥ 0`. -/
theorem time_derivative_kl_antitoneOn' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hmφ : IsMeanFieldCurve Φ s μ m) :
    AntitoneOn (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal) (Ici 0) :=
  sorry

/-- **Time derivative of the KL divergence** (Theorem A.11 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` with
`KL(μ ‖ π) < ∞`. As `𝔎(μ_t ∣ π) ≥ 0`, the Kullback–Leibler divergence `KL(μ_t ‖ π)` is
non-increasing along the mean-field SVGD flow. -/
theorem time_derivative_kl_antitoneOn :
    AntitoneOn (fun t ↦ (klDiv (μ.map (meanFieldFlow Φ s μ t)) π).toReal) (Ici 0) :=
  sorry

end TimeDerivativeKL

/-! ## Appendix B: proofs of Proposition 3.2 and Theorem 3.1 -/

variable [CompleteSpace H₀]

/-! ### Proposition 3.2: the KSD is a valid discrepancy -/

section KSDValidDiscrepancy

variable (hS : StandingAssumptions Ω π p s Φ K C) (hU : IsSteinUniversal Φ s Ω)
  [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω)
include hS hU hν

/-- **KSD valid discrepancy** (Proposition 3.2 of [Serre2025]). If the kernel is Stein-universal,
then for every `ν ∈ 𝒫(Ω)`, `ν = π ⟺ 𝔎(ν ∣ π) = 0`. -/
theorem ksd_valid_discrepancy : ν = π ↔ 𝔎[Φ, s] ν = 0 :=
  sorry

end KSDValidDiscrepancy

/-! ### Theorem 3.1: weak convergence of SVGD -/

section WeakConvergence

variable (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure μ]
include hS

/-- **Uniform continuity of the KSD**, for every continuous bounded curve (Lemma B.4 of
[Serre2025]). Let `m` be a continuous curve bounded by `B`, with flow `T_t = trajectory Φ m 0 · t`,
and let `μ ∈ 𝒫(Ω)` and `μ_t = (T_t)#μ`. Then `t ↦ 𝔎(μ_t ∣ π)` is uniformly continuous on `ℝ`. -/
theorem ksd_uniform_continuity' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B) (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    UniformContinuous fun t ↦ 𝔎[Φ, s] (μ.map (trajectory Φ m 0 · t)) :=
  sorry

/-- **Uniform continuity of the KSD** (Lemma B.4 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` and let
`μ_t = (T_t)#μ` along the mean-field SVGD flow. Then `t ↦ 𝔎(μ_t ∣ π)` is uniformly continuous. -/
theorem ksd_uniform_continuity (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    UniformContinuous fun t ↦ 𝔎[Φ, s] (μ.map (meanFieldFlow Φ s μ t)) :=
  sorry

variable (hKL : klDiv μ π ≠ ∞)
include hKL

/-- **Convergence of the KSD**, for every solution of the mean-field equation (Corollary B.5 of
[Serre2025]). Let `m` be a continuous bounded solution of the mean-field equation from `μ`
(`SVGD.IsMeanFieldCurve Φ s μ m`), with flow `T_t = trajectory Φ m 0 · t`, and let `μ_t = (T_t)#μ`.
If `KL(μ ‖ π) < ∞`, then `𝔎(μ_t ∣ π) → 0` as `t → ∞`. -/
theorem ksd_convergence' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hmφ : IsMeanFieldCurve Φ s μ m) :
    Tendsto (fun t ↦ 𝔎[Φ, s] (μ.map (trajectory Φ m 0 · t))) atTop (𝓝 0) :=
  sorry

/-- **Convergence of the KSD** (Corollary B.5 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` with `KL(μ ‖ π) < ∞`.
Along the mean-field SVGD flow, `𝔎(μ_t ∣ π) → 0` as `t → ∞`. -/
theorem ksd_convergence :
    Tendsto (fun t ↦ 𝔎[Φ, s] (μ.map (meanFieldFlow Φ s μ t))) atTop (𝓝 0) :=
  sorry

/-- **Cluster points**, for every solution of the mean-field equation (Lemma B.6 of [Serre2025]).
Let `m` be a continuous bounded solution of the mean-field equation from `μ`
(`SVGD.IsMeanFieldCurve Φ s μ m`), with flow `T_t = trajectory Φ m 0 · t`, and let `μ_t = (T_t)#μ`.
Let `KL(μ ‖ π) < ∞`, and let `ν ∈ 𝒫(Ω)` and `t_n → ∞` be such that `μ_{t_n} ⇀ ν`, i.e.
`E_{μ_{t_n}}[g] → E_ν[g]` for every `g` continuous on `Ω`. Then `𝔎(ν ∣ π) = 0`. -/
theorem cluster_points' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hmφ : IsMeanFieldCurve Φ s μ m) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Ω)
    (hconv : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω →
      Tendsto (fun n ↦ ∫ x, g x ∂μ.map (trajectory Φ m 0 · (t n))) atTop (𝓝 (∫ x, g x ∂ν))) :
    𝔎[Φ, s] ν = 0 :=
  sorry

/-- **Cluster points** (Lemma B.6 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` with `KL(μ ‖ π) < ∞`, and let
`μ_t = (T_t)#μ` along the mean-field SVGD flow. Let `ν ∈ 𝒫(Ω)` and `t_n → ∞` be such that
`μ_{t_n} ⇀ ν`, i.e. `E_{μ_{t_n}}[g] → E_ν[g]` for every `g` continuous on `Ω`. Then `𝔎(ν ∣ π) = 0`.
-/
theorem cluster_points {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Ω)
    (hconv : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω →
      Tendsto (fun n ↦ ∫ x, g x ∂μ.map (meanFieldFlow Φ s μ (t n))) atTop (𝓝 (∫ x, g x ∂ν))) :
    𝔎[Φ, s] ν = 0 :=
  sorry

/-- **Weak convergence of SVGD**, for every solution of the mean-field equation (Theorem 3.1 of
[Serre2025]). Under the standing assumptions, let the kernel be Stein-universal. Let `m` be a
continuous bounded solution of the mean-field equation from `μ` (`SVGD.IsMeanFieldCurve Φ s μ m`),
with flow `T_t = trajectory Φ m 0 · t`, and let `μ_t = (T_t)#μ`. If `KL(μ ‖ π) < ∞`, then `μ_t ⇀ π`:
for every `g` continuous on `Ω`, `E_{μ_t}[g] → E_π[g]` as `t → ∞`. -/
theorem weak_convergence' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hmφ : IsMeanFieldCurve Φ s μ m)
    (hU : IsSteinUniversal Φ s Ω) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ContinuousOn g Ω) :
    Tendsto (fun t ↦ ∫ x, g x ∂μ.map (trajectory Φ m 0 · t)) atTop (𝓝 (∫ x, g x ∂π)) :=
  sorry

/-- **Weak convergence of SVGD** (Theorem 3.1 of [Serre2025]). Under the standing assumptions, let
the kernel be Stein-universal and let `μ ∈ 𝒫(Ω)` with `KL(μ ‖ π) < ∞`. Along the mean-field SVGD
flow, `μ_t = (T_t)#μ` converges weakly to `π`: for every `g` continuous on `Ω`,
`E_{μ_t}[g] → E_π[g]` as `t → ∞`. -/
theorem weak_convergence (hU : IsSteinUniversal Φ s Ω) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ContinuousOn g Ω) :
    Tendsto (fun t ↦ ∫ x, g x ∂μ.map (meanFieldFlow Φ s μ t)) atTop (𝓝 (∫ x, g x ∂π)) :=
  sorry

end WeakConvergence

end SVGD

/-! ## A Stein-universal kernel on `[-1, 1]`

This section is not in [Serre2025]. It builds a kernel that satisfies all the hypotheses of
Theorem 3.1 in dimension `1`, on `Ω = [-1, 1]` (`closedBall 0 1`), for every admissible target.

The kernel is `k(x, y) = ∑ₙ wₙ² χ(x) Rₙ(x) χ(y) Rₙ(y)`, with the feature map
`SVGD.intervalFeatureMap : y ↦ (wₙ χ(y) Rₙ(y))ₙ ∈ ℓ²(ℕ, ℝ)` of `SVGD.seqFeatureMap`. The polynomial
`Rₙ` (`SVGD.intervalPoly n`) is the primitive of `tⁿ - mₙ` that vanishes at `-1` and `1`. Thus it is
a multiple of `w(t) = 1 - t²`, and `k` is a weighted kernel `w(x) w(y) k₀(x, y)` on `Ω`. The cutoff
`χ` (`SVGD.intervalCutoff`) equals `1` on `[-2, 2]`. It makes the feature map bounded and Lipschitz
on `ℝ`. The weights `wₙ` make it `C¹`, as `wₙ (|gₙ| + |gₙ'|) ≤ 2⁻ⁿ` for `gₙ = χ Rₙ`. As the `Rₙ`
vanish at `±1`, so does the feature map (`SVGD.admissibleFeatureMap_intervalFeatureMap`).

Stein-universality (`SVGD.isSteinUniversal_intervalFeatureMap`) only needs a score `σ` continuous
on `Ω`. Let `φ` be continuous on `Ω`. The one-dimensional Stein equation `σ u + u' = φ - c` has a
solution with `u(-1) = u(1) = 0` (`exists_hasDerivAt_sub_sub_mul`). By the Weierstrass
theorem, `u'` is uniformly close to a polynomial `q = ∑ₙ qₙ tⁿ` on `Ω`. Then `R = ∑ₙ qₙ Rₙ` is
close to `u` in `C¹(Ω)`, and `𝒜_π R + c = σ R + R' + c` is uniformly close to `φ` on `Ω`.

In dimension `d ≥ 2`, a kernel of this form cannot vanish on the frontier of a box and be
Stein-universal: at a corner, `ξ_y = 0`. Weighted kernels on domains with a `C²` frontier are not
formalized. -/

namespace SVGD

open scoped lp

/-- The cutoff `χ` of `SVGD.intervalFeatureMap`: a smooth function on `ℝ`, equal to `1` on
`[-2, 2]` and supported in `(-3, 3)`. -/
@[simps]
def intervalCutoff : ContDiffBump (0 : ℝ) where
  rIn := 2
  rOut := 3
  rIn_pos := two_pos
  rIn_lt_rOut := by norm_num

/-- The polynomial `Rₙ(t) = (tⁿ⁺¹ - (-1)ⁿ⁺¹) / (n + 1) - mₙ (t + 1)`, with
`mₙ = (1 - (-1)ⁿ⁺¹) / (2 (n + 1))`: the primitive of `tⁿ - mₙ` that vanishes at `-1` and `1`. -/
def intervalPoly (n : ℕ) (t : ℝ) : ℝ :=
  (t ^ (n + 1) - (-1) ^ (n + 1)) / (n + 1) - (1 - (-1) ^ (n + 1)) / (2 * (n + 1)) * (t + 1)

/-- **A Stein-universal kernel on `[-1, 1]`.** The feature map `y ↦ (wₙ χ(y) Rₙ(y))ₙ ∈ ℓ²(ℕ, ℝ)` of
the kernel `k(x, y) = ∑ₙ wₙ² χ(x) Rₙ(x) χ(y) Rₙ(y)` on `ℝ`, where `χ = SVGD.intervalCutoff`,
`Rₙ = SVGD.intervalPoly n` and the weights `wₙ > 0` are those of `SVGD.seqFeatureMap`. -/
def intervalFeatureMap (y : EuclideanSpace ℝ (Fin 1)) : ℓ²(ℕ, ℝ) :=
  seqFeatureMap (fun n t ↦ intervalCutoff t * intervalPoly n t) (y 0)

/-- The feature map of a sequence of functions (`CompactSVGD/Definitions.lean`). -/
example (g : ℕ → ℝ → ℝ) (x : ℝ) :
    seqFeatureMap g x = ∑' n, (seqWeight g n * g n x) • lp.single 2 n 1 :=
  rfl

/-- The weights of `SVGD.seqFeatureMap` (`CompactSVGD/Definitions.lean`). -/
example (g : ℕ → ℝ → ℝ) (n : ℕ) :
    seqWeight g n = (2⁻¹ : ℝ) ^ n / (1 + ⨆ x, (‖g n x‖ + ‖fderiv ℝ (g n) x‖)) :=
  rfl

private theorem intervalCutoff_eq_one {t : ℝ} (ht : |t| ≤ 2) : intervalCutoff t = 1 :=
  sorry

private theorem intervalPoly_neg_one (n : ℕ) : intervalPoly n (-1) = 0 :=
  sorry

private theorem intervalPoly_one (n : ℕ) : intervalPoly n 1 = 0 :=
  sorry

private theorem hasDerivAt_intervalPoly (n : ℕ) (t : ℝ) :
    HasDerivAt (intervalPoly n) (t ^ n - (1 - (-1) ^ (n + 1)) / (2 * (n + 1))) t :=
  sorry

private theorem contDiff_intervalCutoff_mul (n : ℕ) :
    ContDiff ℝ 1 fun t ↦ intervalCutoff t * intervalPoly n t :=
  sorry

private theorem bddAbove_intervalCutoff_mul (n : ℕ) :
    BddAbove (range fun t ↦ ‖intervalCutoff t * intervalPoly n t‖ +
      ‖fderiv ℝ (fun t ↦ intervalCutoff t * intervalPoly n t) t‖) :=
  sorry

/-- **The kernel of `SVGD.intervalFeatureMap` is admissible** on `Ω = [-1, 1]`: its feature map is
`C¹`, `2`-Lipschitz, bounded by `2`, and vanishes at `±1`. -/
theorem admissibleFeatureMap_intervalFeatureMap :
    AdmissibleFeatureMap intervalFeatureMap (closedBall 0 1) 2 2 :=
  sorry

/-- In dimension `1`, if `⟪h, Φ y⟫ = G(y₀)` for every `y`, then the Stein operator of the vector
field of `h` is `𝒜 h (x) = s x (e₀) G(x₀) + G'(x₀)`. -/
private theorem steinOperator_eq_of_inner_eq {H₀ : Type*} [NormedAddCommGroup H₀]
    [InnerProductSpace ℝ H₀] {Φ : EuclideanSpace ℝ (Fin 1) → H₀}
    {s : EuclideanSpace ℝ (Fin 1) → StrongDual ℝ (EuclideanSpace ℝ (Fin 1))} {h : H₀} {G : ℝ → ℝ}
    (hG : Differentiable ℝ G) (hΦ : ∀ y, ⟪h, Φ y⟫ = G (y 0)) (x : EuclideanSpace ℝ (Fin 1)) :
    steinOperator s (toVectorField Φ (WithLp.toLp 2 fun _ ↦ h : 𝓗[1, H₀])) x =
      s x (EuclideanSpace.single 0 1) * G (x 0) + deriv G (x 0) :=
  sorry

/-- If `f(-1) = f(1) = 0` and `f' = e - m` with `|e| ≤ δ` on `[-1, 1]`, then `|m| ≤ δ`. -/
private theorem abs_le_of_hasDerivAt_sub {f e : ℝ → ℝ} {m δ : ℝ}
    (hf : ∀ t, HasDerivAt f (e t - m) t) (he : Continuous e) (ha : f (-1) = 0) (hb : f 1 = 0)
    (heδ : ∀ t ∈ Icc (-1 : ℝ) 1, |e t| ≤ δ) : |m| ≤ δ :=
  sorry

/-- If `f(-1) = f(1) = 0` and `f' = e - m` with `|e| ≤ δ` on `[-1, 1]`, then `|f| ≤ 4 δ` on
`[-1, 1]`. -/
private theorem abs_apply_le_of_hasDerivAt_sub {f e : ℝ → ℝ} {m δ : ℝ}
    (hf : ∀ t, HasDerivAt f (e t - m) t) (he : Continuous e) (ha : f (-1) = 0) (hb : f 1 = 0)
    (heδ : ∀ t ∈ Icc (-1 : ℝ) 1, |e t| ≤ δ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    |f t| ≤ 4 * δ :=
  sorry

/-- **The kernel of `SVGD.intervalFeatureMap` is Stein-universal** on `Ω = [-1, 1]`, for every
score `s` continuous on `Ω`. -/
theorem isSteinUniversal_intervalFeatureMap
    {s : EuclideanSpace ℝ (Fin 1) → StrongDual ℝ (EuclideanSpace ℝ (Fin 1))}
    (hs : ContinuousOn s (closedBall 0 1)) :
    IsSteinUniversal intervalFeatureMap s (closedBall 0 1) :=
  sorry

/-- **Weak convergence of SVGD on `[-1, 1]`** (Theorem 3.1 of [Serre2025] in dimension `1`, with an
explicit kernel). Let `π` be an admissible target on `Ω = [-1, 1]` and let `μ ∈ 𝒫(Ω)` with
`KL(μ ‖ π) < ∞`. Along the mean-field SVGD flow of the kernel of `SVGD.intervalFeatureMap`,
`μ_t ⇀ π`: for every `g` continuous on `Ω`, `E_{μ_t}[g] → E_π[g]` as `t → ∞`. -/
theorem weak_convergence_intervalFeatureMap {π μ : Measure (EuclideanSpace ℝ (Fin 1))}
    {p : EuclideanSpace ℝ (Fin 1) → ℝ}
    {s : EuclideanSpace ℝ (Fin 1) → StrongDual ℝ (EuclideanSpace ℝ (Fin 1))}
    (hπ : AdmissibleTarget (closedBall 0 1) π p s) [IsProbabilityMeasure μ] (hKL : klDiv μ π ≠ ∞)
    (g : EuclideanSpace ℝ (Fin 1) → ℝ) (hg : ContinuousOn g (closedBall 0 1)) :
    Tendsto (fun t ↦ ∫ x, g x ∂μ.map (meanFieldFlow intervalFeatureMap s μ t)) atTop
      (𝓝 (∫ x, g x ∂π)) :=
  sorry

end SVGD
