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

import CompactSVGD.FeatureMap.Sequence
import CompactSVGD.FeatureMap.Trajectory
import CompactSVGD.FeatureMap.VectorField
import CompactSVGD.ForMathlib.Analysis.Calculus.Barbalat
import CompactSVGD.ForMathlib.Analysis.Calculus.Divergence
import CompactSVGD.ForMathlib.Analysis.Convex.TotallyBounded
import CompactSVGD.ForMathlib.Analysis.InnerProductSpace.PiL2
import CompactSVGD.ForMathlib.Analysis.InnerProductSpace.UnitBall
import CompactSVGD.ForMathlib.Analysis.ODE.Linear
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Basic
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.FirstVariation
import CompactSVGD.ForMathlib.MeasureTheory.Function.LocallyIntegrable
import CompactSVGD.ForMathlib.MeasureTheory.Integral.Map
import CompactSVGD.ForMathlib.MeasureTheory.Measure.Map
import CompactSVGD.ForMathlib.MeasureTheory.Measure.WithDensity
import CompactSVGD.ForMathlib.Topology.ContinuousMap.Bounded.Causal
import CompactSVGD.ForMathlib.Topology.Order.Gluing
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.ContinuousMap.Weierstrass

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
  kernel (`k(x, y) = ⟪Φ x, Φ y⟫` with an admissible feature map `Φ`). Every result takes this single
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
  InformationTheory.ae_mem_of_klDiv_ne_top hS.isCompact.measurableSet
    (hS.target.eq_withDensity ▸ hKL)

/-- The flow of a bounded continuous curve of `𝓗` keeps the measures carried by `Ω` on `Ω`. -/
private theorem StandingAssumptions.ae_map_trajectory_mem
    (hS : StandingAssumptions Ω π p s Φ K C) (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ω) (t : ℝ) :
    ∀ᵐ y ∂μ.map (trajectory Φ m 0 · t), y ∈ Ω :=
  SVGD.ae_map_trajectory_mem hm hmB hS.kernel.lipschitzWith hS.isCompact.measurableSet
    hS.kernel.eq_zero_of_mem_frontier hμ 0 t

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
    ∫ x, steinOperator s φ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (p x)) = 0 := by
  -- Integrating against `p · μ` multiplies the integrand by `p`, and the integral of `∇ · (p φ)`
  -- vanishes because `φ` is in the Stein class of `p`.
  rw [integral_withDensity_eq_integral_toReal_smul₀ hp.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top), ← hφS.2.2]
  -- `p 𝒜_s φ = p ∇ log p ᵀ φ + p ∇ · φ = ∇ p ᵀ φ + p ∇ · φ = ∇ · (p φ)`.
  refine integral_congr_ae ?_
  filter_upwards [hp₀, hs, hφ] with x hx₀ hx hφx
  rw [ENNReal.toReal_ofReal hx₀, smul_eq_mul, divergence_smul_of_hasFDerivAt_self_smul hx hφx,
    steinOperator]

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
  Real.iSup_nonneg fun _ ↦ sq_nonneg _

/-- **The reproducing property** (Appendix A.2.3 of [Serre2025]). For `f ∈ 𝓗`, the reproducing
properties `fᵢ(x) = ⟪fᵢ, k(·, x)⟫` and `∂ᵢ fᵢ(x) = ⟪fᵢ, ∂ᵢ k(·, x)⟫` give
`𝒜_π f (x) = ⟪f, ξ_x⟫_𝓗`. -/
theorem reproducing_property {x : EuclideanSpace ℝ (Fin d)} (hΦ : DifferentiableAt ℝ Φ x)
    (f : 𝓗[d, H₀]) : steinOperator s (toVectorField Φ f) x = ⟪f, steinFeature Φ s x⟫ := by
  have hv : toVectorField Φ f x = ∑ i, ⟪f i, Φ x⟫ • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [steinOperator, divergence_euclideanSpace,
    (hasFDerivAt_toVectorField hΦ.hasFDerivAt).fderiv, hv, map_sum, PiLp.inner_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [steinFeature, inner_add_right, inner_smul_right, real_inner_comm, mul_comm]

/-! ### Lemma A.6: regularity of `ξ` -/

section KSD

variable (hS : StandingAssumptions Ω π p s Φ K C)
include hS

/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): `x ↦ ξ_x` is uniformly continuous from `Ω`
to `𝓗`. -/
theorem xi_regularity_uniformContinuousOn : UniformContinuousOn (steinFeature Φ s) Ω := by
  -- The components `s x eᵢ • Φ x + ∂ᵢ Φ x` of `ξ_x` are continuous on `Ω`, which is compact.
  refine hS.isCompact.uniformContinuousOn_of_continuous
    ((PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun _ ↦ ?_))
  exact ((hS.target.continuousOn_score.clm_apply continuousOn_const).smul
    hS.kernel.contDiff.continuous.continuousOn).add
      ((hS.kernel.contDiff.continuous_fderiv one_ne_zero).continuousOn.clm_apply continuousOn_const)

/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): `B = max_{x ∈ Ω} ‖ξ_x‖_𝓗` is finite. -/
theorem xi_regularity_exists_bound : ∃ B, ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B :=
  hS.isCompact.exists_bound_of_continuousOn (xi_regularity_uniformContinuousOn hS).continuousOn

/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): for every finite measure `ν` on `Ω`,
`φ*_ν = ∫_Ω ξ_x dν(x)` is well defined in `𝓗`. -/
theorem xi_regularity_integrable [IsFiniteMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) :
    Integrable (steinFeature Φ s) ν :=
  (xi_regularity_uniformContinuousOn hS).continuousOn.integrable_of_ae_mem hS.isCompact hν

omit hS in
/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): `‖φ*_ν‖_𝓗 ≤ B` for every `ν ∈ 𝒫(Ω)`, where
`B` bounds `‖ξ_x‖_𝓗` on `Ω`. -/
theorem xi_regularity_norm_direction_le {B : ℝ} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) : ‖direction Φ s ν‖ ≤ B := by
  simpa [direction] using norm_integral_le_of_norm_le_const (hν.mono hB)

/-- **Regularity of `ξ`** (Lemma A.6 of [Serre2025]): `‖φ*_ν(y)‖₂ ≤ B C` for every `ν ∈ 𝒫(Ω)` and
every `y`, where `B` bounds `‖ξ_x‖_𝓗` on `Ω` and `C` bounds `‖k(·, y)‖_{H₀} = ‖Φ y‖`. -/
theorem xi_regularity_norm_direction_apply_le {B : ℝ≥0}
    (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B) [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω)
    (y : EuclideanSpace ℝ (Fin d)) : ‖toVectorField Φ (direction Φ s ν) y‖ ≤ B * C :=
  norm_toVectorField_le_of_le hS.kernel.norm_le (xi_regularity_norm_direction_le hB hν) y

/-- **Continuity of the Stein operator** (Appendix A.2.3 of [Serre2025]): for `f ∈ 𝓗`, `𝒜_π f` is
continuous on `Ω`. -/
theorem continuousOn_steinOperator (f : 𝓗[d, H₀]) :
    ContinuousOn (steinOperator s (toVectorField Φ f)) Ω :=
  (continuousOn_const.inner (xi_regularity_uniformContinuousOn hS).continuousOn).congr
    fun x _ ↦ reproducing_property (hS.kernel.contDiff.differentiable one_ne_zero x) f

/-! ### Theorem A.7: the steepest trajectory -/

section SteepestTrajectory

variable [CompleteSpace H₀] [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω)
include hμ

/-- **The steepest trajectory** (Theorem A.7 of [Serre2025]): for every `μ ∈ 𝒫(Ω)` and `f ∈ 𝓗`,
`E_{x ∼ μ}[𝒜_π f (x)] = ⟪f, φ*_μ⟫_𝓗`. -/
theorem steepest_trajectory_integral (f : 𝓗[d, H₀]) :
    ∫ x, steinOperator s (toVectorField Φ f) x ∂μ = ⟪f, direction Φ s μ⟫ := by
  -- By the reproducing property, `𝒜_π f (x) = ⟪f, ξ_x⟫`, and the integral commutes with `⟪f, ·⟫`.
  rw [direction, ← integral_inner (xi_regularity_integrable hS hμ) f]
  exact integral_congr_ae (.of_forall fun x ↦
    reproducing_property (hS.kernel.contDiff.differentiable one_ne_zero x) f)

/-- **The steepest trajectory** (Theorem A.7 of [Serre2025]): `φ*_μ / ‖φ*_μ‖_𝓗` maximizes
`f ↦ E_{x ∼ μ}[𝒜_π f (x)]` on the unit ball of `𝓗`. -/
theorem steepest_trajectory_isMaxOn :
    IsMaxOn (fun f : 𝓗[d, H₀] ↦ ∫ x, steinOperator s (toVectorField Φ f) x ∂μ)
      (closedBall 0 1) (‖direction Φ s μ‖⁻¹ • direction Φ s μ) := by
  -- By the first part and the Cauchy–Schwarz inequality.
  simpa only [steepest_trajectory_integral hS hμ] using isMaxOn_inner_closedBall _

/-- **The steepest trajectory** (Theorem A.7 of [Serre2025]):
`𝔎(μ ∣ π) = ‖φ*_μ‖²_𝓗`. -/
theorem steepest_trajectory_ksd : 𝔎[Φ, s] μ = ‖direction Φ s μ‖ ^ 2 := by
  simp only [kernelSteinDiscrepancy, steepest_trajectory_integral hS hμ]
  exact iSup_closedBall_inner_sq _

/-- **The steepest trajectory** (Theorem A.7 of [Serre2025]):
`𝔎(μ ∣ π) = E_{x ∼ μ}[𝒜_π φ*_μ (x)]`. -/
theorem steepest_trajectory_ksd_eq_integral :
    𝔎[Φ, s] μ = ∫ x, steinOperator s (toVectorField Φ (direction Φ s μ)) x ∂μ := by
  rw [steepest_trajectory_ksd hS hμ, steepest_trajectory_integral hS hμ, real_inner_self_eq_norm_sq]

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
      (-⟪f, direction Φ s μ⟫) 0 := by
  obtain ⟨hπ, -, hp, hpc, hp₀, hs, hsc⟩ := hS.target
  have hμ : ∀ᵐ x ∂μ, x ∈ Ω := hS.ae_mem hKL
  subst hπ
  -- The general first variation formula gives `-E_μ[𝒜_π f]`, which is `-⟪f, φ*_μ⟫` by Theorem A.7.
  have := hasDerivAt_toReal_klDiv_map_add_smul
    (lipschitzWith_toVectorField hS.kernel.lipschitzWith f) hS.isCompact hp hpc
    hp₀ hs hsc ((pairing f).contDiff.comp hS.kernel.contDiff)
    (fun y hy ↦ toVectorField_eq_zero_of_eq_zero (hS.kernel.eq_zero_of_mem_frontier y hy)) hKL
  have hA : ∫ x, (s x (toVectorField Φ f x) + divergence ℝ (toVectorField Φ f) x) ∂μ =
      ⟪f, direction Φ s μ⟫ :=
    steepest_trajectory_integral hS hμ f
  rwa [hA] at this

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): the first variation of
`KL(· ‖ π)` at `μ` is the linear form `f ↦ -⟪f, φ*_μ⟫_𝓗`. -/
theorem kl_steepest_descent_eq_inner (f : 𝓗[d, H₀]) :
    klFirstVariation Φ π μ f = -⟪f, direction Φ s μ⟫ :=
  (kl_steepest_descent_hasDerivAt hS hKL f).deriv

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): on the unit ball of `𝓗`,
the first variation of `KL(· ‖ π)` at `μ` is minimized at `φ*_μ / ‖φ*_μ‖_𝓗`. -/
theorem kl_steepest_descent_isMinOn :
    IsMinOn (klFirstVariation Φ π μ) (closedBall 0 1)
      (‖direction Φ s μ‖⁻¹ • direction Φ s μ) := fun f hf ↦ by
  change klFirstVariation Φ π μ _ ≤ klFirstVariation Φ π μ f
  rw [kl_steepest_descent_eq_inner hS hKL, kl_steepest_descent_eq_inner hS hKL,
    inner_inv_norm_smul_self, neg_le_neg_iff]
  exact inner_le_norm_of_mem_closedBall hf

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): if `φ*_μ ≠ 0`, then
`φ*_μ / ‖φ*_μ‖_𝓗` is the only minimizer of the first variation of `KL(· ‖ π)` at `μ` on the unit
ball of `𝓗`. -/
theorem kl_steepest_descent_eq (hφ : direction Φ s μ ≠ 0) {f : 𝓗[d, H₀]}
    (hf : f ∈ closedBall 0 1)
    (hmin : klFirstVariation Φ π μ f =
      klFirstVariation Φ π μ (‖direction Φ s μ‖⁻¹ • direction Φ s μ)) :
    f = ‖direction Φ s μ‖⁻¹ • direction Φ s μ := by
  rw [kl_steepest_descent_eq_inner hS hKL, kl_steepest_descent_eq_inner hS hKL,
    inner_inv_norm_smul_self, neg_inj] at hmin
  exact eq_inv_norm_smul_of_inner_eq_norm hφ hf hmin

/-- **The KL steepest descent trajectory** (Theorem A.8 of [Serre2025]): along `φ*_μ`,
`∇_ε KL((I_d + ε φ*_μ)#μ ‖ π)|_{ε=0} = -𝔎(μ ∣ π)`. -/
theorem kl_steepest_descent_direction :
    klFirstVariation Φ π μ (direction Φ s μ) = -𝔎[Φ, s] μ := by
  rw [kl_steepest_descent_eq_inner hS hKL, real_inner_self_eq_norm_sq,
    steepest_trajectory_ksd hS (hS.ae_mem hKL)]

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
theorem continuous_meanFieldCurve : Continuous (meanFieldCurve Φ s μ) := by
  rw [meanFieldCurve]
  split_ifs with h
  exacts [h.choose_spec.1, continuous_const]

/-- The mean-field SVGD curve is bounded. -/
theorem exists_norm_meanFieldCurve_le : ∃ B : ℝ≥0, ∀ t, ‖meanFieldCurve Φ s μ t‖ ≤ B := by
  rw [meanFieldCurve]
  split_ifs with h
  exacts [h.choose_spec.2.1, ⟨0, fun _ ↦ by simp⟩]

/-- **The mean-field SVGD flow starts at the identity**: `T_0 = I_d`. -/
theorem meanFieldFlow_zero (hS : StandingAssumptions Ω π p s Φ K C) (x : EuclideanSpace ℝ (Fin d)) :
    meanFieldFlow Φ s μ 0 x = x :=
  have ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  trajectory_self continuous_meanFieldCurve hmB hS.kernel.lipschitzWith 0 x

/-- **The mean-field SVGD flow maps are homeomorphisms of `Ω`.** -/
theorem exists_homeomorph_meanFieldFlow (hS : StandingAssumptions Ω π p s Φ K C) (t : ℝ) :
    ∃ e : Ω ≃ₜ Ω, ∀ x : Ω, (e x : EuclideanSpace ℝ (Fin d)) = meanFieldFlow Φ s μ t x :=
  have ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  exists_homeomorph_trajectory continuous_meanFieldCurve hmB hS.kernel.lipschitzWith
    hS.kernel.eq_zero_of_mem_frontier 0 t

section MeanFieldFlow

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
include hS

/-- The closed convex hull of `ξ(Ω)` is compact. -/
private theorem isCompact_closedConvexHull_steinFeature :
    IsCompact (closedConvexHull ℝ (steinFeature Φ s '' Ω)) :=
  (hS.isCompact.image_of_continuousOn
    (xi_regularity_uniformContinuousOn hS).continuousOn).closedConvexHull

/-- For every `ν ∈ 𝒫(Ω)`, `φ*_ν` lies in the closed convex hull of `ξ(Ω)`. -/
private theorem direction_mem_closedConvexHull [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) :
    direction Φ s ν ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω) :=
  (convex_closedConvexHull).integral_mem isClosed_closedConvexHull
    (hν.mono fun _ hx ↦ subset_closedConvexHull (mem_image_of_mem _ hx))
    (xi_regularity_integrable hS hν)

/-- The closed convex hull of `ξ(Ω)` is bounded. -/
private theorem exists_norm_le_closedConvexHull_steinFeature :
    ∃ B : ℝ≥0, ∀ h ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω), ‖h‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedConvexHull_steinFeature hS).isBounded.exists_norm_le
  exact ⟨B.toNNReal, fun h hh ↦ (hB h hh).trans (Real.le_coe_toNNReal B)⟩

/-- **Existence of a solution of the mean-field SVGD equation on a compact time interval.** Under
the standing assumptions, for every `ν ∈ 𝒫(Ω)` and every `a ≤ b`, there is a continuous curve `m`
with values in the closed convex hull of `ξ(Ω)` such that `m t = φ*_{(Xₜ)#ν}` for `t ∈ [a, b]`,
where `Xₜ = trajectory Φ m a · t`. -/
private theorem exists_meanField_Icc [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ m : ℝ → 𝓗[d, H₀], Continuous m ∧ (∀ t, m t ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω)) ∧
      ∀ t ∈ Icc a b, m t = direction Φ s (ν.map (trajectory Φ m a · t)) := by
  have hΦ := hS.kernel
  have hΩ := hS.isCompact
  set 𝒦 := closedConvexHull ℝ (steinFeature Φ s '' Ω)
  obtain ⟨B, hB⟩ := exists_norm_le_closedConvexHull_steinFeature hS
  have h𝒦 : IsCompact 𝒦 := isCompact_closedConvexHull_steinFeature hS
  classical
  have hΩne : Ω.Nonempty := hν.exists
  -- The set `S` of bounded continuous curves on `[a, b]` with values in `𝒦`.
  set S : Set (Icc a b →ᵇ 𝓗[d, H₀]) := {g | ∀ t, g t ∈ 𝒦}
  -- Curves of `S`, extended to `ℝ`, satisfy the assumptions on trajectories.
  have hext {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) :
      Continuous (IccExtend hab ⇑g) ∧ ∀ τ, ‖IccExtend hab (⇑g) τ‖ ≤ B :=
    ⟨g.continuous.Icc_extend', fun τ ↦ hB _ (hg _)⟩
  have htraj {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) (t : ℝ) :
      Continuous (trajectory Φ (IccExtend hab ⇑g) a · t) ∧
        MapsTo (trajectory Φ (IccExtend hab ⇑g) a · t) Ω Ω :=
    ⟨continuous_trajectory_apply (hext hg).1 (hext hg).2 hΦ.lipschitzWith a t,
      fun _ hx ↦ trajectory_mem (hext hg).1 (hext hg).2 hΦ.lipschitzWith
        hΦ.eq_zero_of_mem_frontier hx t⟩
  -- The fixed-point map, on raw functions.
  let F (g : Icc a b →ᵇ 𝓗[d, H₀]) (t : Icc a b) : 𝓗[d, H₀] :=
    direction Φ s (ν.map (trajectory Φ (IccExtend hab ⇑g) a · t))
  have hFS {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) (t : Icc a b) : F g t ∈ 𝒦 :=
    direction_mem_closedConvexHull hS (ae_map_trajectory_mem (hext hg).1 (hext hg).2
      hΦ.lipschitzWith hΩ.measurableSet hΦ.eq_zero_of_mem_frontier hν a t)
  -- Uniform continuity of `ξ` on `Ω`.
  have hξ := Metric.uniformContinuousOn_iff.1 (xi_regularity_uniformContinuousOn hS)
  -- Equicontinuity of the images.
  have hequi : ∀ ε > 0, ∃ δ > 0, ∀ g ∈ S, ∀ t t' : Icc a b, dist t t' < δ →
      dist (F g t) (F g t') < ε := fun ε hε ↦ by
    obtain ⟨δ, hδ, h⟩ := exists_dist_integral_map_trajectory_lt hΩ hΦ.lipschitzWith hΦ.norm_le
      hΦ.eq_zero_of_mem_frontier (xi_regularity_uniformContinuousOn hS) hν B hε
    exact ⟨δ, hδ, fun g hg t t' htt' ↦ h _ (hext hg).1 (hext hg).2 a t t' htt'⟩
  have hFc {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) : Continuous (F g) :=
    Metric.continuous_iff.2 fun t ε hε ↦ by
      obtain ⟨δ, hδ, hδF⟩ := hequi ε hε
      exact ⟨δ, hδ, fun t' ht' ↦ hδF g hg t' t ht'⟩
  -- The fixed-point map on bounded continuous curves.
  let G (g : Icc a b →ᵇ 𝓗[d, H₀]) : Icc a b →ᵇ 𝓗[d, H₀] :=
    if hg : g ∈ S then BoundedContinuousFunction.mkOfCompact ⟨F g, hFc hg⟩ else g
  have hG {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) (t : Icc a b) : G g t = F g t := by
    simp [G, hg]
  have hGS : MapsTo G S S := fun g hg t ↦ by
    rw [hG hg]
    exact hFS hg t
  -- Continuity of the fixed-point map on `S`.
  have hGc : ContinuousOn G S := by
    refine Metric.continuousOn_iff.2 fun g hg ε hε ↦ ?_
    obtain ⟨η, hη, hηξ⟩ := hξ (ε / 2) (half_pos hε)
    have hgr : Tendsto (fun δ ↦ gronwallBound 0 (B * K) (C * δ) (b - a)) (𝓝 0) (𝓝 0) := by
      have := ((gronwallBound_continuous_ε 0 (B * K) (b - a)).comp
        (continuous_const_mul (C : ℝ))).tendsto 0
      simpa [gronwallBound_ε0, Function.comp_def] using this
    obtain ⟨δ, hδ, hδgr⟩ := Metric.tendsto_nhds_nhds.1 hgr η hη
    refine ⟨δ, hδ, fun g' hg' hgg' ↦ ?_⟩
    refine ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun t ↦ ?_).trans_lt
      (half_lt_self hε)
    rw [hG hg', hG hg]
    refine MeasureTheory.dist_integral_map_le hΩ (xi_regularity_uniformContinuousOn hS).continuousOn
      hν (htraj hg' t).1 (htraj hg t).1 (htraj hg' t).2 (htraj hg t).2
      (fun x hx y hy hxy ↦ (hηξ x hx y hy hxy).le) fun x _ ↦ ?_
    calc dist (trajectory Φ (IccExtend hab ⇑g') a x t) (trajectory Φ (IccExtend hab ⇑g) a x t)
      _ ≤ gronwallBound 0 (B * K) (C * dist g' g) (t - a) :=
          dist_trajectory_trajectory_le_of_dist_le (hext hg').1 (hext hg').2 hΦ.lipschitzWith
            hΦ.norm_le (hext hg).1 (hext hg).2 t.property.1
            (fun τ _ ↦ BoundedContinuousFunction.dist_coe_le_dist (f := g') (g := g) _) x
      _ ≤ gronwallBound 0 (B * K) (C * dist g' g) (b - a) :=
          gronwallBound_mono le_rfl (by positivity) (by positivity) (by linarith [t.property.2])
      _ < η := (le_abs_self _).trans_lt (by
          simpa [Real.dist_eq] using
            hδgr (by simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hgg'))
  -- `F g τ` only depends on `g` before `τ`, and `F g a = φ*_ν`.
  have hcaus {g g' : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) (hg' : g' ∈ S) {τ : Icc a b}
      (hgg' : ∀ t : Icc a b, t ≤ τ → g t = g' t) : F g τ = F g' τ := by
    have heq : EqOn (IccExtend hab ⇑g) (IccExtend hab ⇑g') (uIcc a τ) := fun t ht ↦ by
      rw [uIcc_of_le τ.property.1] at ht
      have htab : t ∈ Icc a b := ⟨ht.1, ht.2.trans τ.property.2⟩
      rw [IccExtend_of_mem hab _ htab, IccExtend_of_mem hab _ htab]
      exact hgg' ⟨t, htab⟩ (Subtype.coe_le_coe.1 ht.2)
    have htraj : (fun x ↦ trajectory Φ (IccExtend hab ⇑g) a x τ) =
        fun x ↦ trajectory Φ (IccExtend hab ⇑g') a x τ := funext fun x ↦
      trajectory_eq_of_eqOn (hext hg).1 (hext hg).2 hΦ.lipschitzWith (hext hg').1 (hext hg').2
        heq x
    exact congrArg (fun f ↦ direction Φ s (ν.map f)) htraj
  have hF₀ {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) :
      F g ⟨a, left_mem_Icc.2 hab⟩ = direction Φ s ν := by
    have htraj : (fun x ↦ trajectory Φ (IccExtend hab ⇑g) a x a) = id :=
      funext fun x ↦ trajectory_self (hext hg).1 (hext hg).2 hΦ.lipschitzWith a x
    exact (congrArg (fun f ↦ direction Φ s (ν.map f)) htraj).trans (by rw [Measure.map_id])
  -- Tonelli's argument gives a fixed point of `G`.
  obtain ⟨g, hg, hgG⟩ := BoundedContinuousFunction.exists_isFixedPt_of_causal hab h𝒦
    ((hΩne.image _).mono subset_closedConvexHull) hGS hGc
    (Metric.uniformEquicontinuous_iff.2 fun ε hε ↦ (hequi ε hε).imp fun _ ⟨hδ, h⟩ ↦
      ⟨hδ, fun t t' htt' g ↦ by
        simpa only [hG g.property] using h g g.property t t' htt'⟩).equicontinuous
    (fun g g' hg hg' τ hgg' ↦ by rw [hG hg, hG hg']; exact hcaus hg hg' hgg')
    (fun g g' hg hg' ↦ by rw [hG hg, hG hg', hF₀ hg, hF₀ hg'])
  refine ⟨IccExtend hab ⇑g, (hext hg).1, fun τ ↦ hg _, fun t ht ↦ ?_⟩
  rw [IccExtend_of_mem hab _ ht]
  exact (DFunLike.congr_fun hgG _).symm.trans (hG hg ⟨t, ht⟩)

/-- **Existence of a solution of the mean-field SVGD equation on `[0, ∞)`.** Under the standing
assumptions, for every `μ ∈ 𝒫(Ω)`, there is a continuous curve `m` with values in the closed
convex hull of `ξ(Ω)` such that `m t = φ*_{(T_t)#μ}` for every `t ≥ 0`, where
`T_t = trajectory Φ m 0 · t`. -/
theorem exists_meanField [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    ∃ m : ℝ → 𝓗[d, H₀], Continuous m ∧ (∀ t, m t ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω)) ∧
      IsMeanFieldCurve Φ s μ m := by
  set 𝒦 := closedConvexHull ℝ (steinFeature Φ s '' Ω)
  have hΦ := hS.kernel
  have hΩ := hS.isCompact
  obtain ⟨B, hB⟩ := exists_norm_le_closedConvexHull_steinFeature hS
  -- A solution on `[n, n + 1]` from any probability measure concentrated on `Ω`.
  have hstep (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))) :
      ∃ m : ℝ → 𝓗[d, H₀], IsProbabilityMeasure ν →
      (∀ᵐ x ∂ν, x ∈ Ω) → Continuous m ∧ (∀ t, m t ∈ 𝒦) ∧
        ∀ t ∈ Icc (n : ℝ) (n + 1), m t = direction Φ s (ν.map (trajectory Φ m n · t)) := by
    by_cases h : IsProbabilityMeasure ν ∧ ∀ᵐ x ∂ν, x ∈ Ω
    · have := h.1
      obtain ⟨m, hm⟩ := exists_meanField_Icc hS h.2 (show (n : ℝ) ≤ n + 1 by linarith)
      exact ⟨m, fun _ _ ↦ hm⟩
    · exact ⟨0, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩
  choose step hstep using hstep
  -- The measures `νₙ` reached at the integer times, and the curves `mₙ` on `[n, n + 1]`.
  let ν : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun n ↦ Nat.rec μ (fun k νk ↦
    νk.map (trajectory Φ (step k νk) k · (k + 1))) n
  have hν₀ : ν 0 = μ := rfl
  have hνsucc (n : ℕ) : ν (n + 1) = (ν n).map (trajectory Φ (step n (ν n)) n · (n + 1)) := rfl
  let mₙ (n : ℕ) : ℝ → 𝓗[d, H₀] := step n (ν n)
  have hP (n : ℕ) : IsProbabilityMeasure (ν n) ∧ ∀ᵐ x ∂ν n, x ∈ Ω := by
    induction n with
    | zero => exact ⟨hν₀ ▸ inferInstance, hμ⟩
    | succ n ih =>
      have := ih.1
      obtain ⟨hc, hK, -⟩ := hstep n (ν n) ih.1 ih.2
      have hB' : ∀ t, ‖step n (ν n) t‖ ≤ B := fun t ↦ hB _ (hK t)
      rw [hνsucc]
      exact ⟨by infer_instance, ae_map_trajectory_mem hc hB' hΦ.lipschitzWith hΩ.measurableSet
        hΦ.eq_zero_of_mem_frontier ih.2 n (n + 1)⟩
  have hm (n : ℕ) := hstep n (ν n) (hP n).1 (hP n).2
  have hmB (n : ℕ) (t : ℝ) : ‖mₙ n t‖ ≤ B := hB _ ((hm n).2.1 t)
  -- The concatenated curve.
  let M : ℝ → 𝓗[d, H₀] := fun t ↦ mₙ ⌊t⌋₊ t
  have hM (n : ℕ) : EqOn M (mₙ n) (Icc n (n + 1)) := by
    intro t ht
    rcases ht.2.lt_or_eq with hlt | heq
    · have : ⌊t⌋₊ = n := (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans ht.1)).2 ⟨ht.1, hlt⟩
      simp only [M, this]
    · -- At `t = n + 1`, both curves are the update direction of `νₙ₊₁`.
      have hfl : ⌊t⌋₊ = n + 1 := by rw [heq]; exact_mod_cast Nat.floor_natCast (n + 1)
      have h₁ := (hm (n + 1)).2.2 t
        ⟨by rw [heq]; push_cast; linarith, by rw [heq]; push_cast; linarith⟩
      have h₂ := (hm n).2.2 t ⟨ht.1, ht.2⟩
      simp only [M, hfl]
      change step (n + 1) (ν (n + 1)) t = step n (ν n) t
      have hid : (fun x ↦ trajectory Φ (step (n + 1) (ν (n + 1))) ((n + 1 : ℕ) : ℝ) x t) = id := by
        funext x
        rw [heq, ← Nat.cast_succ]
        exact trajectory_self (hm (n + 1)).1 (hmB (n + 1)) hΦ.lipschitzWith _ x
      rw [h₁, h₂, hid, Measure.map_id, hνsucc, heq]
  have hM₀ : EqOn M (mₙ 0) (Iic 1) := by
    intro t ht
    rcases ht.lt_or_eq with hlt | heq
    · simp only [M, Nat.floor_eq_zero.2 hlt]
    · exact hM 0 ⟨by simp [heq], by simp [heq]⟩
  have hMc : Continuous M := continuous_of_eqOn_Icc_nat (fun n ↦ (hm n).1) hM₀ hM
  have hMK (t : ℝ) : M t ∈ 𝒦 := (hm ⌊t⌋₊).2.1 t
  have hMB (t : ℝ) : ‖M t‖ ≤ B := hB _ (hMK t)
  -- On `[n, n + 1]`, `μₜ` is the image of `μₙ` by the flow of `mₙ` from time `n`.
  have hmap (n : ℕ) {t : ℝ} (ht : t ∈ Icc (n : ℝ) (n + 1)) :
      μ.map (trajectory Φ M 0 · t) =
        (μ.map (trajectory Φ M 0 · n)).map (trajectory Φ (mₙ n) n · t) := by
    rw [Measure.map_map
      (continuous_trajectory_apply (hm n).1 (hmB n) hΦ.lipschitzWith n t).measurable
      (continuous_trajectory_apply hMc hMB hΦ.lipschitzWith 0 n).measurable]
    refine congrArg μ.map (funext fun x ↦ ?_)
    exact (congrFun (trajectory_trajectory hMc hMB hΦ.lipschitzWith 0 n x) t).symm.trans
      (trajectory_eq_of_eqOn hMc hMB hΦ.lipschitzWith (hm n).1 (hmB n)
        ((hM n).mono (uIcc_of_le ht.1 ▸ Icc_subset_Icc_right ht.2)) _)
  -- The image of `μ` at the integer times is `νₙ`.
  have hTν (n : ℕ) : μ.map (trajectory Φ M 0 · n) = ν n := by
    induction n with
    | zero =>
      simp only [Nat.cast_zero, trajectory_self hMc hMB hΦ.lipschitzWith]
      exact Measure.map_id
    | succ n ih => rw [Nat.cast_succ, hmap n ⟨by linarith, le_rfl⟩, ih, hνsucc]
  refine ⟨M, hMc, hMK, fun t ht ↦ ?_⟩
  set n := ⌊t⌋₊
  have htn : t ∈ Icc (n : ℝ) (n + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  rw [hM n htn]
  change step n (ν n) t = _
  rw [(hm n).2.2 t htn, hmap n htn, hTν]

variable [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω)
include hμ

/-- **The mean-field SVGD curve solves the mean-field equation.** Under the standing assumptions,
for `μ ∈ 𝒫(Ω)`, `m t = φ*_{μ_t}` for every `t ≥ 0`, where `m = SVGD.meanFieldCurve Φ s μ` and
`μ_t = (T_t)#μ` along the flow `T_t = SVGD.meanFieldFlow Φ s μ t`. -/
theorem meanFieldCurve_eq_direction {t : ℝ} (ht : 0 ≤ t) :
    meanFieldCurve Φ s μ t = direction Φ s (μ.map (meanFieldFlow Φ s μ t)) := by
  have h : ∃ m : ℝ → 𝓗[d, H₀], Continuous m ∧ (∃ B : ℝ≥0, ∀ t, ‖m t‖ ≤ B) ∧
      IsMeanFieldCurve Φ s μ m := by
    obtain ⟨m, hmc, hmK, hm⟩ := exists_meanField hS hμ
    obtain ⟨B, hB⟩ := exists_norm_le_closedConvexHull_steinFeature hS
    exact ⟨m, hmc, ⟨B, fun t ↦ hB _ (hmK t)⟩, hm⟩
  have hc : meanFieldCurve Φ s μ = h.choose := by rw [meanFieldCurve, dite_eq_left h]
  have := h.choose_spec.2.2 t ht
  rw [← hc] at this
  exact this

/-- **The mean-field SVGD equation.** The particles follow the update direction of their law:
`∂ₜ T_t(x) = φ*_{μ_t}(T_t(x))` for `t ≥ 0`, where `μ_t = (T_t)#μ`. -/
theorem hasDerivAt_meanFieldFlow (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (meanFieldFlow Φ s μ · x)
      (toVectorField Φ (direction Φ s (μ.map (meanFieldFlow Φ s μ t))) (meanFieldFlow Φ s μ t x))
      t := by
  obtain ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  rw [← meanFieldCurve_eq_direction hS hμ ht]
  exact hasDerivAt_trajectory continuous_meanFieldCurve hmB hS.kernel.lipschitzWith 0 x t

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
      (-𝔎[Φ, s] (μ.map (trajectory Φ m 0 · t))) t := by
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := hS.ae_mem hKL
  have hμt := hS.ae_map_trajectory_mem hm hmB hμΩ t
  -- The general dissipation formula gives `d/dt KL(μ_t ‖ π) = -E_{μ_t}[𝒜_π (m t)]`.
  obtain ⟨hπ, -, hp, hpc, hp₀, hs, hsc⟩ := hS.target
  have h : HasDerivAt (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal)
      (-∫ y, steinOperator s (toVectorField Φ (m t)) y ∂(μ.map (trajectory Φ m 0 · t))) t := by
    have := hasDerivAt_toReal_klDiv_map_trajectory hS.isCompact hp hpc hp₀ hS.kernel.contDiff
      hS.kernel.lipschitzWith hS.kernel.eq_zero_of_mem_frontier hm hmB (hπ ▸ hKL) hs hsc t
    rw [← hπ] at this
    exact this
  -- By Theorem A.7, `E_{μ_t}[𝒜_π (m t)] = ⟪m t, φ*_{μ_t}⟫`, and `m t = φ*_{μ_t}`, so this is
  -- `‖φ*_{μ_t}‖² = 𝔎(μ_t ∣ π)`.
  rwa [steepest_trajectory_integral hS hμt, ← hmφ t ht, real_inner_self_eq_norm_sq,
    hmφ t ht, ← steepest_trajectory_ksd hS hμt] at h

/-- **Time derivative of the KL divergence** (Theorem A.11 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` with
`KL(μ ‖ π) < ∞`, and let `μ_t = (T_t)#μ` along the mean-field SVGD flow. Then
`d/dt KL(μ_t ‖ π) = -𝔎(μ_t ∣ π)` for every `t ≥ 0`. -/
theorem time_derivative_kl {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (meanFieldFlow Φ s μ t)) π).toReal)
      (-𝔎[Φ, s] (μ.map (meanFieldFlow Φ s μ t))) t :=
  have ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  time_derivative_kl' hS hKL continuous_meanFieldCurve hmB
    (fun _ ↦ meanFieldCurve_eq_direction hS (hS.ae_mem hKL)) ht

/-- **Time derivative of the KL divergence**, for every solution of the mean-field equation (Theorem
A.11 of [Serre2025]). Let `m` be a continuous bounded solution of the mean-field equation from `μ`
(`SVGD.IsMeanFieldCurve Φ s μ m`), with flow `T_t = trajectory Φ m 0 · t`, and let `μ_t = (T_t)#μ`.
If `KL(μ ‖ π) < ∞`, then `t ↦ KL(μ_t ‖ π)` is non-increasing on `[0, ∞)`, as `𝔎(μ_t ∣ π) ≥ 0`. -/
theorem time_derivative_kl_antitoneOn' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hmφ : IsMeanFieldCurve Φ s μ m) :
    AntitoneOn (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal) (Ici 0) := by
  have hderiv {t : ℝ} (ht : 0 ≤ t) := time_derivative_kl' hS hKL hm hmB hmφ ht
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun t ht ↦ (hderiv ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv (interior_subset ht)).differentiableAt.differentiableWithinAt)
    fun t ht ↦ ?_
  rw [(hderiv (interior_subset ht)).deriv, neg_nonpos]
  exact ksd_nonneg _

/-- **Time derivative of the KL divergence** (Theorem A.11 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` with
`KL(μ ‖ π) < ∞`. As `𝔎(μ_t ∣ π) ≥ 0`, the Kullback–Leibler divergence `KL(μ_t ‖ π)` is
non-increasing along the mean-field SVGD flow. -/
theorem time_derivative_kl_antitoneOn :
    AntitoneOn (fun t ↦ (klDiv (μ.map (meanFieldFlow Φ s μ t)) π).toReal) (Ici 0) :=
  have ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  time_derivative_kl_antitoneOn' hS hKL continuous_meanFieldCurve hmB
    (fun _ ↦ meanFieldCurve_eq_direction hS (hS.ae_mem hKL))

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
theorem ksd_valid_discrepancy : ν = π ↔ 𝔎[Φ, s] ν = 0 := by
  have := hS.target.isProbabilityMeasure
  have hπ : ∀ᵐ x ∂π, x ∈ Ω :=
    hS.target.eq_withDensity ▸ ae_withDensity_restrict_mem hS.isCompact.measurableSet _
  -- `⟹`: `𝔎(π ∣ π) = 0`, by Theorem A.8 at `μ = π`. The map `ε ↦ KL((I_d + ε φ*_π)#π ‖ π)` is
  -- nonnegative and vanishes at `0`, so its derivative `-‖φ*_π‖²` at `0` vanishes. Stein's
  -- identity would also give the result, but it requires `φ*_π` to be in the Stein class of `π`.
  have hself : 𝔎[Φ, s] π = 0 := by
    have hKL : klDiv π π ≠ ∞ := by simp
    set φ := direction Φ s π
    have hmin : IsLocalMin
        (fun ε : ℝ ↦ (klDiv (π.map fun x ↦ x + ε • toVectorField Φ φ x) π).toReal) 0 :=
      Filter.Eventually.of_forall fun ε ↦ by simp
    have h₀ := hmin.hasDerivAt_eq_zero (kl_steepest_descent_hasDerivAt hS hKL φ)
    rw [steepest_trajectory_ksd hS hπ, ← real_inner_self_eq_norm_sq]
    linarith
  refine ⟨fun h ↦ h ▸ hself, fun hK ↦ ?_⟩
  -- `⟸`. By Theorem A.7, `𝔎(ρ ∣ π) = ‖φ*_ρ‖²` and `E_ρ[𝒜_π f] = ⟪f, φ*_ρ⟫` for `ρ ∈ 𝒫(Ω)`.
  -- Hence, if `|g - 𝒜_π f - c| ≤ ε` on `Ω` and `𝔎(ρ ∣ π) = 0`, then
  -- `|E_ρ[g] - c| = |E_ρ[g - 𝒜_π f - c]| ≤ ε`.
  have : CompactSpace Ω := isCompact_iff_compactSpace.1 hS.isCompact
  have hclose {ρ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ρ]
      (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) (hKρ : 𝔎[Φ, s] ρ = 0)
      (g : EuclideanSpace ℝ (Fin d) →ᵇ ℝ) (f : 𝓗[d, H₀]) {c ε : ℝ}
      (hfc : ∀ x ∈ Ω, |g x - steinOperator s (toVectorField Φ f) x - c| ≤ ε) :
      |∫ x, g x ∂ρ - c| ≤ ε := by
    rw [steepest_trajectory_ksd hS hρ, sq_eq_zero_iff, norm_eq_zero] at hKρ
    have h₀ : ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ = 0 := by
      rw [steepest_trajectory_integral hS hρ, hKρ, inner_zero_right]
    have hgi : Integrable (fun x ↦ g x) ρ := g.integrable ρ
    have hAi : Integrable (fun x ↦ steinOperator s (toVectorField Φ f) x) ρ :=
      (continuousOn_steinOperator hS f).integrable_of_ae_mem hS.isCompact hρ
    have hsub : ∫ x, g x ∂ρ - c =
        ∫ x, (g x - steinOperator s (toVectorField Φ f) x - c) ∂ρ := by
      rw [integral_sub (f := fun x ↦ g x - steinOperator s (toVectorField Φ f) x)
        (hgi.sub hAi) (integrable_const c), integral_sub hgi hAi, h₀, integral_const]
      simp
    rw [hsub, ← Real.norm_eq_abs]
    exact (norm_integral_le_of_norm_le_const (C := ε)
      (hρ.mono fun x hx ↦ by simpa [Real.norm_eq_abs] using hfc x hx)).trans (by simp)
  -- Let `g` be bounded continuous and `ε > 0`. By Stein-universality, some `𝒜_π f + c` is
  -- `ε / 2`-close to `g` on `Ω`. As `𝔎(ν ∣ π) = 𝔎(π ∣ π) = 0`, `|E_ν[g] - E_π[g]| ≤ ε`.
  have key (g : EuclideanSpace ℝ (Fin d) →ᵇ ℝ) : ∫ x, g x ∂ν = ∫ x, g x ∂π :=
    eq_of_forall_dist_le fun ε hε ↦ by
      obtain ⟨φ, ⟨f, c, hφ⟩, hdist⟩ :=
        hU.exists_dist_lt ((g : C(EuclideanSpace ℝ (Fin d), ℝ)).restrict Ω) (half_pos hε)
      have hfc (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Ω) :
          |g x - steinOperator s (toVectorField Φ f) x - c| ≤ ε / 2 := by
        have := (ContinuousMap.dist_apply_le_dist ⟨x, hx⟩).trans hdist.le
        simpa [hφ, Real.dist_eq, sub_add_eq_sub_sub] using this
      calc dist (∫ x, g x ∂ν) (∫ x, g x ∂π) ≤ |∫ x, g x ∂ν - c| + |∫ x, g x ∂π - c| := by
            rw [Real.dist_eq, abs_sub_comm (∫ x, g x ∂π)]
            exact abs_sub_le _ _ _
        _ ≤ ε / 2 + ε / 2 := add_le_add (hclose hν hK g f hfc) (hclose hπ hself g f hfc)
        _ = ε := add_halves ε
  -- Two finite measures with the same integrals of bounded continuous functions are equal.
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure key

end KSDValidDiscrepancy

/-! ### Theorem 3.1: weak convergence of SVGD -/

section WeakConvergence

variable (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure μ]
include hS

/-- **Uniform continuity of the KSD**, for every continuous bounded curve (Lemma B.4 of
[Serre2025]). Let `m` be a continuous curve bounded by `B`, with flow `T_t = trajectory Φ m 0 · t`,
and let `μ ∈ 𝒫(Ω)` and `μ_t = (T_t)#μ`. Then `t ↦ 𝔎(μ_t ∣ π)` is uniformly continuous on `ℝ`. -/
theorem ksd_uniform_continuity' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B) (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    UniformContinuous fun t ↦ 𝔎[Φ, s] (μ.map (trajectory Φ m 0 · t)) := by
  have hK := hS.kernel
  obtain ⟨D, hD⟩ := xi_regularity_exists_bound hS
  have hμt (t : ℝ) := hS.ae_map_trajectory_mem hm hmB hμ t
  -- Steps 1 and 2: the trajectories are `B C`-Lipschitz in time, and `ξ` is uniformly
  -- continuous on `Ω` (Lemma A.6), so `t ↦ φ*_{μ_t} = ∫ ξ_{T_t x} dμ(x)` is uniformly continuous.
  have hφ : UniformContinuous fun t ↦ direction Φ s (μ.map (trajectory Φ m 0 · t)) :=
    Metric.uniformContinuous_iff.2 fun _ hε ↦
      (exists_dist_integral_map_trajectory_lt hS.isCompact hK.lipschitzWith hK.norm_le
        hK.eq_zero_of_mem_frontier (xi_regularity_uniformContinuousOn hS) hμ B hε).imp
        fun _ ⟨hδ, h⟩ ↦ ⟨hδ, fun {_ _} ↦ h m hm hmB 0 _ _⟩
  -- Step 3: `𝔎(μ_t ∣ π) = ‖φ*_{μ_t}‖²` (Theorem A.7), and `x ↦ ‖x‖²` is uniformly continuous on the
  -- ball of radius `D`, which contains every `φ*_{μ_t}` (Lemma A.6).
  have heq : (fun t ↦ ‖direction Φ s (μ.map (trajectory Φ m 0 · t))‖ ^ 2) =
      fun t ↦ 𝔎[Φ, s] (μ.map (trajectory Φ m 0 · t)) :=
    funext fun t ↦ (steepest_trajectory_ksd hS (hμt t)).symm
  rw [← heq, ← uniformContinuousOn_univ]
  exact (isCompact_Icc.uniformContinuousOn_of_continuous (continuous_pow 2).continuousOn).comp
    (uniformContinuous_norm.comp hφ).uniformContinuousOn
    fun t _ ↦ ⟨norm_nonneg _, xi_regularity_norm_direction_le hD (hμt t)⟩

/-- **Uniform continuity of the KSD** (Lemma B.4 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` and let
`μ_t = (T_t)#μ` along the mean-field SVGD flow. Then `t ↦ 𝔎(μ_t ∣ π)` is uniformly continuous. -/
theorem ksd_uniform_continuity (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    UniformContinuous fun t ↦ 𝔎[Φ, s] (μ.map (meanFieldFlow Φ s μ t)) :=
  have ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  ksd_uniform_continuity' hS continuous_meanFieldCurve hmB hμ

variable (hKL : klDiv μ π ≠ ∞)
include hKL

/-- **Convergence of the KSD**, for every solution of the mean-field equation (Corollary B.5 of
[Serre2025]). Let `m` be a continuous bounded solution of the mean-field equation from `μ`
(`SVGD.IsMeanFieldCurve Φ s μ m`), with flow `T_t = trajectory Φ m 0 · t`, and let `μ_t = (T_t)#μ`.
If `KL(μ ‖ π) < ∞`, then `𝔎(μ_t ∣ π) → 0` as `t → ∞`. -/
theorem ksd_convergence' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hmφ : IsMeanFieldCurve Φ s μ m) :
    Tendsto (fun t ↦ 𝔎[Φ, s] (μ.map (trajectory Φ m 0 · t))) atTop (𝓝 0) := by
  have hμ : ∀ᵐ x ∂μ, x ∈ Ω := hS.ae_mem hKL
  -- `F(t) = KL(μ_t ‖ π) ≥ 0` has derivative `-g(t) = -𝔎(μ_t ∣ π)` (Theorem A.11), and `g ≥ 0` is
  -- uniformly continuous (Lemma B.4). Barbalat's lemma gives `g(t) → 0`.
  refine tendsto_zero_of_hasDerivWithinAt_neg_of_uniformContinuousOn (a := 0) (c := 0)
    (fun t ht ↦ (time_derivative_kl' hS hKL hm hmB hmφ ht).hasDerivWithinAt)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (fun _ _ ↦ ksd_nonneg _)
    (ksd_uniform_continuity' hS hm hmB hμ).uniformContinuousOn

/-- **Convergence of the KSD** (Corollary B.5 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` with `KL(μ ‖ π) < ∞`.
Along the mean-field SVGD flow, `𝔎(μ_t ∣ π) → 0` as `t → ∞`. -/
theorem ksd_convergence :
    Tendsto (fun t ↦ 𝔎[Φ, s] (μ.map (meanFieldFlow Φ s μ t))) atTop (𝓝 0) :=
  have ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  ksd_convergence' hS hKL continuous_meanFieldCurve hmB
    (fun _ ↦ meanFieldCurve_eq_direction hS (hS.ae_mem hKL))

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
    𝔎[Φ, s] ν = 0 := by
  have hμ : ∀ᵐ x ∂μ, x ∈ Ω := hS.ae_mem hKL
  have hμt (τ : ℝ) := hS.ae_map_trajectory_mem hm hmB hμ τ
  set φ := direction Φ s ν
  -- We compute the limit of `a_n = ⟪φ*_ν, φ*_{μ_{t_n}}⟫` in two ways.
  -- First limit: by Theorem A.7, `a_n = E_{μ_{t_n}}[𝒜_π φ*_ν]`, and `𝒜_π φ*_ν` is continuous on
  -- `Ω`, so `a_n → E_ν[𝒜_π φ*_ν] = ⟪φ*_ν, φ*_ν⟫ = ‖φ*_ν‖²`.
  have hA (n : ℕ) : ∫ x, steinOperator s (toVectorField Φ φ) x ∂μ.map (trajectory Φ m 0 · (t n)) =
      ⟪φ, direction Φ s (μ.map (trajectory Φ m 0 · (t n)))⟫ :=
    steepest_trajectory_integral hS (hμt (t n)) φ
  have h₁ : Tendsto (fun n ↦ ⟪φ, direction Φ s (μ.map (trajectory Φ m 0 · (t n)))⟫) atTop
      (𝓝 (‖φ‖ ^ 2)) := by
    have := hconv _ (continuousOn_steinOperator hS φ)
    rwa [funext hA, steepest_trajectory_integral hS hν, real_inner_self_eq_norm_sq] at this
  -- Second limit: `|a_n| ≤ ‖φ*_ν‖ ‖φ*_{μ_{t_n}}‖ = ‖φ*_ν‖ 𝔎(μ_{t_n} ∣ π)^{1/2} → 0` by
  -- Corollary B.5.
  have hφt : Tendsto (fun τ ↦ direction Φ s (μ.map (trajectory Φ m 0 · τ))) atTop (𝓝 0) := by
    have hsq : Tendsto (fun τ ↦ ‖direction Φ s (μ.map (trajectory Φ m 0 · τ))‖ ^ 2) atTop (𝓝 0) :=
      (ksd_convergence' hS hKL hm hmB hmφ).congr fun τ ↦ steepest_trajectory_ksd hS (hμt τ)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  have h₂ :
      Tendsto (fun n ↦ ⟪φ, direction Φ s (μ.map (trajectory Φ m 0 · (t n)))⟫) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := φ)).inner (hφt.comp ht)
  -- By uniqueness of the limit, `𝔎(ν ∣ π) = ‖φ*_ν‖² = 0`.
  rw [steepest_trajectory_ksd hS hν]
  exact tendsto_nhds_unique h₁ h₂

/-- **Cluster points** (Lemma B.6 of [Serre2025]). Let `μ ∈ 𝒫(Ω)` with `KL(μ ‖ π) < ∞`, and let
`μ_t = (T_t)#μ` along the mean-field SVGD flow. Let `ν ∈ 𝒫(Ω)` and `t_n → ∞` be such that
`μ_{t_n} ⇀ ν`, i.e. `E_{μ_{t_n}}[g] → E_ν[g]` for every `g` continuous on `Ω`. Then `𝔎(ν ∣ π) = 0`.
-/
theorem cluster_points {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Ω)
    (hconv : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω →
      Tendsto (fun n ↦ ∫ x, g x ∂μ.map (meanFieldFlow Φ s μ (t n))) atTop (𝓝 (∫ x, g x ∂ν))) :
    𝔎[Φ, s] ν = 0 :=
  have ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  cluster_points' hS hKL continuous_meanFieldCurve hmB
    (fun _ ↦ meanFieldCurve_eq_direction hS (hS.ae_mem hKL)) ht hν hconv

/-- **Weak convergence of SVGD**, for every solution of the mean-field equation (Theorem 3.1 of
[Serre2025]). Under the standing assumptions, let the kernel be Stein-universal. Let `m` be a
continuous bounded solution of the mean-field equation from `μ` (`SVGD.IsMeanFieldCurve Φ s μ m`),
with flow `T_t = trajectory Φ m 0 · t`, and let `μ_t = (T_t)#μ`. If `KL(μ ‖ π) < ∞`, then `μ_t ⇀ π`:
for every `g` continuous on `Ω`, `E_{μ_t}[g] → E_π[g]` as `t → ∞`. -/
theorem weak_convergence' (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
    (hmφ : IsMeanFieldCurve Φ s μ m)
    (hU : IsSteinUniversal Φ s Ω) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ContinuousOn g Ω) :
    Tendsto (fun t ↦ ∫ x, g x ∂μ.map (trajectory Φ m 0 · t)) atTop (𝓝 (∫ x, g x ∂π)) := by
  have : CompactSpace Ω := isCompact_iff_compactSpace.1 hS.isCompact
  have hι := MeasurableEmbedding.subtypeVal hS.isCompact.measurableSet
  have hμ : ∀ᵐ x ∂μ, x ∈ Ω := hS.ae_mem hKL
  -- The measures `μ_t` are probability measures `u t` on `Ω`, as the flow maps are homeomorphisms
  -- of `Ω`.
  have hcomap : (μ.comap ((↑) : Ω → EuclideanSpace ℝ (Fin d))).map (↑) = μ := by
    rw [map_comap_subtypeVal hS.isCompact.measurableSet, Measure.restrict_eq_self_of_ae_mem hμ]
  have : IsProbabilityMeasure (μ.comap ((↑) : Ω → EuclideanSpace ℝ (Fin d))) :=
    hι.isProbabilityMeasure_comap (by rwa [Subtype.range_coe])
  choose T hT using fun t ↦ exists_homeomorph_trajectory hm hmB hS.kernel.lipschitzWith
    hS.kernel.eq_zero_of_mem_frontier 0 t
  set u : ℝ → ProbabilityMeasure Ω := fun t ↦ ⟨(μ.comap (↑)).map (T t), inferInstance⟩
  have hu (t : ℝ) : (u t : Measure Ω).map (↑) = μ.map (trajectory Φ m 0 · t) := by
    have hTt : (↑) ∘ T t = (trajectory Φ m 0 · t) ∘ ((↑) : Ω → EuclideanSpace ℝ (Fin d)) :=
      funext (hT t)
    rw [ProbabilityMeasure.coe_mk, Measure.map_map continuous_subtypeVal.measurable
      (T t).continuous.measurable, hTt, ← Measure.map_map
      (continuous_trajectory_apply hm hmB hS.kernel.lipschitzWith 0 t).measurable
      continuous_subtypeVal.measurable, hcomap]
  -- Weak convergence in `𝒫(Ω)` gives the convergence of `E[g]` for every `g` continuous on `Ω`.
  have hweak {ρ : ℕ → ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω}
      (hρ : Tendsto ρ atTop (𝓝 ν)) (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : ContinuousOn g Ω) :
      Tendsto (fun n ↦ ∫ x, g x ∂(ρ n : Measure Ω).map (↑)) atTop
        (𝓝 (∫ x, g x ∂(ν : Measure Ω).map (↑))) := by
    have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hρ
      (BoundedContinuousFunction.mkOfCompact ⟨Ω.domRestrict g, hg.domRestrict⟩)
    simp only [hι.integral_map]
    exact this
  -- It is enough that every sequence `t_n → ∞` has a subsequence along which
  -- `E_{μ_t}[g] → E_π[g]`.
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  -- By Prokhorov's theorem (`𝒫(Ω)` is compact and metrizable), `(u (t_n))` has a weakly convergent
  -- subsequence, with limit `ν`.
  obtain ⟨ν, -, ψ, hψ, hlim⟩ := isCompact_univ.tendsto_subseq (x := fun n ↦ u (ns n))
    fun _ ↦ mem_univ _
  -- Its limit has a null KSD (Lemma B.6), hence is `π` (Proposition 3.2).
  have hνπ : (ν : Measure Ω).map (↑) = π := by
    refine (ksd_valid_discrepancy hS hU (ae_map_subtypeVal_mem hS.isCompact.measurableSet)).2
      (cluster_points' hS hKL hm hmB hmφ (hns.comp hψ.tendsto_atTop)
        (ae_map_subtypeVal_mem hS.isCompact.measurableSet) fun g hg ↦ ?_)
    simpa only [Function.comp_def, hu] using hweak hlim g hg
  exact ⟨ψ, by simpa only [Function.comp_def, hu, hνπ] using hweak hlim g hg⟩

/-- **Weak convergence of SVGD** (Theorem 3.1 of [Serre2025]). Under the standing assumptions, let
the kernel be Stein-universal and let `μ ∈ 𝒫(Ω)` with `KL(μ ‖ π) < ∞`. Along the mean-field SVGD
flow, `μ_t = (T_t)#μ` converges weakly to `π`: for every `g` continuous on `Ω`,
`E_{μ_t}[g] → E_π[g]` as `t → ∞`. -/
theorem weak_convergence (hU : IsSteinUniversal Φ s Ω) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hg : ContinuousOn g Ω) :
    Tendsto (fun t ↦ ∫ x, g x ∂μ.map (meanFieldFlow Φ s μ t)) atTop (𝓝 (∫ x, g x ∂π)) :=
  have ⟨_, hmB⟩ := exists_norm_meanFieldCurve_le (Φ := Φ) (s := s) (μ := μ)
  weak_convergence' hS hKL continuous_meanFieldCurve hmB
    (fun _ ↦ meanFieldCurve_eq_direction hS (hS.ae_mem hKL)) hU g hg

end WeakConvergence

end SVGD

/-! ## A Stein-universal kernel on `[-1, 1]`

This section is not in [Serre2025]. It builds a kernel that satisfies all the hypotheses of
Theorem 3.1 in dimension `1`, on `Ω = [-1, 1]` (`closedBall 0 1`), for every admissible target.

The kernel is `k(x, y) = χ(x) χ(y) ∑ₙ wₙ² Rₙ(x) Rₙ(y)`, with the feature map
`SVGD.intervalFeatureMap : y ↦ (wₙ χ(y) Rₙ(y))ₙ ∈ ℓ²(ℕ, ℝ)` of `SVGD.seqFeatureMap`. The polynomial
`Rₙ` (`SVGD.intervalPoly n`) is the primitive of `tⁿ - mₙ` that vanishes at `-1` and `1`. Thus it is
a multiple of `w(t) = 1 - t²`, and `k` is a weighted kernel `w(x) w(y) k₀(x, y)` on `Ω`. The cutoff
`χ` (`SVGD.intervalCutoff`) equals `1` on `[-2, 2]`. It makes the feature map bounded and Lipschitz
on `ℝ`, and the weights `wₙ > 0` make it `C¹`. As the `Rₙ` vanish at `±1`, so does the feature
map (`SVGD.admissibleFeatureMap_intervalFeatureMap`).

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
the kernel `k(x, y) = χ(x) χ(y) ∑ₙ wₙ² Rₙ(x) Rₙ(y)` on `ℝ`, where `χ = SVGD.intervalCutoff`,
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
  intervalCutoff.one_of_mem_closedBall <| by
    rwa [mem_closedBall, Real.dist_eq, sub_zero, intervalCutoff_rIn]

private theorem intervalPoly_neg_one (n : ℕ) : intervalPoly n (-1) = 0 := by
  simp [intervalPoly]

private theorem intervalPoly_one (n : ℕ) : intervalPoly n 1 = 0 := by
  rw [intervalPoly]
  field_simp
  ring

private theorem hasDerivAt_intervalPoly (n : ℕ) (t : ℝ) :
    HasDerivAt (intervalPoly n) (t ^ n - (1 - (-1) ^ (n + 1)) / (2 * (n + 1))) t := by
  have h₁ : HasDerivAt (fun t : ℝ ↦ (t ^ (n + 1) - (-1) ^ (n + 1)) / (n + 1)) (t ^ n) t := by
    convert ((hasDerivAt_pow (n + 1) t).sub_const ((-1 : ℝ) ^ (n + 1))).div_const
      ((n : ℝ) + 1) using 1
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  have h₂ := ((hasDerivAt_id t).add_const 1).const_mul ((1 - (-1 : ℝ) ^ (n + 1)) / (2 * (n + 1)))
  rw [mul_one] at h₂
  exact h₁.sub h₂

private theorem contDiff_intervalCutoff_mul (n : ℕ) :
    ContDiff ℝ 1 fun t ↦ intervalCutoff t * intervalPoly n t :=
  intervalCutoff.contDiff.mul (by unfold intervalPoly; fun_prop)

private theorem bddAbove_intervalCutoff_mul (n : ℕ) :
    BddAbove (range fun t ↦ ‖intervalCutoff t * intervalPoly n t‖ +
      ‖fderiv ℝ (fun t ↦ intervalCutoff t * intervalPoly n t) t‖) := by
  have hc : HasCompactSupport fun t ↦ intervalCutoff t * intervalPoly n t :=
    intervalCutoff.hasCompactSupport.mul_right
  have hf := contDiff_intervalCutoff_mul n
  exact (hf.continuous.norm.add (hf.continuous_fderiv one_ne_zero).norm)
    |>.bddAbove_range_of_hasCompactSupport (hc.norm.add (hc.fderiv ℝ).norm)

/-- **The kernel of `SVGD.intervalFeatureMap` is admissible** on `Ω = [-1, 1]`: its feature map is
`C¹`, `2`-Lipschitz, bounded by `2`, and vanishes at `±1`. -/
theorem admissibleFeatureMap_intervalFeatureMap :
    AdmissibleFeatureMap intervalFeatureMap (closedBall 0 1) 2 2 := by
  refine ⟨(contDiff_seqFeatureMap contDiff_intervalCutoff_mul bddAbove_intervalCutoff_mul).comp
    (by fun_prop : ContDiff ℝ 1 fun y : EuclideanSpace ℝ (Fin 1) ↦ y 0), ?_,
    fun y ↦ norm_seqFeatureMap_le bddAbove_intervalCutoff_mul (y 0), fun y hy ↦ ?_⟩
  · have h : LipschitzWith 1 fun y : EuclideanSpace ℝ (Fin 1) ↦ y 0 :=
      LipschitzWith.of_dist_le_mul fun y z ↦ by
        simpa [dist_eq_norm] using PiLp.norm_apply_le (y - z) 0
    have := (lipschitzWith_seqFeatureMap contDiff_intervalCutoff_mul
      bddAbove_intervalCutoff_mul).comp h
    rwa [mul_one] at this
  · rw [frontier_closedBall 0 one_ne_zero, mem_sphere_zero_iff_norm,
      EuclideanSpace.norm_fin_one, Real.norm_eq_abs] at hy
    refine seqFeatureMap_eq_zero fun n ↦ ?_
    rcases (abs_eq zero_le_one).1 hy with h | h <;> simp [h, intervalPoly_one, intervalPoly_neg_one]

/-- In dimension `1`, if `⟪h, Φ y⟫ = G(y₀)` for every `y`, then the Stein operator of the vector
field of `h` is `𝒜 h (x) = s x (e₀) G(x₀) + G'(x₀)`. -/
private theorem steinOperator_eq_of_inner_eq {H₀ : Type*} [NormedAddCommGroup H₀]
    [InnerProductSpace ℝ H₀] {Φ : EuclideanSpace ℝ (Fin 1) → H₀}
    {s : EuclideanSpace ℝ (Fin 1) → StrongDual ℝ (EuclideanSpace ℝ (Fin 1))} {h : H₀} {G : ℝ → ℝ}
    (hG : Differentiable ℝ G) (hΦ : ∀ y, ⟪h, Φ y⟫ = G (y 0)) (x : EuclideanSpace ℝ (Fin 1)) :
    steinOperator s (toVectorField Φ (WithLp.toLp 2 fun _ ↦ h : 𝓗[1, H₀])) x =
      s x (EuclideanSpace.single 0 1) * G (x 0) + deriv G (x 0) := by
  have hV : toVectorField Φ (WithLp.toLp 2 fun _ ↦ h : 𝓗[1, H₀]) =
      fun y ↦ G (y 0) • EuclideanSpace.single 0 1 := by
    funext y
    ext i
    fin_cases i
    simp [hΦ]
  have h₁ : HasDerivAt G (deriv G (x 0)) (EuclideanSpace.proj (0 : Fin 1) x) :=
    (hG (x 0)).hasDerivAt
  have h₂ :=
    (h₁.comp_hasFDerivAt x (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt).smul_const
      (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))
  have hd : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 1) ↦
      G (y 0) • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))) x =
      (deriv G (x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).smulRight
        (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) :=
    h₂.fderiv
  rw [steinOperator, hV, divergence_euclideanSpace, hd]
  simp [mul_comm]

/-- If `f(-1) = f(1) = 0` and `f' = e - m` with `|e| ≤ δ` on `[-1, 1]`, then `|m| ≤ δ`. -/
private theorem abs_le_of_hasDerivAt_sub {f e : ℝ → ℝ} {m δ : ℝ}
    (hf : ∀ t, HasDerivAt f (e t - m) t) (he : Continuous e) (ha : f (-1) = 0) (hb : f 1 = 0)
    (heδ : ∀ t ∈ Icc (-1 : ℝ) 1, |e t| ≤ δ) : |m| ≤ δ := by
  -- `∫₋₁¹ (e - m) = f(1) - f(-1) = 0`, so `2 m = ∫₋₁¹ e`, and `|∫₋₁¹ e| ≤ 2 δ`.
  have h₁ : ∫ τ in (-1)..1, (e τ - m) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ ↦ hf τ)
      ((he.sub continuous_const).intervalIntegrable _ _), ha, hb, sub_zero]
  rw [intervalIntegral.integral_sub (he.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at h₁
  have h₂ : ‖∫ τ in (-1)..1, e τ‖ ≤ δ * |1 - (-1)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ ↦ by
      rw [uIoc_of_le (by norm_num)] at hτ
      exact (Real.norm_eq_abs _).trans_le (heδ τ (Ioc_subset_Icc_self hτ))
  have h₃ : ∫ τ in (-1)..1, e τ = 2 * m := by
    norm_num at h₁
    linarith
  rw [h₃, Real.norm_eq_abs, abs_mul] at h₂
  norm_num at h₂
  linarith

/-- If `f(-1) = f(1) = 0` and `f' = e - m` with `|e| ≤ δ` on `[-1, 1]`, then `|f| ≤ 4 δ` on
`[-1, 1]`. -/
private theorem abs_apply_le_of_hasDerivAt_sub {f e : ℝ → ℝ} {m δ : ℝ}
    (hf : ∀ t, HasDerivAt f (e t - m) t) (he : Continuous e) (ha : f (-1) = 0) (hb : f 1 = 0)
    (heδ : ∀ t ∈ Icc (-1 : ℝ) 1, |e t| ≤ δ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    |f t| ≤ 4 * δ := by
  have hm := abs_le_of_hasDerivAt_sub hf he ha hb heδ
  -- `f(t) = ∫₋₁ᵗ (e - m)`, with `|e - m| ≤ 2 δ` on `[-1, t]`.
  have hint : ∫ τ in (-1)..t, (e τ - m) = f t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ ↦ hf τ)
      ((he.sub continuous_const).intervalIntegrable _ _), ha, sub_zero]
  rw [← hint, ← Real.norm_eq_abs]
  calc ‖∫ τ in (-1)..t, (e τ - m)‖ ≤ 2 * δ * |t - (-1)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ ↦ by
          rw [uIoc_of_le ht.1] at hτ
          rw [Real.norm_eq_abs]
          exact (abs_sub _ _).trans (by linarith [heδ τ ⟨hτ.1.le, hτ.2.trans ht.2⟩])
    _ ≤ 2 * δ * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith [abs_nonneg m])
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
    _ = 4 * δ := by ring

/-- **The kernel of `SVGD.intervalFeatureMap` is Stein-universal** on `Ω = [-1, 1]`, for every
score `s` continuous on `Ω`. -/
theorem isSteinUniversal_intervalFeatureMap
    {s : EuclideanSpace ℝ (Fin 1) → StrongDual ℝ (EuclideanSpace ℝ (Fin 1))}
    (hs : ContinuousOn s (closedBall 0 1)) :
    IsSteinUniversal intervalFeatureMap s (closedBall 0 1) := by
  have hp : Continuous fun y : EuclideanSpace ℝ (Fin 1) ↦ y 0 := by fun_prop
  have hΩ {x : EuclideanSpace ℝ (Fin 1)} : x ∈ closedBall 0 1 ↔ x 0 ∈ Icc (-1 : ℝ) 1 := by
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_fin_one, Real.norm_eq_abs, abs_le, mem_Icc]
  -- The map `ι : ℝ → Ω`, `t ↦ ρ(t) e₀`, where `ρ` is the projection of `ℝ` onto `[-1, 1]`.
  have h₁ : (-1 : ℝ) ≤ 1 := by norm_num
  let ι : ℝ → EuclideanSpace ℝ (Fin 1) := fun t ↦
    (projIcc (-1) 1 h₁ t : ℝ) • EuclideanSpace.single 0 1
  have hιΩ (t : ℝ) : ι t ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
    hΩ.2 (by simp [ι])
  have hιc : Continuous ι := (continuous_subtypeVal.comp continuous_projIcc).smul continuous_const
  have hιx {x : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ closedBall 0 1) : ι (x 0) = x := by
    simp [ι, projIcc_of_mem h₁ (hΩ.1 hx), EuclideanSpace.apply_zero_smul_single_fin_one]
  -- The score `σ` and the function `φ'` to approximate, on `ℝ`.
  let σ : ℝ → ℝ := fun t ↦ s (ι t) (EuclideanSpace.single 0 1)
  have hσ : Continuous σ := (hs.comp_continuous hιc hιΩ).clm_apply continuous_const
  refine fun φ ↦ Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  let φ' : ℝ → ℝ := fun t ↦ φ ⟨ι t, hιΩ t⟩
  have hφ' : Continuous φ' := φ.continuous.comp (hιc.subtype_mk hιΩ)
  -- The solution `u` of the Stein equation `σ u + u' = φ' - c` with `u(-1) = u(1) = 0`.
  obtain ⟨c, u, hua, hub, hu⟩ := exists_hasDerivAt_sub_sub_mul hσ hφ' (-1) 1
  let u' : ℝ → ℝ := fun t ↦ φ' t - c - σ t * u t
  have huc : Continuous u := continuous_iff_continuousAt.2 fun t ↦ (hu t).continuousAt
  have hu'c : Continuous u' := (hφ'.sub continuous_const).sub (hσ.mul huc)
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hσ.continuousOn (s := Icc (-1 : ℝ) 1))
  set δ := ε / (2 * (2 + 4 * |S|)) with hδ_def
  have hδ : 0 < δ := by positivity
  -- A polynomial `q` close to `u'` on `[-1, 1]`, and `R = ∑ₙ qₙ Rₙ`, with `R' = q - m`.
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1 u' hu'c.continuousOn δ hδ
  let N := q.natDegree + 1
  let m : ℝ := ∑ n ∈ Finset.range N, q.coeff n * ((1 - (-1) ^ (n + 1)) / (2 * (n + 1)))
  let R : ℝ → ℝ := fun t ↦ ∑ n ∈ Finset.range N, q.coeff n * intervalPoly n t
  have hR (t : ℝ) : HasDerivAt R (q.eval t - m) t := by
    convert HasDerivAt.fun_sum (u := Finset.range N) fun n _ ↦
      (hasDerivAt_intervalPoly n t).const_mul (q.coeff n) using 1
    rw [Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  -- `R - u` vanishes at `±1`, with derivative `(q - u') - m` and `|q - u'| ≤ δ` on `[-1, 1]`.
  -- Thus `|m| ≤ δ` and `|R - u| ≤ 4 δ` on `[-1, 1]`.
  have hD (t : ℝ) : HasDerivAt (fun t ↦ R t - u t) ((q.eval t - u' t) - m) t :=
    ((hR t).sub (hu t)).congr_deriv (by simp only [u']; ring)
  have hDa : R (-1) - u (-1) = 0 := by simp [R, intervalPoly_neg_one, hua]
  have hDb : R 1 - u 1 = 0 := by simp [R, intervalPoly_one, hub]
  have hqδ (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |q.eval t - u' t| ≤ δ := (hq t ht).le
  have hqc : Continuous fun t ↦ q.eval t - u' t := q.continuous.sub hu'c
  have hm : |m| ≤ δ := abs_le_of_hasDerivAt_sub hD hqc hDa hDb hqδ
  -- The element `h` of `ℓ²` with `⟪h, Φ y⟫ = G(y₀)`, where `G = χ R` equals `R` near `[-1, 1]`.
  let G : ℝ → ℝ := fun t ↦ ∑ n ∈ Finset.range N, q.coeff n * (intervalCutoff t * intervalPoly n t)
  obtain ⟨h, hh⟩ :=
    exists_inner_seqFeatureMap_eq bddAbove_intervalCutoff_mul q.coeff (Finset.range N)
  have hGc : ContDiff ℝ 1 G :=
    ContDiff.sum fun n _ ↦ contDiff_const.mul (contDiff_intervalCutoff_mul n)
  have hGR {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : G =ᶠ[𝓝 t] R := by
    filter_upwards [Metric.ball_mem_nhds t one_pos] with τ hτ
    rw [mem_ball, Real.dist_eq, abs_sub_lt_iff] at hτ
    have hχ : intervalCutoff τ = 1 :=
      intervalCutoff_eq_one (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simp [G, R, hχ]
  -- The Stein operator of `f = (h) ∈ 𝓗` is `s e₀ G + G'`.
  set f : 𝓗[1, ℓ²(ℕ, ℝ)] := WithLp.toLp 2 fun _ ↦ h
  have hA (x : EuclideanSpace ℝ (Fin 1)) :
      steinOperator s (toVectorField intervalFeatureMap f) x =
        s x (EuclideanSpace.single 0 1) * G (x 0) + deriv G (x 0) :=
    steinOperator_eq_of_inner_eq (hGc.differentiable one_ne_zero) (fun y ↦ hh (y 0)) x
  have hcont : ContinuousOn (fun x ↦ steinOperator s (toVectorField intervalFeatureMap f) x + c)
      (closedBall 0 1) := by
    simp_rw [hA]
    exact (((hs.clm_apply continuousOn_const).mul (hGc.continuous.comp hp).continuousOn).add
      ((hGc.continuous_deriv le_rfl).comp hp).continuousOn).add continuousOn_const
  refine ⟨⟨_, hcont.domRestrict⟩, ⟨f, c, fun x ↦ rfl⟩, ?_⟩
  -- On `Ω`, `φ - 𝒜 f - c = -((q - u') - m) - σ (R - u)`.
  refine ((ContinuousMap.dist_le (by positivity)).2 fun x ↦ ?_).trans_lt (half_lt_self hε)
  obtain ⟨x, hx⟩ := x
  have ht : x 0 ∈ Icc (-1 : ℝ) 1 := hΩ.1 hx
  have hσt : s x (EuclideanSpace.single 0 1) = σ (x 0) := by
    change _ = s (ι (x 0)) _
    rw [hιx hx]
  have hφt : φ ⟨x, hx⟩ = φ' (x 0) := congrArg φ (Subtype.ext (hιx hx).symm)
  have hσS : |σ (x 0)| ≤ |S| := by
    have := hS _ ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self S)
  have hRu : |R (x 0) - u (x 0)| ≤ 4 * δ := abs_apply_le_of_hasDerivAt_sub hD hqc hDa hDb hqδ ht
  simp only [ContinuousMap.coe_mk, domRestrict_apply, hA, (hGR ht).eq_of_nhds,
    ((hR (x 0)).congr_of_eventuallyEq (hGR ht)).deriv, hσt, hφt, Real.dist_eq]
  calc |φ' (x 0) - (σ (x 0) * R (x 0) + (q.eval (x 0) - m) + c)|
      = |-(q.eval (x 0) - u' (x 0) - m) - σ (x 0) * (R (x 0) - u (x 0))| := by
        congr 1
        simp only [u']
        ring
    _ ≤ |q.eval (x 0) - u' (x 0) - m| + |σ (x 0)| * |R (x 0) - u (x 0)| := by
        rw [← abs_mul, ← abs_neg (q.eval (x 0) - u' (x 0) - m)]
        exact abs_sub _ _
    _ ≤ 2 * δ + |S| * (4 * δ) := by
        gcongr
        exact (abs_sub _ _).trans (by linarith [hqδ _ ht])
    _ = ε / 2 := by
        rw [hδ_def]
        field_simp

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
  weak_convergence ⟨isCompact_closedBall 0 1, hπ, admissibleFeatureMap_intervalFeatureMap⟩ hKL
    (isSteinUniversal_intervalFeatureMap hπ.continuousOn_score) g hg

end SVGD
