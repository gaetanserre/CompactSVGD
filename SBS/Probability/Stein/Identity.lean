/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import SBS.Probability.Stein.Class
public import SBS.Probability.Stein.Operator

/-!
# Stein's identity

Let `μ` be a measure on a finite-dimensional real normed space `E`, let `p : E → ℝ` be a
nonnegative density and let `ν = μ.withDensity p` be the measure with density `p` with respect to
`μ`. Let `s : E → StrongDual ℝ E` be a score of `p`, i.e. `Dp = p • s` holds `μ`-almost
everywhere. For every vector field `φ` that is differentiable `μ`-almost everywhere, the identity
`p * 𝒜_s φ = div (p • φ)` gives

  `∫ x, 𝒜_s φ x ∂ν = ∫ x, div (p • φ) x ∂μ`.

**Stein's identity** follows: if `φ` is in the Stein class of `p`, then `𝒜_s φ` is `ν`-integrable
and `∫ x, 𝒜_s φ x ∂ν = 0`. Conversely, a field `φ` that satisfies Stein's identity is in the
Stein class.

None of the following is assumed: `μ` being the Lebesgue measure, `ν` being a probability
measure, `p` being positive, or the domain having a regular boundary. A domain `Ω` is handled by
taking `μ = volume.restrict Ω`, and the measure-theoretic condition on the boundary is the one
of `ProbabilityTheory.steinClass`.

## Main statements

* `ProbabilityTheory.integral_steinOperator_withDensity`: `∫ 𝒜_s φ dν = ∫ div (p • φ) dμ`.
* `ProbabilityTheory.integrable_steinOperator_withDensity_iff`: `𝒜_s φ` is `ν`-integrable if and
  only if `div (p • φ)` is `μ`-integrable.
* `ProbabilityTheory.integral_steinOperator_eq_zero`: **Stein's identity**.
* `ProbabilityTheory.mem_steinClass_iff_integral_steinOperator_eq_zero`: the Stein class is the
  set of fields that satisfy Stein's identity.
* `ProbabilityTheory.integral_steinOperator_fderiv_log_eq_zero`: Stein's identity for the
  Stein operator `𝒜_p φ = ⟪∇ log p, φ⟫ + ∇ · φ` of the density `p` itself.

## References

* [C. Stein, *A bound for the error in the normal approximation to the distribution of a sum of
  dependent random variables*][Stein1972]
* [Q. Liu, J. Lee, M. Jordan, *A Kernelized Stein Discrepancy for Goodness-of-fit Tests*][Liu2016]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Lemma A.3

## Tags

Stein identity, Stein's method, Stein operator, Stein class
-/

@[expose] public section

open MeasureTheory Filter Set

open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} {p : E → ℝ} {s : E → StrongDual ℝ E} {φ : E → E}

/-- If `Dp = p • s` and `φ` is differentiable `μ`-almost everywhere, then `p * 𝒜_s φ` and
`div (p • φ)` are `μ`-almost everywhere equal. -/
theorem mul_steinOperator_ae_eq_divergence (hs : ∀ᵐ x ∂μ, HasFDerivAt p (p x • s x) x)
    (hφ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x) :
    (fun x ↦ p x * steinOperator s φ x) =ᵐ[μ] divergence ℝ (p • φ) := by
  filter_upwards [hs, hφ] with x hx hφx
  exact mul_steinOperator_eq_divergence hx hφx

variable (hp : AEMeasurable p μ) (hp₀ : 0 ≤ᵐ[μ] p)
  (hs : ∀ᵐ x ∂μ, HasFDerivAt p (p x • s x) x) (hφ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x)
include hp hp₀ hs hφ

/-- Integrating the Stein operator against `p • μ` amounts to integrating the divergence of
`p • φ` against `μ`. -/
theorem integral_steinOperator_withDensity :
    ∫ x, steinOperator s φ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (p x)) =
      ∫ x, divergence ℝ (p • φ) x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hp.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hp₀, mul_steinOperator_ae_eq_divergence hs hφ] with x hx₀ hx
  rw [ENNReal.toReal_ofReal hx₀, smul_eq_mul, hx]

/-- The Stein operator is integrable against `p • μ` if and only if the divergence of `p • φ` is
integrable against `μ`. -/
theorem integrable_steinOperator_withDensity_iff :
    Integrable (steinOperator s φ) (μ.withDensity fun x ↦ ENNReal.ofReal (p x)) ↔
      Integrable (divergence ℝ (p • φ)) μ := by
  rw [integrable_withDensity_iff_integrable_smul₀' hp.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [hp₀, mul_steinOperator_ae_eq_divergence hs hφ] with x hx₀ hx
  rw [ENNReal.toReal_ofReal hx₀, smul_eq_mul, hx]

/-- The Stein operator of a field in the Stein class is integrable against `p • μ`. -/
theorem integrable_steinOperator (hφS : φ ∈ steinClass μ p) :
    Integrable (steinOperator s φ) (μ.withDensity fun x ↦ ENNReal.ofReal (p x)) :=
  (integrable_steinOperator_withDensity_iff hp hp₀ hs hφ).2
    (integrable_divergence_of_mem_steinClass hφS)

/-- **Stein's identity.** Let `p` be a nonnegative density with score `s`, i.e. `Dp = p • s`
holds `μ`-almost everywhere. If `φ` is differentiable `μ`-almost everywhere and lies in the Stein
class of `p`, then the Stein operator `𝒜_s φ` has zero mean under `p • μ`. -/
theorem integral_steinOperator_eq_zero (hφS : φ ∈ steinClass μ p) :
    ∫ x, steinOperator s φ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (p x)) = 0 := by
  rw [integral_steinOperator_withDensity hp hp₀ hs hφ]
  exact integral_divergence_eq_zero_of_mem_steinClass hφS

/-- The Stein class is exactly the set of fields that satisfy Stein's identity. -/
theorem mem_steinClass_iff_integral_steinOperator_eq_zero :
    φ ∈ steinClass μ p ↔
      Integrable (steinOperator s φ) (μ.withDensity fun x ↦ ENNReal.ofReal (p x)) ∧
        ∫ x, steinOperator s φ x ∂μ.withDensity (fun x ↦ ENNReal.ofReal (p x)) = 0 := by
  rw [integrable_steinOperator_withDensity_iff hp hp₀ hs hφ,
    integral_steinOperator_withDensity hp hp₀ hs hφ]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  filter_upwards [hs, hφ] with x hx hφx
  exact hx.differentiableAt.smul hφx

omit hp₀ hs

/-- **Stein's identity** for the Stein operator `𝒜_p φ = ⟪∇ log p, φ⟫ + ∇ · φ` of a nonnegative
density `p`, whose score is the logarithmic derivative of `p`. Here `p` only needs to be
differentiable `μ`-almost everywhere, and may vanish. -/
theorem integral_steinOperator_fderiv_log_eq_zero (hp_nonneg : 0 ≤ p)
    (hpd : ∀ᵐ x ∂μ, DifferentiableAt ℝ p x) (hφS : φ ∈ steinClass μ p) :
    ∫ x, steinOperator (fun x ↦ fderiv ℝ (fun y ↦ Real.log (p y)) x) φ x
      ∂μ.withDensity (fun x ↦ ENNReal.ofReal (p x)) = 0 := by
  refine integral_steinOperator_eq_zero hp (.of_forall hp_nonneg) ?_ hφ hφS
  filter_upwards [hpd] with x hx
  exact hx.hasFDerivAt_self_smul_fderiv_log_of_eventually_nonneg (.of_forall hp_nonneg)

end ProbabilityTheory
