/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import SBS.Analysis.InnerProductSpace.UnitBall
public import SBS.Probability.SVGD.Basic

/-!
# The kernelized Stein discrepancy and the steepest direction of SVGD

Let `ν` be a measure on `ℝᵈ` such that `x ↦ ξₓ` is `ν`-integrable and `Φ` is differentiable
`ν`-almost everywhere. For `h ∈ 𝓗`, the mean under `ν` of the Stein operator applied to the vector
field of `h` is the inner product of `h` with the update direction `φ*_ν`
(`SVGD.integral_steinOperator_eq_inner`):

  `E_ν[𝒜_s h] = ⟪h, φ*_ν⟫_𝓗`.

The *kernelized Stein discrepancy* `𝔎(ν) = sup_{‖h‖ ≤ 1} E_ν[𝒜_s h]²` measures the largest violation
of Stein's identity over the unit ball of `𝓗` (Definition A.5 of [Serre2025],
`SVGD.kernelSteinDiscrepancy`). By the Cauchy–Schwarz inequality:

* `𝔎(ν) = ‖φ*_ν‖²` (`SVGD.kernelSteinDiscrepancy_eq`);
* `φ*_ν / ‖φ*_ν‖` maximizes `h ↦ E_ν[𝒜_s h]` on the unit ball
  (`SVGD.isMaxOn_integral_steinOperator`), and it is the unique maximizer when `φ*_ν ≠ 0`
  (`SVGD.eq_of_integral_steinOperator_eq`).

This is Theorem A.7 of [Serre2025]: `φ*_ν` is the direction of `𝓗` along which Stein's identity
is most violated, which motivates the SVGD update.

## Main definitions

* `SVGD.kernelSteinDiscrepancy Φ s ν`: the kernelized Stein discrepancy of `ν`.

## Main statements

* `SVGD.integral_steinOperator_eq_inner`: `E_ν[𝒜_s h] = ⟪h, φ*_ν⟫`.
* `SVGD.kernelSteinDiscrepancy_eq`: `𝔎(ν) = ‖φ*_ν‖²`.
* `SVGD.isMaxOn_integral_steinOperator`, `SVGD.eq_of_integral_steinOperator_eq`: `φ*_ν / ‖φ*_ν‖`
  is the unique steepest direction.

## References

* [Q. Liu, J. Lee, M. Jordan, *A Kernelized Stein Discrepancy for Goodness-of-fit Tests*][Liu2016]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Theorem A.7
-/

@[expose] public section

open MeasureTheory Metric

open scoped RealInnerProductSpace

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- The kernelized Stein discrepancy `𝔎(ν) = sup_{‖h‖ ≤ 1} E_ν[𝒜_s h]²`, the largest violation of
Stein's identity over the unit ball of `𝓗`. It equals `‖φ*_ν‖²`
(`SVGD.kernelSteinDiscrepancy_eq`). -/
def kernelSteinDiscrepancy (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⨆ h : closedBall (0 : 𝓗[d, H₀]) 1,
    (∫ x, ProbabilityTheory.steinOperator s (toVectorField Φ h) x ∂ν) ^ 2

variable [CompleteSpace H₀] {Φ : EuclideanSpace ℝ (Fin d) → H₀}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {ν : Measure (EuclideanSpace ℝ (Fin d))}
  (hΦ : ∀ᵐ x ∂ν, DifferentiableAt ℝ Φ x) (hξ : Integrable (steinFeature Φ s) ν)
include hΦ hξ

/-- **The Stein operator in expectation** (Theorem A.7). The mean under `ν` of the Stein operator
applied to the vector field of `h` is `⟪h, φ*_ν⟫`. -/
theorem integral_steinOperator_eq_inner (h : 𝓗[d, H₀]) :
    ∫ x, ProbabilityTheory.steinOperator s (toVectorField Φ h) x ∂ν = ⟪h, direction Φ s ν⟫ := by
  rw [direction, ← integral_inner hξ h]
  refine integral_congr_ae ?_
  filter_upwards [hΦ] with x hx
  exact (inner_steinFeature hx h).symm

/-- **The kernelized Stein discrepancy in closed form** (Theorem A.7): `𝔎(ν) = ‖φ*_ν‖²`. -/
theorem kernelSteinDiscrepancy_eq : kernelSteinDiscrepancy Φ s ν = ‖direction Φ s ν‖ ^ 2 := by
  simp only [kernelSteinDiscrepancy, integral_steinOperator_eq_inner hΦ hξ]
  exact iSup_closedBall_inner_sq _

/-- **The steepest direction** (Theorem A.7). On the unit ball of `𝓗`, `h ↦ E_ν[𝒜_s h]` is
maximized at `φ*_ν / ‖φ*_ν‖`, with maximum `‖φ*_ν‖ = 𝔎(ν)^{1/2}`. -/
theorem isMaxOn_integral_steinOperator :
    IsMaxOn (fun h : 𝓗[d, H₀] ↦ ∫ x, ProbabilityTheory.steinOperator s (toVectorField Φ h) x ∂ν)
      (closedBall 0 1) (‖direction Φ s ν‖⁻¹ • direction Φ s ν) := by
  simpa only [integral_steinOperator_eq_inner hΦ hξ] using isMaxOn_inner_closedBall _

/-- The maximum of `h ↦ E_ν[𝒜_s h]` on the unit ball of `𝓗` is `‖φ*_ν‖`. -/
theorem integral_steinOperator_inv_norm_smul_direction :
    ∫ x, ProbabilityTheory.steinOperator s
      (toVectorField Φ (‖direction Φ s ν‖⁻¹ • direction Φ s ν)) x ∂ν = ‖direction Φ s ν‖ := by
  rw [integral_steinOperator_eq_inner hΦ hξ, inner_inv_norm_smul_self]

/-- **Uniqueness of the steepest direction** (Theorem A.7). If `φ*_ν ≠ 0`, then `φ*_ν / ‖φ*_ν‖` is
the only maximizer of `h ↦ E_ν[𝒜_s h]` on the unit ball of `𝓗`. -/
theorem eq_of_integral_steinOperator_eq (hφ : direction Φ s ν ≠ 0) {h : 𝓗[d, H₀]}
    (hh : h ∈ closedBall 0 1)
    (heq : ∫ x, ProbabilityTheory.steinOperator s (toVectorField Φ h) x ∂ν =
      ‖direction Φ s ν‖) :
    h = ‖direction Φ s ν‖⁻¹ • direction Φ s ν :=
  eq_of_inner_eq_norm hφ hh (by rwa [integral_steinOperator_eq_inner hΦ hξ] at heq)

end SVGD
