/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Probability.SVGD.MeanField
public import SBS.Probability.SVGD.SteinDiscrepancy
public import SBS.Probability.Stein.FirstVariation

/-!
# SVGD is the steepest descent of the Kullback–Leibler divergence

Let `Ω ⊆ ℝᵈ` be compact and let `π = p · λ|_Ω`, where `p` is continuous and positive on `Ω` and
`log p` has derivative `s` in the interior of `Ω`, with `s` continuous on `Ω`. Let `Φ` be an
admissible feature map and let `μ` be a probability measure with `KL(μ ‖ π) < ∞`. Every `h ∈ 𝓗`
defines a perturbation `I + ε h` of the identity, and `SVGD.klFirstVariation Φ π μ h` is the
derivative at `ε = 0` of `ε ↦ KL((I + ε h)#μ ‖ π)`.

This file proves Theorem A.8 of [Serre2025]:

* the first variation is the linear form `h ↦ -⟪h, φ*_μ⟫` (`SVGD.klFirstVariation_eq`);
* on the unit ball of `𝓗`, it is minimized at `φ*_μ / ‖φ*_μ‖` (`SVGD.isMinOn_klFirstVariation`),
  its minimum is `-‖φ*_μ‖ = -𝔎(μ)^{1/2}` (`SVGD.klFirstVariation_inv_norm_smul_direction`), and
  this minimizer is unique when `φ*_μ ≠ 0` (`SVGD.eq_of_klFirstVariation_eq`);
* in the direction `φ*_μ` itself, the first variation is `-𝔎(μ)`
  (`SVGD.klFirstVariation_direction`).

So the update direction `φ*_μ` of SVGD is, up to normalization, the direction of `𝓗` along which
the Kullback–Leibler divergence to the target decreases the fastest. This motivates the SVGD
update `μ ↦ (I + ε φ*_μ)#μ`.

## Main definitions

* `SVGD.klFirstVariation Φ π μ h`: the derivative at `0` of `ε ↦ KL((I + ε h)#μ ‖ π)`.

## Main statements

* `SVGD.hasDerivAt_toReal_klDiv_map_add_smul_toVectorField`: the first variation is `-⟪h, φ*_μ⟫`.
* `SVGD.isMinOn_klFirstVariation`, `SVGD.eq_of_klFirstVariation_eq`: `φ*_μ / ‖φ*_μ‖` is the unique
  steepest descent direction of the Kullback–Leibler divergence in the unit ball of `𝓗`.
* `SVGD.klFirstVariation_direction`: the first variation in the direction `φ*_μ` is `-𝔎(μ)`.

## References

* [Q. Liu, D. Wang, *Stein Variational Gradient Descent*][Liu2016SVGD]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Theorem A.8
-/

@[expose] public section

open MeasureTheory Metric InformationTheory

open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- The first variation of the Kullback–Leibler divergence to `π` at `μ` in the direction
`h ∈ 𝓗`: the derivative at `0` of `ε ↦ KL((I + ε h)#μ ‖ π)`, where `h` acts through its vector
field `toVectorField Φ h`. -/
def klFirstVariation (Φ : EuclideanSpace ℝ (Fin d) → H₀) (π μ : Measure (EuclideanSpace ℝ (Fin d)))
    (h : 𝓗[d, H₀]) : ℝ :=
  deriv (fun ε : ℝ ↦ (klDiv (μ.map fun x ↦ x + ε • toVectorField Φ h x) π).toReal) 0

variable [CompleteSpace H₀] {Φ : EuclideanSpace ℝ (Fin d) → H₀}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {Ω : Set (EuclideanSpace ℝ (Fin d))} {K C : ℝ≥0} {p : EuclideanSpace ℝ (Fin d) → ℝ}
  {π μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
  (hΦ : AdmissibleFeatureMap Φ Ω K C) (hΩ : IsCompact Ω)
  (hπ : π = (volume.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x))
  (hp : Measurable p) (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x)
  (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ Real.log (p y)) (s x) x) (hsc : ContinuousOn s Ω)
  (hμ : klDiv μ π ≠ ∞)
include hΦ hΩ hπ hp hpc hp₀ hs hsc hμ

/-- **The first variation of the Kullback–Leibler divergence along `h ∈ 𝓗`** (Theorem A.8). The
map `ε ↦ KL((I + ε h)#μ ‖ π)` has derivative `-⟪h, φ*_μ⟫` at `0`. -/
theorem hasDerivAt_toReal_klDiv_map_add_smul_toVectorField (h : 𝓗[d, H₀]) :
    HasDerivAt (fun ε : ℝ ↦ (klDiv (μ.map fun x ↦ x + ε • toVectorField Φ h x) π).toReal)
      (-⟪h, direction Φ s μ⟫) 0 := by
  subst hπ
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := ae_mem_of_klDiv_ne_top hΩ.measurableSet hμ
  have hv : ContDiff ℝ 1 (toVectorField Φ h) :=
    (pairing h).contDiff.comp hΦ.contDiff
  have hvK : LipschitzWith (‖h‖₊ * K) (toVectorField Φ h) :=
    lipschitzWith_toVectorField hΦ.lipschitzWith (coe_nnNorm h).ge
  have := hasDerivAt_toReal_klDiv_map_add_smul hvK hΩ hp hpc hp₀ hs hsc hv
    (fun y hy ↦ toVectorField_eq_zero_of_eq_zero (hΦ.eq_zero_of_mem_frontier y hy)) hμ
  rwa [integral_steinOperator_eq_inner (.of_forall (hΦ.contDiff.differentiable one_ne_zero))
    (integrable_steinFeature hΩ hΦ.contDiff hsc hμΩ) h] at this

/-- The first variation of the Kullback–Leibler divergence is the linear form `h ↦ -⟪h, φ*_μ⟫`
(Theorem A.8). -/
theorem klFirstVariation_eq (h : 𝓗[d, H₀]) :
    klFirstVariation Φ π μ h = -⟪h, direction Φ s μ⟫ :=
  (hasDerivAt_toReal_klDiv_map_add_smul_toVectorField hΦ hΩ hπ hp hpc hp₀ hs hsc hμ h).deriv

/-- **SVGD is the steepest descent of the Kullback–Leibler divergence** (Theorem A.8). On the unit
ball of `𝓗`, the first variation of `KL(· ‖ π)` at `μ` is minimized at `φ*_μ / ‖φ*_μ‖`. -/
theorem isMinOn_klFirstVariation :
    IsMinOn (klFirstVariation Φ π μ) (closedBall 0 1)
      (‖direction Φ s μ‖⁻¹ • direction Φ s μ) := fun h hh ↦ by
  change klFirstVariation Φ π μ _ ≤ klFirstVariation Φ π μ h
  rw [klFirstVariation_eq hΦ hΩ hπ hp hpc hp₀ hs hsc hμ,
    klFirstVariation_eq hΦ hΩ hπ hp hpc hp₀ hs hsc hμ, inner_inv_norm_smul_self, neg_le_neg_iff]
  exact inner_le_norm_of_mem_closedBall hh

/-- The minimum of the first variation of `KL(· ‖ π)` at `μ` on the unit ball of `𝓗` is
`-‖φ*_μ‖ = -𝔎(μ)^{1/2}`. -/
theorem klFirstVariation_inv_norm_smul_direction :
    klFirstVariation Φ π μ (‖direction Φ s μ‖⁻¹ • direction Φ s μ) = -‖direction Φ s μ‖ := by
  rw [klFirstVariation_eq hΦ hΩ hπ hp hpc hp₀ hs hsc hμ, inner_inv_norm_smul_self]

/-- **Uniqueness of the steepest descent direction** (Theorem A.8). If `φ*_μ ≠ 0`, then
`φ*_μ / ‖φ*_μ‖` is the only minimizer of the first variation of `KL(· ‖ π)` at `μ` on the unit
ball of `𝓗`. -/
theorem eq_of_klFirstVariation_eq (hφ : direction Φ s μ ≠ 0) {h : 𝓗[d, H₀]}
    (hh : h ∈ closedBall 0 1) (heq : klFirstVariation Φ π μ h = -‖direction Φ s μ‖) :
    h = ‖direction Φ s μ‖⁻¹ • direction Φ s μ := by
  rw [klFirstVariation_eq hΦ hΩ hπ hp hpc hp₀ hs hsc hμ, neg_inj] at heq
  exact eq_of_inner_eq_norm hφ hh heq

/-- **The first variation along the SVGD direction** (Theorem A.8). Along `φ*_μ`, the first
variation of `KL(· ‖ π)` at `μ` is minus the kernelized Stein discrepancy:
`∂ε KL((I + ε φ*_μ)#μ ‖ π)|_{ε=0} = -𝔎(μ)`. -/
theorem klFirstVariation_direction :
    klFirstVariation Φ π μ (direction Φ s μ) = -kernelSteinDiscrepancy Φ s μ := by
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := ae_mem_of_klDiv_ne_top hΩ.measurableSet (hπ ▸ hμ)
  rw [klFirstVariation_eq hΦ hΩ hπ hp hpc hp₀ hs hsc hμ, real_inner_self_eq_norm_sq,
    kernelSteinDiscrepancy_eq (.of_forall (hΦ.contDiff.differentiable one_ne_zero))
      (integrable_steinFeature hΩ hΦ.contDiff hsc hμΩ)]

end SVGD
