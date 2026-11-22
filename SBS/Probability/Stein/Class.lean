/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.MeasureTheory.Integral.DivergenceTheorem.WholeSpace

/-!
# The Stein class of a density

Let `μ` be a measure on a real normed space `E` and let `p : E → ℝ` be a density. The *Stein
class* `steinClass μ p` is the set of vector fields `φ : E → E` such that `p • φ` is
differentiable `μ`-almost everywhere, its divergence is `μ`-integrable, and

  `∫ x, divergence ℝ (p • φ) x ∂μ = 0`.

When `μ` is the Lebesgue measure restricted to a domain `Ω` with a regular boundary, the
divergence theorem turns this integral into the boundary flux `∮_{∂Ω} p φ · n dS`. The last
condition then says that `p φ` has zero flux through `∂Ω`, which is the definition of the Stein
class in [Liu2016] and [Serre2025]. No regularity of `Ω` or of its boundary is assumed here: the
divergence theorem is only used to check that a given field belongs to the Stein class.

By `ProbabilityTheory.mem_steinClass_iff_integral_steinOperator_eq_zero`, the Stein class is the
set of differentiable fields that satisfy the Stein identity, so this definition is the weakest
one for which the Stein identity holds.

## Main definitions

* `ProbabilityTheory.steinClass μ p`: the Stein class of `p` with respect to `μ`, as a
  submodule of `E → E`.

## Main statements

* `ProbabilityTheory.mem_steinClass_of_integrable`: on the whole space, with an additive Haar
  measure, `φ` is in the Stein class as soon as `p • φ` is differentiable and integrable with an
  integrable derivative.
* `ProbabilityTheory.mem_steinClass_restrict_of_tsupport_subset`: the same on a set `Ω`, if
  moreover `tsupport (p • φ) ⊆ Ω`.
* `ProbabilityTheory.mem_steinClass_restrict_of_hasCompactSupport`: compactly supported `C¹`
  fields `p • φ` with `tsupport (p • φ) ⊆ Ω` are in the Stein class of `p` on `Ω`.

## References

* [Q. Liu, J. Lee, M. Jordan, *A Kernelized Stein Discrepancy for Goodness-of-fit Tests*][Liu2016]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025]

## Tags

Stein class, Stein's method, divergence
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E} {p : E → ℝ} {φ : E → E}

/-- The Stein class of the density `p` with respect to the measure `μ`: the vector fields `φ`
such that `p • φ` is differentiable `μ`-almost everywhere, with a `μ`-integrable divergence of
integral `0`. On a regular domain, the last condition says that the flux of `p φ` through the
boundary vanishes. -/
def steinClass (μ : Measure E) (p : E → ℝ) : Submodule ℝ (E → E) where
  carrier := {φ | (∀ᵐ x ∂μ, DifferentiableAt ℝ (p • φ) x) ∧
    Integrable (divergence ℝ (p • φ)) μ ∧ ∫ x, divergence ℝ (p • φ) x ∂μ = 0}
  add_mem' := by
    rintro φ ψ ⟨hφd, hφi, hφ⟩ ⟨hψd, hψi, hψ⟩
    have hd : divergence ℝ (p • (φ + ψ)) =ᵐ[μ] divergence ℝ (p • φ) + divergence ℝ (p • ψ) := by
      filter_upwards [hφd, hψd] with x hx hy
      rw [smul_add, divergence_add hx hy, Pi.add_apply]
    refine ⟨?_, (hφi.add hψi).congr hd.symm, ?_⟩
    · filter_upwards [hφd, hψd] with x hx hy
      rw [smul_add]
      exact hx.add hy
    · rw [integral_congr_ae hd, integral_add' hφi hψi, hφ, hψ, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    rintro c φ ⟨hφd, hφi, hφ⟩
    have hc : p • (c • φ) = c • (p • φ) := smul_comm p c φ
    have hd : divergence ℝ (p • (c • φ)) =ᵐ[μ] fun x ↦ c * divergence ℝ (p • φ) x := by
      filter_upwards [hφd] with x hx
      rw [hc, divergence_const_smul hx]
    refine ⟨?_, (hφi.const_mul c).congr hd.symm, ?_⟩
    · filter_upwards [hφd] with x hx
      rw [hc]
      exact hx.const_smul c
    · rw [integral_congr_ae hd, integral_const_mul, hφ, mul_zero]

theorem mem_steinClass_iff :
    φ ∈ steinClass μ p ↔ (∀ᵐ x ∂μ, DifferentiableAt ℝ (p • φ) x) ∧
      Integrable (divergence ℝ (p • φ)) μ ∧ ∫ x, divergence ℝ (p • φ) x ∂μ = 0 :=
  Iff.rfl

theorem ae_differentiableAt_of_mem_steinClass (hφ : φ ∈ steinClass μ p) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ (p • φ) x :=
  hφ.1

theorem integrable_divergence_of_mem_steinClass (hφ : φ ∈ steinClass μ p) :
    Integrable (divergence ℝ (p • φ)) μ :=
  hφ.2.1

/-- The flux of `p • φ` through the boundary vanishes for `φ` in the Stein class of `p`. -/
theorem integral_divergence_eq_zero_of_mem_steinClass (hφ : φ ∈ steinClass μ p) :
    ∫ x, divergence ℝ (p • φ) x ∂μ = 0 :=
  hφ.2.2

/-! ### Sufficient conditions -/

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]

/-- On the whole space, `φ` is in the Stein class of `p` as soon as `p • φ` is differentiable and
integrable, with an integrable derivative. -/
theorem mem_steinClass_of_integrable (hd : Differentiable ℝ (p • φ)) (hi : Integrable (p • φ) μ)
    (hi' : Integrable (fderiv ℝ (p • φ)) μ) : φ ∈ steinClass μ p :=
  ⟨.of_forall hd, integrable_divergence hi', integral_divergence_eq_zero hd hi hi'⟩

/-- On a set `Ω`, `φ` is in the Stein class of `p` as soon as `p • φ` is differentiable and
integrable with an integrable derivative, and vanishes outside `Ω` together with its derivative,
i.e. `tsupport (p • φ) ⊆ Ω`. -/
theorem mem_steinClass_restrict_of_tsupport_subset {Ω : Set E} (hΩ : tsupport (p • φ) ⊆ Ω)
    (hd : Differentiable ℝ (p • φ)) (hi : Integrable (p • φ) μ)
    (hi' : Integrable (fderiv ℝ (p • φ)) μ) : φ ∈ steinClass (μ.restrict Ω) p :=
  ⟨.of_forall hd, (integrable_divergence hi').integrableOn,
    setIntegral_divergence_eq_zero_of_tsupport_subset hΩ hd hi hi'⟩

/-- A field `φ` such that `p • φ` is `C¹` with compact support in `Ω` is in the Stein class of `p`
on `Ω`. -/
theorem mem_steinClass_restrict_of_hasCompactSupport {Ω : Set E} (hΩ : tsupport (p • φ) ⊆ Ω)
    (hc : HasCompactSupport (p • φ)) (hf : ContDiff ℝ 1 (p • φ)) :
    φ ∈ steinClass (μ.restrict Ω) p :=
  mem_steinClass_restrict_of_tsupport_subset hΩ (hf.differentiable one_ne_zero)
    (hf.continuous.integrable_of_hasCompactSupport hc)
    ((hf.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hc.fderiv ℝ))

end ProbabilityTheory
