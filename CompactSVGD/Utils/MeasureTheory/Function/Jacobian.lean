/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.Module.Determinant

import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Calculus.FDeriv.Measurable

/-!
# Transporting a measure with a density by a diffeomorphism

Let `π = p · vol|_Ω` with `p` positive on `Ω`, for an additive Haar measure `vol` on a
finite-dimensional real normed space. If a measurable equivalence `e` is differentiable on `Ω`,
maps `Ω` onto `Ω` and has a positive Jacobian determinant on `Ω`, then the image of `π` by `e⁻¹`
has density `(p ∘ e) · det De / p` with respect to `π`, by the change of variables formula. No
regularity of `Ω` is needed.

## Main statements

* `MeasureTheory.map_symm_withDensity_eq_withDensity_det_fderiv`: the formula above.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {vol : Measure E} [vol.IsAddHaarMeasure] {Ω : Set E}
  {p : E → ℝ} {e : E ≃ᵐ E}

/-- **The backward transport of a measure with a density.** If `e` is differentiable on `Ω`, maps
`Ω` onto `Ω` and has a positive Jacobian determinant on `Ω`, then the image of `π = p · vol|_Ω` by
`e⁻¹` has density `(p ∘ e) · det De / p` with respect to `π`. -/
theorem map_symm_withDensity_eq_withDensity_det_fderiv (hΩ : MeasurableSet Ω) (hp : Measurable p)
    (hp₀ : ∀ x ∈ Ω, 0 < p x) (he : ∀ x ∈ Ω, DifferentiableAt ℝ e x) (himage : ⇑e '' Ω = Ω)
    (hdet : ∀ x ∈ Ω, 0 < (fderiv ℝ e x).det) :
    ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)).map e.symm =
      ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)).withDensity fun x ↦
        .ofReal (p (e x) * (fderiv ℝ e x).det / p x) := by
  have hw : Measurable fun x ↦ p (e x) * (fderiv ℝ e x).det / p x :=
    ((hp.comp e.measurable).mul (TauCeti.measurable_det_fderiv ℝ e)).div hp
  ext A hA
  have heA : MeasurableSet (⇑e '' A) := e.measurableSet_image.2 hA
  rw [Measure.map_apply e.symm.measurable hA, ← e.image_eq_preimage_symm,
    withDensity_apply _ heA, Measure.restrict_restrict heA,
    withDensity_apply _ hA, setLIntegral_withDensity_eq_setLIntegral_mul _
      hp.ennreal_ofReal hw.ennreal_ofReal hA, Measure.restrict_restrict hA,
    ← himage, ← image_inter e.injective, himage,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul vol (hA.inter hΩ)
      (fun x hx ↦ (he x hx.2).hasFDerivAt.hasFDerivWithinAt) e.injective.injOn]
  refine setLIntegral_congr_fun (hA.inter hΩ) fun x hx ↦ ?_
  simp only [Pi.mul_apply]
  rw [abs_of_pos (hdet x hx.2), ← ENNReal.ofReal_mul (hdet x hx.2).le,
    ← ENNReal.ofReal_mul (hp₀ x hx.2).le, mul_div_cancel₀ _ (hp₀ x hx.2).ne', mul_comm]

end MeasureTheory
