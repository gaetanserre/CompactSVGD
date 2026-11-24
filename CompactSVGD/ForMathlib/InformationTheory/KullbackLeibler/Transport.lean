/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

import CompactSVGD.ForMathlib.Analysis.Calculus.FDeriv.Measurable
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Basic
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Reweighting
import CompactSVGD.ForMathlib.MeasureTheory.Function.Jacobian
import CompactSVGD.ForMathlib.MeasureTheory.Function.LocallyIntegrable
import CompactSVGD.ForMathlib.MeasureTheory.Measure.WithDensity

/-!
# The Kullback–Leibler divergence of a transported measure

Let `π = p · vol|_Ω`, with `Ω` compact and `p` continuous and positive on `Ω`, and let `e` be a
measurable equivalence that is differentiable on `Ω`, maps `Ω` onto `Ω`, and has a positive
Jacobian determinant on `Ω` with `μ`-integrable logarithm. If `KL(μ ‖ π) < ∞`, then
`KL(e#μ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ e - log p + log det De) dμ`. No density is needed for `μ`:
the proof transports `π` backwards instead of `μ` forwards.

## Main statements

* `InformationTheory.klDiv_map_ne_top`: `KL(e#μ ‖ π) < ∞`.
* `InformationTheory.toReal_klDiv_map_eq`: the formula above.
-/

@[expose] public section

open MeasureTheory Set Real

open scoped ENNReal

namespace InformationTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {vol : Measure E} [vol.IsAddHaarMeasure] {Ω : Set E}
  {p : E → ℝ} {e : E ≃ᵐ E}

section KullbackLeibler

variable {μ : Measure E} [IsFiniteMeasure μ] (hΩ : IsCompact Ω) (hp : Measurable p)
  (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x) (he : ∀ x ∈ Ω, DifferentiableAt ℝ e x)
  (himage : ⇑e '' Ω = Ω) (hdet : ∀ x ∈ Ω, 0 < (fderiv ℝ e x).det)
  (hdetμ : Integrable (fun x ↦ log (fderiv ℝ e x).det) μ)
  (hμ : klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞)
include hΩ hp hpc hp₀ he himage hdet hdetμ hμ

/-- The change of variables behind `InformationTheory.toReal_klDiv_map_eq`. Transporting `π`
backwards by `e` reweights it by `w = (p ∘ e) det De / p`, a positive weight with `μ`-integrable
logarithm `log p ∘ e - log p + log det De`. -/
private theorem exists_weight :
    ∃ w : E → ℝ, Measurable w ∧
      (∀ᵐ x ∂(vol.restrict Ω).withDensity fun x ↦ .ofReal (p x), 0 < w x) ∧
      Integrable (fun x ↦ log (w x)) μ ∧
      ((fun x ↦ log (w x)) =ᵐ[μ] fun x ↦ log (p (e x)) - log (p x) + log (fderiv ℝ e x).det) ∧
      ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)).map e.symm =
        ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)).withDensity
          fun x ↦ .ofReal (w x) := by
  set ν := (vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  have hνΩ : ∀ᵐ x ∂ν, x ∈ Ω := ae_withDensity_restrict_mem hΩ.measurableSet _
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := ae_mem_of_klDiv_ne_top hΩ.measurableSet hμ
  have heΩ {x : E} (hx : x ∈ Ω) : e x ∈ Ω := himage ▸ mem_image_of_mem e hx
  -- The weight `w = (p ∘ e) · det De / p`, its measurability and positivity.
  set w : E → ℝ := fun x ↦ p (e x) * (fderiv ℝ e x).det / p x
  have hw₀ {x : E} (hx : x ∈ Ω) : 0 < w x :=
    div_pos (mul_pos (hp₀ _ (heΩ hx)) (hdet x hx)) (hp₀ x hx)
  -- The logarithm of the weight and its integrability.
  have hlogw : (fun x ↦ log (w x)) =ᵐ[μ] fun x ↦ log (p (e x)) - log (p x) +
      log (fderiv ℝ e x).det := by
    filter_upwards [hμΩ] with x hx
    rw [log_div (mul_pos (hp₀ _ (heΩ hx)) (hdet x hx)).ne' (hp₀ x hx).ne',
      log_mul (hp₀ _ (heΩ hx)).ne' (hdet x hx).ne']
    ring
  have hlogp : ContinuousOn (fun x ↦ log (p x)) Ω := hpc.log fun x hx ↦ (hp₀ x hx).ne'
  have hlogpe : ContinuousOn (fun x ↦ log (p (e x))) Ω :=
    hlogp.comp (fun x hx ↦ (he x hx).continuousAt.continuousWithinAt) fun _ hx ↦ heΩ hx
  refine ⟨w, ((hp.comp e.measurable).mul (measurable_det_fderiv ℝ e)).div hp,
    hνΩ.mono fun _ hx ↦ hw₀ hx, (((hlogpe.integrable_of_ae_mem hΩ hμΩ).sub
      (hlogp.integrable_of_ae_mem hΩ hμΩ)).add hdetμ).congr hlogw.symm, hlogw, ?_⟩
  -- Transport `π` backwards, by the change of variables formula.
  exact map_symm_withDensity_eq_withDensity_det_fderiv (vol := vol) hΩ.measurableSet hp hp₀ he
    himage hdet

/-- **The Kullback–Leibler divergence of a transported measure is finite.** Let `π = p · vol|_Ω`,
with `Ω` compact and `p` continuous and positive on `Ω`. Let `e` be a measurable equivalence,
differentiable on `Ω`, mapping `Ω` onto `Ω`, with a positive Jacobian determinant on `Ω` whose
logarithm is `μ`-integrable. If `KL(μ ‖ π) < ∞`, then `KL(e#μ ‖ π) < ∞`. -/
theorem klDiv_map_ne_top :
    klDiv (μ.map e) ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞ := by
  obtain ⟨hμν, hllr⟩ := klDiv_ne_top_iff.1 hμ
  have : IsFiniteMeasure ((vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)) :=
    isFiniteMeasure_withDensity_ofReal (hpc.integrableOn_compact hΩ).hasFiniteIntegral
  obtain ⟨w, hw, hw₀, hlog, -, hνe⟩ := exists_weight hΩ hp hpc hp₀ he himage hdet hdetμ hμ
  rw [e.klDiv_map_left, hνe]
  exact klDiv_withDensity_ofReal_right_ne_top hμν hllr hw.aemeasurable hw₀ hlog

/-- **The Kullback–Leibler divergence of a transported measure.** Let `π = p · vol|_Ω`, with `Ω`
compact and `p` continuous and positive on `Ω`. Let `e` be a measurable equivalence,
differentiable on `Ω`, mapping `Ω` onto `Ω`, with a positive Jacobian determinant on `Ω` whose
logarithm is `μ`-integrable. If `KL(μ ‖ π) < ∞`, then
`KL(e#μ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ e - log p + log det De) dμ`. -/
theorem toReal_klDiv_map_eq :
    (klDiv (μ.map e) ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal =
      (klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal -
        ∫ x, (log (p (e x)) - log (p x) + log (fderiv ℝ e x).det) ∂μ := by
  set ν := (vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  obtain ⟨hμν, hllr⟩ := klDiv_ne_top_iff.1 hμ
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity_ofReal (hpc.integrableOn_compact hΩ).hasFiniteIntegral
  obtain ⟨w, hw, hw₀, hlog, hlogw, hνe⟩ := exists_weight hΩ hp hpc hp₀ he himage hdet hdetμ hμ
  have : IsFiniteMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
    rw [← hνe]
    infer_instance
  have hmass : (ν.withDensity fun x ↦ ENNReal.ofReal (w x)).real univ = ν.real univ := by
    rw [← hνe, measureReal_def, Measure.map_apply e.symm.measurable MeasurableSet.univ,
      preimage_univ, measureReal_def]
  rw [e.klDiv_map_left, hνe, toReal_klDiv_withDensity_ofReal_right hμν hllr hw.aemeasurable hw₀
    hlog, hmass, integral_congr_ae hlogw]
  ring

end KullbackLeibler

end InformationTheory
