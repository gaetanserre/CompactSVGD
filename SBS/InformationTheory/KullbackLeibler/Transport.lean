/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SBS.InformationTheory.KullbackLeibler.Reweighting
public import SBS.MeasureTheory.Function.Jacobian

/-!
# The Kullback–Leibler divergence of a transported measure

Let `E` be a finite-dimensional real normed space with an additive Haar measure `vol`, and let
`π = p · vol|_Ω`, with `Ω` compact and `p` continuous and positive on `Ω`. Let `e : E ≃ᵐ E` be a
measurable equivalence that is differentiable on `Ω`, maps `Ω` onto `Ω`, and has a positive
Jacobian determinant on `Ω`, and let `μ` be a probability measure with `KL(μ ‖ π) < ∞`. If
`log det De` is `μ`-integrable, then `KL(e#μ ‖ π) < ∞` (`InformationTheory.klDiv_map_ne_top`) and

  `KL(e#μ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ e - log p + log det De) dμ`

(`InformationTheory.toReal_klDiv_map_eq`).

No density is needed for `μ`. Transporting `μ` forward amounts to transporting `π` backwards
(`InformationTheory.klDiv_map_measurableEquiv_left`), and `e⁻¹#π` has density
`(p ∘ e) · det De / p` with respect to `π` (`MeasureTheory.map_symm_eq_withDensity`). This formula
computes the Kullback–Leibler divergence along the perturbations `I + ε v` of the identity and
along the flows of vector fields.
-/

@[expose] public section

open MeasureTheory Set Real

open scoped ENNReal

namespace InformationTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {vol : Measure E} [vol.IsAddHaarMeasure] {Ω : Set E}
  {p : E → ℝ} {e : E ≃ᵐ E}

section KullbackLeibler

variable {μ : Measure E} [IsProbabilityMeasure μ] (hΩ : IsCompact Ω) (hp : Measurable p)
  (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x) (he : ∀ x ∈ Ω, DifferentiableAt ℝ e x)
  (himage : ⇑e '' Ω = Ω) (hdet : ∀ x ∈ Ω, 0 < (fderiv ℝ e x).det)
  (hdetμ : Integrable (fun x ↦ log (fderiv ℝ e x).det) μ)
  (hμ : klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞)
include hΩ hp hpc hp₀ he himage hdet hdetμ hμ

/-- The two statements of `InformationTheory.klDiv_map_ne_top` and
`InformationTheory.toReal_klDiv_map_eq`, which share their proof. -/
private theorem klDiv_map_ne_top_and_toReal_eq :
    klDiv (μ.map e) ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞ ∧
      (klDiv (μ.map e) ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal =
        (klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal -
          ∫ x, (log (p (e x)) - log (p x) + log (fderiv ℝ e x).det) ∂μ := by
  set ν := (vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  obtain ⟨hμν, hllr⟩ := klDiv_ne_top_iff.1 hμ
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity_ofReal (hpc.integrableOn_compact hΩ).hasFiniteIntegral
  have hνΩ : ∀ᵐ x ∂ν, x ∈ Ω :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ.measurableSet)
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := ae_mem_of_klDiv_ne_top hΩ.measurableSet hμ
  have heΩ {x : E} (hx : x ∈ Ω) : e x ∈ Ω := himage ▸ mem_image_of_mem e hx
  -- The weight `w = (p ∘ e) · det De / p`, its measurability and positivity.
  set w : E → ℝ := fun x ↦ p (e x) * (fderiv ℝ e x).det / p x
  have hw : Measurable w :=
    ((hp.comp e.measurable).mul (TauCeti.measurable_det_fderiv ℝ e)).div hp
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
  have hint {f : E → ℝ} (hf : ContinuousOn f Ω) : Integrable f μ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hμΩ]
    exact hf.integrableOn_compact hΩ
  have hlog : Integrable (fun x ↦ log (w x)) μ :=
    (((hint (hlogp.comp (fun x hx ↦ (he x hx).continuousAt.continuousWithinAt)
      fun _ hx ↦ heΩ hx)).sub (hint hlogp)).add hdetμ).congr hlogw.symm
  -- Transport the first argument forward, or the second one backwards.
  have hνe := map_symm_eq_withDensity (vol := vol) hΩ.measurableSet hp hp₀ he himage hdet
  have : IsFiniteMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
    rw [← hνe]
    infer_instance
  have hmass : (ν.withDensity fun x ↦ ENNReal.ofReal (w x)).real univ = ν.real univ := by
    rw [← hνe, measureReal_def, Measure.map_apply e.symm.measurable MeasurableSet.univ,
      preimage_univ, measureReal_def]
  have hw₀' : ∀ᵐ x ∂ν, 0 < w x := hνΩ.mono fun _ hx ↦ hw₀ hx
  rw [klDiv_map_measurableEquiv_left, hνe]
  refine ⟨klDiv_withDensity_ofReal_right_ne_top hμν hllr hw hw₀' hlog, ?_⟩
  rw [toReal_klDiv_withDensity_ofReal_right hμν hllr hw hw₀' hlog, hmass,
    integral_congr_ae hlogw]
  ring

/-- **Transport preserves the finiteness of the Kullback–Leibler divergence.** Let
`π = p · vol|_Ω`, with `Ω` compact and `p` continuous and positive on `Ω`. Let `e` be a measurable
equivalence, differentiable on `Ω`, mapping `Ω` onto `Ω`, with a positive Jacobian determinant on
`Ω` whose logarithm is `μ`-integrable. If `KL(μ ‖ π) < ∞`, then `KL(e#μ ‖ π) < ∞`. -/
theorem klDiv_map_ne_top :
    klDiv (μ.map e) ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞ :=
  (klDiv_map_ne_top_and_toReal_eq hΩ hp hpc hp₀ he himage hdet hdetμ hμ).1

/-- **The Kullback–Leibler divergence of a transported measure.** Let `π = p · vol|_Ω`, with `Ω`
compact and `p` continuous and positive on `Ω`. Let `e` be a measurable equivalence,
differentiable on `Ω`, mapping `Ω` onto `Ω`, with a positive Jacobian determinant on `Ω` whose
logarithm is `μ`-integrable. If `KL(μ ‖ π) < ∞`, then
`KL(e#μ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ e - log p + log det De) dμ`. -/
theorem toReal_klDiv_map_eq :
    (klDiv (μ.map e) ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal =
      (klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal -
        ∫ x, (log (p (e x)) - log (p x) + log (fderiv ℝ e x).det) ∂μ :=
  (klDiv_map_ne_top_and_toReal_eq hΩ hp hpc hp₀ he himage hdet hdetμ hμ).2

end KullbackLeibler

end InformationTheory
