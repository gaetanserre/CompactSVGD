/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Kullback–Leibler divergence under transport and reweighting

This file gathers two identities for the Kullback–Leibler divergence of finite measures.

* **Invariance under measurable equivalences** (`InformationTheory.klDiv_map_measurableEquiv`):
  `KL(e#μ ‖ e#ν) = KL(μ ‖ ν)`. It follows from the data processing inequality applied to `e`
  and `e.symm`. Consequently `KL(e#μ ‖ ν) = KL(μ ‖ e⁻¹#ν)`
  (`InformationTheory.klDiv_map_measurableEquiv_left`): transporting the first argument amounts
  to transporting the second one backwards.
* **Reweighting the reference measure** (`InformationTheory.toReal_klDiv_withDensity_right`): for
  a positive weight `w` with `log w` integrable,
  `KL(μ ‖ w • ν) = KL(μ ‖ ν) - ∫ log w dμ + (w • ν)(univ) - ν(univ)`.

Together, they compute the Kullback–Leibler divergence of a transported measure `T#μ` with
respect to `π` when `T⁻¹#π` has a density `w` with respect to `π`, without any density for `μ`.
-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

/-- **The Kullback–Leibler divergence is invariant under measurable equivalences.** -/
theorem klDiv_map_measurableEquiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν e.measurable) ?_
  have := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at this

/-- Transporting the first argument of the Kullback–Leibler divergence by a measurable equivalence
amounts to transporting the second one backwards. -/
theorem klDiv_map_measurableEquiv_left [IsFiniteMeasure μ] {ν : Measure β} [IsFiniteMeasure ν]
    (e : α ≃ᵐ β) : klDiv (μ.map e) ν = klDiv μ (ν.map e.symm) := by
  rw [← klDiv_map_measurableEquiv (ν := ν.map e.symm) e, MeasurableEquiv.map_map_symm]

/-- **Reweighting the reference measure.** If `μ ≪ ν` with an integrable log-likelihood ratio,
and `w` is a positive weight with `log w` integrable against `μ`, then
`KL(μ ‖ w • ν) = KL(μ ‖ ν) - ∫ log w dμ + (w • ν)(univ) - ν(univ)`. -/
theorem toReal_klDiv_withDensity_right [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) {w : α → ℝ} (hw : Measurable w) (hw₀ : ∀ᵐ x ∂ν, 0 < w x)
    (hlog : Integrable (fun x ↦ log (w x)) μ)
    [IsFiniteMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (w x))] :
    (klDiv μ (ν.withDensity fun x ↦ ENNReal.ofReal (w x))).toReal =
      (klDiv μ ν).toReal - ∫ x, log (w x) ∂μ +
        (ν.withDensity fun x ↦ ENNReal.ofReal (w x)).real Set.univ - ν.real Set.univ := by
  set ν' := ν.withDensity fun x ↦ ENNReal.ofReal (w x)
  have hw' : AEMeasurable (fun x ↦ ENNReal.ofReal (w x)) ν := hw.ennreal_ofReal.aemeasurable
  have hne : ∀ᵐ x ∂ν, ENNReal.ofReal (w x) ≠ 0 := hw₀.mono fun x hx ↦ by simp [hx]
  have hμν' : μ ≪ ν' := hμν.trans (withDensity_absolutelyContinuous' hw' hne)
  -- The log-likelihood ratio with respect to `ν'` is `llr μ ν - log w`.
  have hllr : llr μ ν' =ᵐ[μ] fun x ↦ llr μ ν x - log (w x) := by
    filter_upwards [hμν.ae_le (Measure.rnDeriv_withDensity_right μ ν hw' hne
      (.of_forall fun _ ↦ ENNReal.ofReal_ne_top)), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν), hμν.ae_le hw₀] with x hx hpos hlt hwx
    rw [llr, llr, hx, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hwx.le,
      log_mul (inv_ne_zero hwx.ne') (ENNReal.toReal_pos hpos.ne' hlt.ne).ne', log_inv]
    ring
  have h_int' : Integrable (llr μ ν') μ := (h_int.sub hlog).congr hllr.symm
  rw [toReal_klDiv hμν' h_int', toReal_klDiv hμν h_int, integral_congr_ae hllr,
    integral_sub h_int hlog]
  ring

end InformationTheory
