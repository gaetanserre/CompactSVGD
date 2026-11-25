/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback–Leibler divergence against a reweighted reference measure

For a positive weight `w` with `log w` integrable, reweighting the reference measure subtracts
`log w` from the log-likelihood ratio, so that
`KL(μ ‖ w • ν) = KL(μ ‖ ν) - ∫ log w dμ + (w • ν)(univ) - ν(univ)`.

## Main statements

* `InformationTheory.toReal_klDiv_withDensity_ofReal_right`: the formula above.
-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {w : α → ℝ}

namespace MeasureTheory

/-- Reweighting the reference measure by a positive weight `w` preserves absolute continuity. -/
theorem Measure.AbsolutelyContinuous.withDensity_ofReal (hμν : μ ≪ ν) (hw : AEMeasurable w ν)
    (hw₀ : ∀ᵐ x ∂ν, 0 < w x) : μ ≪ ν.withDensity fun x ↦ ENNReal.ofReal (w x) :=
  hμν.trans (withDensity_absolutelyContinuous' hw.ennreal_ofReal (by simpa using hw₀))

/-- Reweighting the reference measure by a positive weight `w` subtracts `log w` from the
log-likelihood ratio. -/
theorem llr_withDensity_ofReal_right [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (hw : AEMeasurable w ν) (hw₀ : ∀ᵐ x ∂ν, 0 < w x) :
    llr μ (ν.withDensity fun x ↦ ENNReal.ofReal (w x)) =ᵐ[μ] fun x ↦ llr μ ν x - log (w x) := by
  filter_upwards [hμν.ae_le (Measure.rnDeriv_withDensity_right μ ν hw.ennreal_ofReal
    (hw₀.mono fun x hx ↦ by simp [hx]) (.of_forall fun _ ↦ ENNReal.ofReal_ne_top)),
    Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν), hμν.ae_le hw₀]
    with x hx hpos hlt hwx
  rw [llr, llr, hx, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hwx.le,
    log_mul (inv_ne_zero hwx.ne') (ENNReal.toReal_pos hpos.ne' hlt.ne).ne', log_inv]
  ring

end MeasureTheory

namespace InformationTheory

section Reweighting

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  (hw : AEMeasurable w ν) (hw₀ : ∀ᵐ x ∂ν, 0 < w x) (hlog : Integrable (fun x ↦ log (w x)) μ)
include hμν h_int hw hw₀ hlog

/-- **Reweighting the reference measure keeps the divergence finite.** If `μ ≪ ν` with an
integrable log-likelihood ratio, and `w` is a positive weight with `log w` integrable against `μ`,
then `KL(μ ‖ w • ν) < ∞`. -/
theorem klDiv_withDensity_ofReal_right_ne_top :
    klDiv μ (ν.withDensity fun x ↦ ENNReal.ofReal (w x)) ≠ ∞ :=
  klDiv_ne_top (hμν.withDensity_ofReal hw hw₀)
    ((h_int.sub hlog).congr (llr_withDensity_ofReal_right hμν hw hw₀).symm)

/-- **Reweighting the reference measure.** If `μ ≪ ν` with an integrable log-likelihood ratio,
and `w` is a positive weight with `log w` integrable against `μ`, then
`KL(μ ‖ w • ν) = KL(μ ‖ ν) - ∫ log w dμ + (w • ν)(univ) - ν(univ)`. -/
theorem toReal_klDiv_withDensity_ofReal_right
    [IsFiniteMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (w x))] :
    (klDiv μ (ν.withDensity fun x ↦ ENNReal.ofReal (w x))).toReal =
      (klDiv μ ν).toReal - ∫ x, log (w x) ∂μ +
        (ν.withDensity fun x ↦ ENNReal.ofReal (w x)).real Set.univ - ν.real Set.univ := by
  have hllr := llr_withDensity_ofReal_right hμν hw hw₀
  rw [toReal_klDiv (hμν.withDensity_ofReal hw hw₀) ((h_int.sub hlog).congr hllr.symm),
    toReal_klDiv hμν h_int, integral_congr_ae hllr, integral_sub h_int hlog]
  ring

end Reweighting

end InformationTheory
