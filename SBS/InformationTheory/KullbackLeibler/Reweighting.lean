/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import TauCeti.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback–Leibler divergence under transport and reweighting

This file gathers identities for the Kullback–Leibler divergence of finite measures.

* **Transport.** Transporting the first argument by a measurable equivalence amounts to
  transporting the second one backwards, `KL(e#μ ‖ ν) = KL(μ ‖ e⁻¹#ν)`
  (`InformationTheory.klDiv_map_measurableEquiv_left`). This follows from the invariance
  `KL(e#μ ‖ e#ν) = KL(μ ‖ ν)` (`MeasureTheory.Measure.klDiv_map_measurableEquiv`, in Tau Ceti).
* **Reweighting the reference measure**
  (`InformationTheory.toReal_klDiv_withDensity_ofReal_right`). For a positive weight `w` with
  `log w` integrable, `KL(μ ‖ w • ν) = KL(μ ‖ ν) - ∫ log w dμ + (w • ν)(univ) - ν(univ)`. In
  particular, reweighting preserves the finiteness of the divergence
  (`InformationTheory.klDiv_withDensity_ofReal_right_ne_top`). The underlying identity is
  `llr μ (w • ν) = llr μ ν - log w` (`MeasureTheory.llr_withDensity_ofReal_right`).
* **Support.** A measure at finite divergence from a measure carried by `Ω` is carried by `Ω`
  (`InformationTheory.ae_mem_of_klDiv_ne_top`).

Together, they compute the Kullback–Leibler divergence of a transported measure `T#μ` with
respect to `π` when `T⁻¹#π` has a density `w` with respect to `π`, without any density for `μ`.
-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  {w : α → ℝ}

namespace MeasureTheory

/-- Reweighting the reference measure by a positive weight `w` preserves absolute continuity. -/
theorem Measure.AbsolutelyContinuous.withDensity_ofReal (hμν : μ ≪ ν) (hw : Measurable w)
    (hw₀ : ∀ᵐ x ∂ν, 0 < w x) : μ ≪ ν.withDensity fun x ↦ ENNReal.ofReal (w x) :=
  hμν.trans (withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable
    (hw₀.mono fun x hx ↦ by simp [hx]))

/-- Reweighting the reference measure by a positive weight `w` subtracts `log w` from the
log-likelihood ratio. -/
theorem llr_withDensity_ofReal_right [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (hw : Measurable w) (hw₀ : ∀ᵐ x ∂ν, 0 < w x) :
    llr μ (ν.withDensity fun x ↦ ENNReal.ofReal (w x)) =ᵐ[μ] fun x ↦ llr μ ν x - log (w x) := by
  filter_upwards [hμν.ae_le (Measure.rnDeriv_withDensity_right μ ν hw.ennreal_ofReal.aemeasurable
    (hw₀.mono fun x hx ↦ by simp [hx]) (.of_forall fun _ ↦ ENNReal.ofReal_ne_top)),
    Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν), hμν.ae_le hw₀]
    with x hx hpos hlt hwx
  rw [llr, llr, hx, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hwx.le,
    log_mul (inv_ne_zero hwx.ne') (ENNReal.toReal_pos hpos.ne' hlt.ne).ne', log_inv]
  ring

end MeasureTheory

namespace InformationTheory

/-- A measure at finite Kullback–Leibler divergence from a measure carried by `Ω` is carried by
`Ω`. -/
theorem ae_mem_of_klDiv_ne_top {Ω : Set α} {f : α → ℝ≥0∞} (hΩ : MeasurableSet Ω)
    (hμ : klDiv μ ((ν.restrict Ω).withDensity f) ≠ ∞) : ∀ᵐ x ∂μ, x ∈ Ω :=
  (klDiv_ne_top_iff.1 hμ).1.ae_le ((withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem hΩ))

/-- Transporting the first argument of the Kullback–Leibler divergence by a measurable equivalence
amounts to transporting the second one backwards. -/
theorem klDiv_map_measurableEquiv_left [IsFiniteMeasure μ] {ν : Measure β} [IsFiniteMeasure ν]
    (e : α ≃ᵐ β) : klDiv (μ.map e) ν = klDiv μ (ν.map e.symm) := by
  rw [← Measure.klDiv_map_measurableEquiv μ (ν.map e.symm) e, MeasurableEquiv.map_map_symm]

section Reweighting

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
  (hw : Measurable w) (hw₀ : ∀ᵐ x ∂ν, 0 < w x) (hlog : Integrable (fun x ↦ log (w x)) μ)
include hμν h_int hw hw₀ hlog

/-- Reweighting the reference measure by a positive weight `w` with `log w` integrable preserves
the finiteness of the Kullback–Leibler divergence. -/
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
