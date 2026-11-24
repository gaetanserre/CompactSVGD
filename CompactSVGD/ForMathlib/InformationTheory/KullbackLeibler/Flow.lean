/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.InformationTheory.KullbackLeibler.Basic

import CompactSVGD.ForMathlib.Analysis.Calculus.Divergence
import CompactSVGD.ForMathlib.Analysis.Calculus.FDeriv.Measurable
import CompactSVGD.ForMathlib.Analysis.ODE.FlowHomeomorph
import CompactSVGD.ForMathlib.Analysis.ODE.FlowJacobian
import CompactSVGD.ForMathlib.Analysis.ODE.Invariance
import CompactSVGD.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Basic
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Transport
import CompactSVGD.ForMathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The dissipation of the Kullback–Leibler divergence along a flow

Let `π = p · vol|_Ω` as for the first variation, let `v : ℝ → E → E` be continuous in time,
Lipschitz in space, with a jointly continuous spatial derivative and vanishing on the frontier of
`Ω`, and let `α` be its flow. If `KL(μ ‖ π) < ∞`, then `μₜ = (α · t)#μ` satisfies
`∂ₜ KL(μₜ ‖ π) = -E_{μₜ}[𝒜_s vₜ]` at every time. The proof is Lagrangian: no density, continuity
equation or time regularity is needed for `μₜ`.

## Main statements

* `InformationTheory.klDiv_map_flow_ne_top`: the divergence stays finite along the flow.
* `InformationTheory.hasDerivAt_toReal_klDiv_map_flow`: **the dissipation of the
  Kullback–Leibler divergence**.

## References

* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Theorem A.11
-/

@[expose] public section

open MeasureTheory Set Function Real ODE

open scoped NNReal ENNReal

namespace InformationTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {vol : Measure E} [vol.IsAddHaarMeasure] {Ω : Set E}
  {p : E → ℝ} {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {K : ℝ≥0} {α : E → ℝ → E}
  {μ : Measure E} [IsFiniteMeasure μ]

private theorem integrable_log_det_fderiv_flow (hvK : ∀ t, LipschitzWith K (v t))
    (hv : ∀ t y, HasFDerivAt (v t) (Dv t y) y) (hDv : Continuous (uncurry Dv))
    (hα : ∀ x t, HasDerivAt (α x) (v t (α x t)) t) (hα₀ : ∀ x, α x 0 = x) (t : ℝ) :
    Integrable (fun x ↦ log (fderiv ℝ (α · t) x).det) μ :=
  Integrable.of_bound (measurable_det_fderiv ℝ _).log.aestronglyMeasurable _
    (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le
      (abs_log_det_fderiv_flow_le hv hDv hvK hα hα₀ x t))

/-- The flow map at time `t` is a measurable equivalence satisfying the assumptions of the
transport formula `InformationTheory.toReal_klDiv_map_eq`. -/
private theorem exists_measurableEquiv_flow (hvc : ∀ y, Continuous (v · y))
    (hvK : ∀ t, LipschitzWith K (v t)) (hv : ∀ t y, HasFDerivAt (v t) (Dv t y) y)
    (hDv : Continuous (uncurry Dv)) (hv₀ : ∀ t, ∀ y ∈ frontier Ω, v t y = 0)
    (hα : ∀ x t, HasDerivAt (α x) (v t (α x t)) t) (hα₀ : ∀ x, α x 0 = x) (t : ℝ) :
    ∃ e : E ≃ᵐ E, ⇑e = (α · t) ∧ (∀ x ∈ Ω, DifferentiableAt ℝ e x) ∧ ⇑e '' Ω = Ω ∧
      (∀ x ∈ Ω, 0 < (fderiv ℝ e x).det) ∧ Integrable (fun x ↦ log (fderiv ℝ e x).det) μ := by
  set e := (isHomeomorph_flow hvc hvK hα hα₀ t).homeomorph _
  have hcoe : ⇑e.toMeasurableEquiv = (α · t) := rfl
  refine ⟨e.toMeasurableEquiv, hcoe, ?_⟩
  rw [hcoe]
  refine ⟨fun x _ ↦ differentiable_flow hv hDv hvK hα hα₀ t x,
    image_flow_eq_of_forall_frontier_eq_zero hvc hvK hα hα₀ hv₀ t,
    fun x _ ↦ det_fderiv_flow_pos hv hDv hvK hα hα₀ x t, ?_⟩
  exact integrable_log_det_fderiv_flow hvK hv hDv hα hα₀ t

variable (hΩ : IsCompact Ω) (hp : Measurable p) (hpc : ContinuousOn p Ω)
  (hp₀ : ∀ x ∈ Ω, 0 < p x) (hvc : ∀ y, Continuous (v · y)) (hvK : ∀ t, LipschitzWith K (v t))
  (hv : ∀ t y, HasFDerivAt (v t) (Dv t y) y) (hDv : Continuous (uncurry Dv))
  (hv₀ : ∀ t, ∀ y ∈ frontier Ω, v t y = 0) (hα : ∀ x t, HasDerivAt (α x) (v t (α x t)) t)
  (hα₀ : ∀ x, α x 0 = x)
  (hμ : klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞)
include hΩ hp hpc hp₀ hvc hvK hv hDv hv₀ hα hα₀ hμ

/-- **The Kullback–Leibler divergence stays finite along a flow.** Let `π = p · vol|_Ω` as above,
let `α` be the flow of a vector field `v` vanishing on the frontier of `Ω`, and let `μ` be a finite
measure with `KL(μ ‖ π) < ∞`. Then `KL((α · t)#μ ‖ π) < ∞` at every time `t`. -/
theorem klDiv_map_flow_ne_top (t : ℝ) :
    klDiv (μ.map (α · t)) ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞ := by
  obtain ⟨e, he, h₁, h₂, h₃, h₄⟩ :=
    exists_measurableEquiv_flow (μ := μ) hvc hvK hv hDv hv₀ hα hα₀ t
  have := klDiv_map_ne_top hΩ hp hpc hp₀ h₁ h₂ h₃ h₄ hμ
  rwa [he] at this

/-- **The dissipation of the Kullback–Leibler divergence along a flow** (proof of Theorem A.11 of
[Serre2025]). Let
`π = p · vol|_Ω` as above, let `α` be the flow of a vector field `v` vanishing on the frontier of
`Ω`, and let `μ` be a finite measure with `KL(μ ‖ π) < ∞`. Then `μₜ = (α · t)#μ` satisfies
`∂ₜ KL(μₜ ‖ π) = -E_{μₜ}[𝒜_s vₜ]` at every time `t`, where `𝒜_s vₜ = s(vₜ) + div vₜ` is the Stein
operator. -/
theorem hasDerivAt_toReal_klDiv_map_flow {s : E → StrongDual ℝ E}
    (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ log (p y)) (s x) x) (hsc : ContinuousOn s Ω)
    (t₀ : ℝ) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (α · t))
        ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal)
      (-∫ y, (s y (v t₀ y) + divergence ℝ (v t₀) y) ∂(μ.map (α · t₀))) t₀ := by
  set ν := (vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := ae_mem_of_klDiv_ne_top hΩ.measurableSet hμ
  have hαc (t : ℝ) : Continuous (α · t) := continuous_flow hv hDv hvK hα hα₀ t
  have hαΩ {x : E} (hx : x ∈ Ω) (t : ℝ) : α x t ∈ Ω :=
    mem_of_forall_frontier_eq_zero hvK hv₀ (hα x) (t₀ := 0) (by rwa [hα₀]) t
  -- The Kullback–Leibler divergence along the flow, by the transport formula.
  set G : ℝ → E → ℝ := fun t x ↦ log (p (α x t)) - log (p x) + log (fderiv ℝ (α · t) x).det
  have hF (t : ℝ) : (klDiv (μ.map (α · t)) ν).toReal = (klDiv μ ν).toReal - ∫ x, G t x ∂μ := by
    obtain ⟨e, he, h₁, h₂, h₃, h₄⟩ :=
      exists_measurableEquiv_flow (μ := μ) hvc hvK hv hDv hv₀ hα hα₀ t
    have := toReal_klDiv_map_eq hΩ hp hpc hp₀ h₁ h₂ h₃ h₄ hμ
    rwa [he] at this
  -- The derivative of the integrand is the Stein operator along the flow.
  set G' : ℝ → E → ℝ := fun t x ↦ (s (α x t) (v t (α x t)) + divergence ℝ (v t) (α x t))
  have hG' : ∫ y, (s y (v t₀ y) + divergence ℝ (v t₀) y) ∂(μ.map (α · t₀)) =
      ∫ x, G' t₀ x ∂μ := by
    obtain ⟨e, he, -⟩ := exists_measurableEquiv_flow (μ := μ) hvc hvK hv hDv hv₀ hα hα₀ t₀
    rw [← he, integral_map_equiv, he]
  -- Uniform bounds: `‖s‖ ≤ S` on `Ω`, `‖v‖ ≤ V` on `[t₀ - 1, t₀ + 1] × Ω`, `|div v| ≤ ‖trace‖ K`.
  obtain ⟨S, hS⟩ := hΩ.exists_bound_of_continuousOn hsc
  obtain ⟨V, hV⟩ := ((isCompact_Icc (a := t₀ - 1) (b := t₀ + 1)).prod
    hΩ).exists_bound_of_continuousOn
      (continuous_prod_of_continuous_lipschitzWith' (uncurry v) K hvK hvc).continuousOn
  have hdivc (t : ℝ) : Continuous (divergence ℝ (v t)) :=
    (contDiff_one_iff_hasFDerivAt.2 ⟨Dv t, hDv.comp (continuous_const.prodMk continuous_id),
      hv t⟩).continuous_divergence
  have hlogdetm (t : ℝ) : Measurable fun x ↦ log (fderiv ℝ (α · t) x).det :=
    (measurable_det_fderiv ℝ _).log
  have hlogp : ContinuousOn (fun x ↦ log (p x)) Ω := hpc.log fun x hx ↦ (hp₀ x hx).ne'
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := G) (F' := G')
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (bound := fun _ ↦ S * V + ‖ContinuousLinearMap.traceCLM ℝ E‖ * K)
    (Metric.ball_mem_nhds t₀ one_pos) ?_ ?_ ?_ ?_ (integrable_const _) ?_
  · rw [funext hF, hG', neg_eq_zero_sub]
    exact (hasDerivAt_const t₀ _).sub hderiv.2
  · -- Measurability of the integrand.
    exact .of_forall fun t ↦ (((measurable_log.comp (hp.comp (hαc t).measurable)).sub
      (measurable_log.comp hp)).add (hlogdetm t)).aestronglyMeasurable
  · -- Integrability of the integrand.
    exact (((hlogp.comp (hαc t₀).continuousOn fun _ hx ↦ hαΩ hx t₀).integrable_of_ae_mem hΩ
      hμΩ).sub (hlogp.integrable_of_ae_mem hΩ hμΩ)).add
        (integrable_log_det_fderiv_flow hvK hv hDv hα hα₀ t₀)
  · -- Measurability of the derivative at `t₀`.
    exact ((((hsc.comp (hαc t₀).continuousOn fun _ hx ↦ hαΩ hx t₀).clm_apply
      ((hvK t₀).continuous.comp (hαc t₀)).continuousOn).add
        ((hdivc t₀).comp (hαc t₀)).continuousOn).integrable_of_ae_mem hΩ
          hμΩ).aestronglyMeasurable
  · -- Domination of the derivative.
    filter_upwards [hμΩ] with x hx t ht
    have htI : t ∈ Icc (t₀ - 1) (t₀ + 1) := by
      rw [Real.ball_eq_Ioo] at ht
      exact Ioo_subset_Icc_self ht
    have hVx : ‖v t (α x t)‖ ≤ V := hV (t, α x t) ⟨htI, hαΩ hx t⟩
    have hSx : ‖s (α x t)‖ ≤ S := hS _ (hαΩ hx t)
    change ‖s (α x t) (v t (α x t)) + divergence ℝ (v t) (α x t)‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add ((s (α x t)).le_of_opNorm_le_of_le hSx hVx)
      (norm_divergence_le_of_lipschitz (hvK t) _))
  · -- Differentiability of the integrand.
    filter_upwards [hμΩ] with x hx t ht
    -- The term `log p (α x t)`.
    have h₁ : HasDerivAt (fun t ↦ log (p (α x t))) (s (α x t) (v t (α x t))) t := by
      refine hasDerivAt_log_comp_of_mem_interior_or_const hs (hα x t) ?_
      by_cases hxi : x ∈ interior Ω
      · exact .inl (mem_interior_of_forall_frontier_eq_zero hvK hv₀ (hα x) (t₀ := 0)
          (by rwa [hα₀]) t)
      · -- The trajectory through a point of the frontier is constant.
        have hfr : x ∈ frontier Ω := ⟨subset_closure hx, hxi⟩
        have hconst (τ : ℝ) : α x τ = x := by
          have := congrFun (eq_const_of_forall_eq_zero hvK (hα x) (t₀ := 0) fun τ ↦ by
            rw [hα₀]
            exact hv₀ τ x hfr) τ
          rwa [hα₀] at this
        exact .inr ⟨funext fun τ ↦ by rw [hconst, hconst], by rw [hconst, hv₀ t x hfr]⟩
    -- The term `log det D(α · t) x`, by Liouville's formula.
    exact (h₁.sub_const (log (p x))).add (hasDerivAt_log_det_fderiv_flow hv hDv hvK hα hα₀ x t)

end InformationTheory
