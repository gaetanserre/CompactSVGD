/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import SBS.Analysis.ODE.FlowHomeomorph
public import SBS.Analysis.ODE.FlowJacobian
public import SBS.InformationTheory.KullbackLeibler.Transport
public import SBS.Probability.Stein.Operator

/-!
# The dissipation of the Kullback–Leibler divergence along a flow

Let `Ω` be a compact subset of a finite-dimensional real normed space `E` with an additive Haar
measure `vol`, and let `π = p · vol|_Ω`, where `p` is continuous and positive on `Ω` and `log p`
has derivative `s` in the interior of `Ω`, with `s` continuous on `Ω`. Let `v : ℝ → E → E` be a
time-dependent vector field, continuous in time, `K`-Lipschitz in space uniformly in time,
differentiable in space with a jointly continuous derivative, and vanishing on the frontier of
`Ω`. Let `α x` be its trajectory with `α x 0 = x`, and let `μ` be a probability measure with
`KL(μ ‖ π) < ∞`. Then `μₜ = (α · t)#μ` satisfies `KL(μₜ ‖ π) < ∞`
(`InformationTheory.klDiv_map_flow_ne_top`) and

  `∂ₜ KL(μₜ ‖ π) = -E_{μₜ}[𝒜_s vₜ]`

at every time `t` (`InformationTheory.hasDerivAt_toReal_klDiv_map_flow`), where
`𝒜_s vₜ = s(vₜ) + div vₜ` is the Stein operator. This is the continuous-time counterpart of the
first variation `InformationTheory.hasDerivAt_toReal_klDiv_map_add_smul`.

The proof is Lagrangian. No density, continuity equation or time regularity is needed for `μₜ`. By
the transport formula `InformationTheory.toReal_klDiv_map_eq`,

  `KL(μₜ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ (α · t) - log p + log det D(α · t)) dμ`,

and the time derivative of the integrand is `𝒜_s vₜ ∘ (α · t)`. Indeed, the trajectories through
the frontier of `Ω` are constant, those through the interior of `Ω` stay in the interior, and
`∂ₜ log det D(α · t) = div vₜ ∘ (α · t)` by Liouville's formula
(`ODE.hasDerivAt_log_det_fderiv_flow`).

## Main statements

* `InformationTheory.klDiv_map_flow_ne_top`: the flow preserves the finiteness of the
  Kullback–Leibler divergence.
* `InformationTheory.hasDerivAt_toReal_klDiv_map_flow`: **the dissipation of the Kullback–Leibler
  divergence**, `∂ₜ KL(μₜ ‖ π) = -E_{μₜ}[𝒜_s vₜ]`.

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
  {μ : Measure E} [IsProbabilityMeasure μ]

variable (hΩ : IsCompact Ω) (hp : Measurable p) (hpc : ContinuousOn p Ω)
  (hp₀ : ∀ x ∈ Ω, 0 < p x) (hvc : ∀ y, Continuous (v · y)) (hvK : ∀ t, LipschitzWith K (v t))
  (hv : ∀ t y, HasFDerivAt (v t) (Dv t y) y) (hDv : Continuous (uncurry Dv))
  (hv₀ : ∀ t, ∀ y ∈ frontier Ω, v t y = 0) (hα : ∀ x t, HasDerivAt (α x) (v t (α x t)) t)
  (hα₀ : ∀ x, α x 0 = x)
  (hμ : klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞)
include hΩ hp hpc hp₀ hvc hvK hv hDv hv₀ hα hα₀ hμ

omit [vol.IsAddHaarMeasure] hp hpc hp₀ hμ in
/-- The flow map at time `t` is a measurable equivalence satisfying the assumptions of the
transport formula `InformationTheory.toReal_klDiv_map_eq`. -/
private theorem exists_measurableEquiv_flow (t : ℝ) :
    ∃ e : E ≃ᵐ E, ⇑e = (α · t) ∧ (∀ x ∈ Ω, DifferentiableAt ℝ e x) ∧ ⇑e '' Ω = Ω ∧
      (∀ x ∈ Ω, 0 < (fderiv ℝ e x).det) ∧ Integrable (fun x ↦ log (fderiv ℝ e x).det) μ := by
  set e := (isHomeomorph_flow hvc hvK hα hα₀ t).homeomorph _
  have hcoe : ⇑e.toMeasurableEquiv = (α · t) := rfl
  refine ⟨e.toMeasurableEquiv, hcoe, ?_⟩
  rw [hcoe]
  refine ⟨fun x _ ↦ differentiable_flow hv hDv hvK hα hα₀ t x,
    image_flow_eq hvc hvK hα hα₀ hΩ.isClosed hv₀ t,
    fun x _ ↦ det_fderiv_flow_pos hv hDv hvK hα hα₀ x t, ?_⟩
  exact Integrable.of_bound (TauCeti.measurable_det_fderiv ℝ _).log.aestronglyMeasurable _
    (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le
      (abs_log_det_fderiv_flow_le hv hDv hvK hα hα₀ x t))

/-- **The flow preserves the finiteness of the Kullback–Leibler divergence.** If
`KL(μ ‖ π) < ∞`, then `KL((α · t)#μ ‖ π) < ∞` for every time `t`. -/
theorem klDiv_map_flow_ne_top (t : ℝ) :
    klDiv (μ.map (α · t)) ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞ := by
  obtain ⟨e, he, h₁, h₂, h₃, h₄⟩ :=
    exists_measurableEquiv_flow (μ := μ) hΩ hvc hvK hv hDv hv₀ hα hα₀ t
  rw [← he]
  exact klDiv_map_ne_top hΩ hp hpc hp₀ h₁ h₂ h₃ h₄ hμ

/-- **The dissipation of the Kullback–Leibler divergence along a flow** (Theorem A.11). Let
`π = p · vol|_Ω` as above, let `α` be the flow of a vector field `v` vanishing on the frontier of
`Ω`, and let `μ` be a probability measure with `KL(μ ‖ π) < ∞`. Then `μₜ = (α · t)#μ` satisfies
`∂ₜ KL(μₜ ‖ π) = -E_{μₜ}[𝒜_s vₜ]` at every time `t`, where `𝒜_s vₜ = s(vₜ) + div vₜ` is the Stein
operator. -/
theorem hasDerivAt_toReal_klDiv_map_flow {s : E → StrongDual ℝ E}
    (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ log (p y)) (s x) x) (hsc : ContinuousOn s Ω)
    (t₀ : ℝ) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (α · t))
        ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal)
      (-∫ y, ProbabilityTheory.steinOperator s (v t₀) y ∂(μ.map (α · t₀))) t₀ := by
  set ν := (vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := ae_mem_of_klDiv_ne_top hΩ.measurableSet hμ
  have hαc (t : ℝ) : Continuous (α · t) := continuous_flow hv hDv hvK hα hα₀ t
  have hαΩ {x : E} (hx : x ∈ Ω) (t : ℝ) : α x t ∈ Ω :=
    mem_of_forall_frontier_eq_zero hΩ.isClosed hvK hv₀ (hα x) (t₀ := 0) (by rwa [hα₀]) t
  -- The Kullback–Leibler divergence along the flow, by the transport formula.
  set G : ℝ → E → ℝ := fun t x ↦ log (p (α x t)) - log (p x) + log (fderiv ℝ (α · t) x).det
  have hF (t : ℝ) : (klDiv (μ.map (α · t)) ν).toReal = (klDiv μ ν).toReal - ∫ x, G t x ∂μ := by
    obtain ⟨e, he, h₁, h₂, h₃, h₄⟩ :=
      exists_measurableEquiv_flow (μ := μ) hΩ hvc hvK hv hDv hv₀ hα hα₀ t
    have := toReal_klDiv_map_eq hΩ hp hpc hp₀ h₁ h₂ h₃ h₄ hμ
    rwa [he] at this
  -- The derivative of the integrand is the Stein operator along the flow.
  set G' : ℝ → E → ℝ := fun t x ↦ ProbabilityTheory.steinOperator s (v t) (α x t)
  have hG' : ∫ y, ProbabilityTheory.steinOperator s (v t₀) y ∂(μ.map (α · t₀)) =
      ∫ x, G' t₀ x ∂μ := by
    obtain ⟨e, he, -⟩ := exists_measurableEquiv_flow (μ := μ) hΩ hvc hvK hv hDv hv₀ hα hα₀ t₀
    rw [← he, integral_map_equiv, he]
  -- Uniform bounds: `‖s‖ ≤ S` on `Ω`, `‖v‖ ≤ V` on `[t₀ - 1, t₀ + 1] × Ω`, `|div v| ≤ ‖trace‖ K`.
  obtain ⟨S, hS⟩ := hΩ.exists_bound_of_continuousOn hsc
  obtain ⟨V, hV⟩ := ((isCompact_Icc (a := t₀ - 1) (b := t₀ + 1)).prod
    hΩ).exists_bound_of_continuousOn
      (continuous_prod_of_continuous_lipschitzWith' (uncurry v) K hvK hvc).continuousOn
  have hdivc (t : ℝ) : Continuous (divergence ℝ (v t)) := by
    have : divergence ℝ (v t) = fun y ↦ ContinuousLinearMap.trace ℝ E (Dv t y) :=
      funext fun y ↦ (hv t y).divergence_eq
    rw [this]
    exact (ContinuousLinearMap.trace ℝ E).continuous.comp
      (hDv.comp (continuous_const.prodMk continuous_id))
  have hlogdetm (t : ℝ) : Measurable fun x ↦ log (fderiv ℝ (α · t) x).det :=
    (TauCeti.measurable_det_fderiv ℝ _).log
  have hlogp : ContinuousOn (fun x ↦ log (p x)) Ω := hpc.log fun x hx ↦ (hp₀ x hx).ne'
  have hint {f : E → ℝ} (hf : ContinuousOn f Ω) : Integrable f μ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hμΩ]
    exact hf.integrableOn_compact hΩ
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := G) (F' := G')
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (bound := fun _ ↦ S * V + ‖ContinuousLinearMap.trace ℝ E‖ * K)
    (Metric.ball_mem_nhds t₀ one_pos) ?_ ?_ ?_ ?_ (integrable_const _) ?_
  · rw [funext hF, hG', neg_eq_zero_sub]
    exact (hasDerivAt_const t₀ _).sub hderiv.2
  · -- Measurability of the integrand.
    exact .of_forall fun t ↦ (((measurable_log.comp (hp.comp (hαc t).measurable)).sub
      (measurable_log.comp hp)).add (hlogdetm t)).aestronglyMeasurable
  · -- Integrability of the integrand.
    exact ((hint (hlogp.comp (hαc t₀).continuousOn fun _ hx ↦ hαΩ hx t₀)).sub
      (hint hlogp)).add (Integrable.of_bound (hlogdetm t₀).aestronglyMeasurable _
        (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le
          (abs_log_det_fderiv_flow_le hv hDv hvK hα hα₀ x t₀)))
  · -- Measurability of the derivative at `t₀`.
    rw [← Measure.restrict_eq_self_of_ae_mem hμΩ]
    exact (((hsc.comp (hαc t₀).continuousOn fun _ hx ↦ hαΩ hx t₀).clm_apply
      ((hvK t₀).continuous.comp (hαc t₀)).continuousOn).add
        ((hdivc t₀).comp (hαc t₀)).continuousOn).aestronglyMeasurable hΩ.measurableSet
  · -- Domination of the derivative.
    filter_upwards [hμΩ] with x hx t ht
    have htI : t ∈ Icc (t₀ - 1) (t₀ + 1) := by
      rw [Real.ball_eq_Ioo] at ht
      exact Ioo_subset_Icc_self ht
    have hVx : ‖v t (α x t)‖ ≤ V := hV (t, α x t) ⟨htI, hαΩ hx t⟩
    have hSx : ‖s (α x t)‖ ≤ S := hS _ (hαΩ hx t)
    change ‖s (α x t) (v t (α x t)) + divergence ℝ (v t) (α x t)‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add (((s (α x t)).le_opNorm _).trans
      (mul_le_mul hSx hVx (norm_nonneg _) ((norm_nonneg _).trans hSx)))
      (norm_divergence_le_of_lipschitz (hvK t) _))
  · -- Differentiability of the integrand.
    filter_upwards [hμΩ] with x hx t ht
    -- The term `log p (α x t)`.
    have h₁ : HasDerivAt (fun t ↦ log (p (α x t))) (s (α x t) (v t (α x t))) t := by
      by_cases hxi : x ∈ interior Ω
      · have hxt : α x t ∈ interior Ω := mem_interior_of_forall_frontier_eq_zero hΩ.isClosed hvK
          hv₀ (hα x) (t₀ := 0) (by rwa [hα₀]) t
        exact (hs _ hxt).comp_hasDerivAt t (hα x t)
      · -- The trajectory through a point of the frontier is constant.
        have hfr : x ∈ frontier Ω := ⟨subset_closure hx, hxi⟩
        have hconst (τ : ℝ) : α x τ = x := by
          have := congrFun (eq_const_of_forall_eq_zero hvK (hα x) (t₀ := 0) fun τ ↦ by
            rw [hα₀]
            exact hv₀ τ x hfr) τ
          rwa [hα₀] at this
        simp only [hconst, hv₀ t x hfr, map_zero]
        exact hasDerivAt_const t _
    -- The term `log det D(α · t) x`, by Liouville's formula.
    exact (h₁.sub_const (log (p x))).add (hasDerivAt_log_det_fderiv_flow hv hDv hvK hα hα₀ x t)

end InformationTheory
