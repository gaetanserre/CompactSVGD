/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.InformationTheory.KullbackLeibler.Basic

import CompactSVGD.ForMathlib.Analysis.Calculus.Divergence
import CompactSVGD.ForMathlib.Analysis.Calculus.FDeriv.DetIdAddSMul
import CompactSVGD.ForMathlib.Analysis.Normed.PerturbationOfIdentity
import CompactSVGD.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Basic
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Transport
import CompactSVGD.ForMathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

/-!
# The first variation of the Kullback–Leibler divergence

Let `π = p · vol|_Ω`, with `Ω` compact, `p` continuous and positive on `Ω`, and `log p`
differentiable in the interior of `Ω` with derivative `s`. Let `v` be a `C¹` Lipschitz vector field
vanishing on the frontier of `Ω`, and `μ` a finite measure with `KL(μ ‖ π) < ∞`. Then
`ε ↦ KL((I + ε v)#μ ‖ π)` has derivative `-E_μ[𝒜_s v]` at `0`.

## Main statements

* `InformationTheory.eventually_klDiv_map_add_smul_ne_top`: `KL((I + ε v)#μ ‖ π) < ∞` for small
  `ε`.
* `InformationTheory.toReal_klDiv_map_add_smul`: the Kullback–Leibler divergence of
  `(I + ε v)#μ`, by the transport formula.
* `InformationTheory.hasDerivAt_toReal_klDiv_map_add_smul`: **the first variation**.

## References

* [Q. Liu, D. Wang, *Stein Variational Gradient Descent*][Liu2016SVGD]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Theorem A.8
-/

@[expose] public section

open MeasureTheory Set Real

open scoped NNReal ENNReal Topology

namespace InformationTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {vol : Measure E} [vol.IsAddHaarMeasure] {Ω : Set E}
  {p : E → ℝ} {v : E → E} {K : ℝ≥0} {ε : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The map `(ε, A) ↦ I + ε A` is continuous. -/
private theorem continuous_id_add_smul :
    Continuous fun q : ℝ × (E →L[ℝ] E) ↦ ContinuousLinearMap.id ℝ E + q.1 • q.2 :=
  continuous_const.add (continuous_fst.smul continuous_snd)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The determinant of `I + ε A` is continuous in `(ε, A)`. -/
private theorem continuous_det_id_add_smul :
    Continuous fun q : ℝ × (E →L[ℝ] E) ↦
      LinearMap.det ((ContinuousLinearMap.id ℝ E + q.1 • q.2 : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
  ContinuousLinearMap.continuous_det.comp continuous_id_add_smul

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Near `ε = 0`, the perturbation `I + ε v` is a perturbation of the identity, i.e.
`|ε| K < 1`, and its Jacobian determinant is at least `1 / 2` on `Ω`. -/
private theorem eventually_lt_one_and_half_le_det (hΩ : IsCompact Ω) (hv : ContDiff ℝ 1 v) :
    ∀ᶠ ε : ℝ in 𝓝 0, ‖ε‖₊ * K < 1 ∧
      ∀ x ∈ Ω, 1 / 2 ≤ (fderiv ℝ (fun y ↦ y + ε • v y) x).det := by
  set J : ℝ → (E →L[ℝ] E) → ℝ := fun ε A ↦
    LinearMap.det ((ContinuousLinearMap.id ℝ E + ε • A : E →L[ℝ] E) : E →ₗ[ℝ] E)
  have hJc : Continuous fun q : ℝ × (E →L[ℝ] E) ↦ J q.1 q.2 := continuous_det_id_add_smul
  have hKD : IsCompact (fderiv ℝ v '' Ω) := hΩ.image (hv.continuous_fderiv one_ne_zero)
  have hJ₀ : ∀ᶠ ε in 𝓝 0, ∀ A ∈ fderiv ℝ v '' Ω, 1 / 2 ≤ J ε A :=
    hKD.eventually_forall_of_forall_eventually fun A _ ↦
      ((hJc.tendsto (0, A)).eventually_const_lt (by norm_num [J])).mono fun _ h ↦ h.le
  have hK : ∀ᶠ ε : ℝ in 𝓝 0, ‖ε‖₊ * K < 1 :=
    (((continuous_nnNorm (E := ℝ)).mul continuous_const).tendsto 0).eventually_lt_const
      (by simp)
  filter_upwards [hK, hJ₀] with ε hε hJ
  refine ⟨hε, fun x hx ↦ ?_⟩
  rw [(hasFDerivAt_add_smul (ε := ε) ((hv.differentiable one_ne_zero) x)).fderiv]
  exact hJ _ (mem_image_of_mem _ hx)

/-- The perturbation `I + ε v` as a measurable equivalence, with the properties required by the
transport formula `InformationTheory.toReal_klDiv_map_eq`. -/
private theorem exists_measurableEquiv_add_smul {μ : Measure E} [IsFiniteMeasure μ]
    (hvK : LipschitzWith K v)
    (hε : ‖ε‖₊ * K < 1) (hΩ : IsCompact Ω) (hv : ContDiff ℝ 1 v)
    (hv₀ : ∀ y ∈ frontier Ω, v y = 0)
    (hdet : ∀ x ∈ Ω, 0 < (fderiv ℝ (fun y ↦ y + ε • v y) x).det) (hμΩ : ∀ᵐ x ∂μ, x ∈ Ω) :
    ∃ e : E ≃ᵐ E, ⇑e = (fun x ↦ x + ε • v x) ∧ (∀ x ∈ Ω, DifferentiableAt ℝ e x) ∧
      ⇑e '' Ω = Ω ∧ Integrable (fun x ↦ log (fderiv ℝ e x).det) μ := by
  obtain ⟨e₀, he₀⟩ := hvK.exists_homeomorph_id_add_smul hε
  have he : ⇑e₀.toMeasurableEquiv = fun x ↦ x + ε • v x := he₀
  have hdetc : Continuous fun x ↦ (fderiv ℝ (fun y ↦ y + ε • v y) x).det :=
    ContinuousLinearMap.continuous_det.comp
      ((contDiff_id.add (hv.const_smul ε)).continuous_fderiv one_ne_zero)
  refine ⟨e₀.toMeasurableEquiv, he, fun x _ ↦ he ▸
    (hasFDerivAt_add_smul (hv.differentiable one_ne_zero x)).differentiableAt,
    he ▸ hvK.image_add_smul_eq_of_forall_frontier_eq_zero hε hv₀, he ▸ ?_⟩
  exact (hdetc.continuousOn.log fun x hx ↦ (hdet x hx).ne').integrable_of_ae_mem hΩ hμΩ

section Perturbation

variable {μ : Measure E} [IsFiniteMeasure μ] (hvK : LipschitzWith K v) (hΩ : IsCompact Ω)
  (hp : Measurable p) (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x) (hv : ContDiff ℝ 1 v)
  (hv₀ : ∀ y ∈ frontier Ω, v y = 0)
  (hμ : klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞)
include hvK hΩ hp hpc hp₀ hv hv₀ hμ

/-- **The perturbed Kullback–Leibler divergence is finite near `0`.** Let `π = p · vol|_Ω`, with
`Ω` compact and `p` continuous and positive on `Ω`, let `v` be a `C¹` Lipschitz vector field
vanishing on the frontier of `Ω`, and let `μ` be a finite measure with `KL(μ ‖ π) < ∞`. Then
`KL((I + ε v)#μ ‖ π) < ∞` for every `ε` close enough to `0`. -/
theorem eventually_klDiv_map_add_smul_ne_top :
    ∀ᶠ ε : ℝ in 𝓝 0, klDiv (μ.map fun x ↦ x + ε • v x)
      ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞ := by
  filter_upwards [eventually_lt_one_and_half_le_det (K := K) hΩ hv] with ε ⟨hε, hdet⟩
  have hdet' (x : E) (hx : x ∈ Ω) : 0 < (fderiv ℝ (fun y ↦ y + ε • v y) x).det :=
    lt_of_lt_of_le (by norm_num) (hdet x hx)
  obtain ⟨e, he, hed, himage, hdetμ⟩ := exists_measurableEquiv_add_smul hvK hε hΩ hv hv₀ hdet'
    (ae_mem_of_klDiv_ne_top hΩ.measurableSet hμ)
  have := klDiv_map_ne_top hΩ hp hpc hp₀ hed himage (he ▸ hdet') hdetμ hμ
  rwa [he] at this

/-- **The Kullback–Leibler divergence of a perturbed measure.** Let `π = p · vol|_Ω`, with `Ω`
compact and `p` continuous and positive on `Ω`, let `v` be a `C¹` `K`-Lipschitz vector field
vanishing on the frontier of `Ω`, and let `μ` be a finite measure with `KL(μ ‖ π) < ∞`. If
`|ε| K < 1` and the Jacobian determinant of `Tε = I + ε v` is positive on `Ω`, then
`KL(Tε#μ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ Tε - log p + log det DTε) dμ`. -/
theorem toReal_klDiv_map_add_smul (hε : ‖ε‖₊ * K < 1)
    (hdet : ∀ x ∈ Ω, 0 < (fderiv ℝ (fun y ↦ y + ε • v y) x).det) :
    (klDiv (μ.map fun x ↦ x + ε • v x)
        ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal =
      (klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal -
        ∫ x, (log (p (x + ε • v x)) - log (p x) +
          log (fderiv ℝ (fun y ↦ y + ε • v y) x).det) ∂μ := by
  obtain ⟨e, he, hed, himage, hdetμ⟩ := exists_measurableEquiv_add_smul hvK hε hΩ hv hv₀ hdet
    (ae_mem_of_klDiv_ne_top hΩ.measurableSet hμ)
  have h := toReal_klDiv_map_eq hΩ hp hpc hp₀ hed himage (he ▸ hdet) hdetμ hμ
  simpa only [he] using h

/-- **The first variation of the Kullback–Leibler divergence** (proof of Theorem A.8 of
[Serre2025]). Let `π = p · vol|_Ω`, with `Ω` compact, `p` continuous and positive on `Ω`, and
`log p` differentiable in the interior of `Ω` with derivative `s`, continuous on `Ω`. Let `v` be a
`C¹` Lipschitz vector field vanishing on the frontier of `Ω`, and let `μ` be a finite measure with
`KL(μ ‖ π) < ∞`. Then
`ε ↦ KL((I + ε v)#μ ‖ π)` has derivative `-E_μ[𝒜_s v]` at `0`, where
`𝒜_s v = s(v) + div v` is the Stein operator. -/
theorem hasDerivAt_toReal_klDiv_map_add_smul {s : E → StrongDual ℝ E}
    (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ log (p y)) (s x) x) (hsc : ContinuousOn s Ω) :
    HasDerivAt (fun ε : ℝ ↦ (klDiv (μ.map fun x ↦ x + ε • v x)
        ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal)
      (-∫ x, (s x (v x) + divergence ℝ v x) ∂μ) 0 := by
  set ν := (vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := ae_mem_of_klDiv_ne_top hΩ.measurableSet hμ
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hD : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  -- The determinant along the lines `ε ↦ id + ε • A`.
  set J : ℝ → (E →L[ℝ] E) → ℝ := fun ε A ↦
    LinearMap.det ((ContinuousLinearMap.id ℝ E + ε • A : E →L[ℝ] E) : E →ₗ[ℝ] E)
  set dJ : ℝ → (E →L[ℝ] E) → ℝ := fun ε A ↦
    fderiv ℝ (fun B : E →L[ℝ] E ↦ LinearMap.det (B : E →ₗ[ℝ] E))
      (ContinuousLinearMap.id ℝ E + ε • A) A
  have hJT (ε : ℝ) (x : E) : (fderiv ℝ (fun y ↦ y + ε • v y) x).det = J ε (fderiv ℝ v x) := by
    rw [(hasFDerivAt_add_smul (ε := ε) (hvd x)).fderiv]
  have hJc : Continuous fun q : ℝ × (E →L[ℝ] E) ↦ J q.1 q.2 := continuous_det_id_add_smul
  have hdJc : Continuous fun q : ℝ × (E →L[ℝ] E) ↦ dJ q.1 q.2 :=
    ((ContinuousLinearMap.contDiff_det (𝕜 := ℝ) (E := E) (r := 1)).continuous_fderiv
      one_ne_zero |>.comp continuous_id_add_smul).clm_apply continuous_snd
  -- Uniform bounds on the compact set `[-1, 1] × Dv(Ω)`.
  have hKD : IsCompact (fderiv ℝ v '' Ω) := hΩ.image hD
  obtain ⟨Md, hMd⟩ := (isCompact_Icc.prod hKD).exists_bound_of_continuousOn hdJc.continuousOn
  obtain ⟨S, hS⟩ := hΩ.exists_bound_of_continuousOn hsc
  obtain ⟨V, hV⟩ := hΩ.exists_bound_of_continuousOn hvd.continuous.continuousOn
  -- The radius `ε₀` below which `ε ∈ [-1, 1]`, `I + ε v` is a homeomorphism and its Jacobian is at
  -- least `1 / 2` on `Ω`.
  have hI : ∀ᶠ ε : ℝ in 𝓝 0, ε ∈ Icc (-1 : ℝ) 1 := Icc_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨ε₀, hε₀, hε₀'⟩ := Metric.eventually_nhds_iff_ball.1
    ((eventually_lt_one_and_half_le_det (K := K) hΩ hv).and hI)
  have hεK {ε : ℝ} (hε : ε ∈ Metric.ball (0 : ℝ) ε₀) : ‖ε‖₊ * K < 1 := (hε₀' ε hε).1.1
  have hJ {ε : ℝ} (hε : ε ∈ Metric.ball (0 : ℝ) ε₀) {x : E} (hx : x ∈ Ω) :
      1 / 2 ≤ J ε (fderiv ℝ v x) :=
    hJT ε x ▸ (hε₀' ε hε).1.2 x hx
  -- For small `ε`, the Kullback–Leibler divergence is given by the change of variables.
  set G : ℝ → E → ℝ := fun ε x ↦ log (p (x + ε • v x)) - log (p x) + log (J ε (fderiv ℝ v x))
  set C := (klDiv μ ν).toReal
  have hev : (fun ε : ℝ ↦ (klDiv (μ.map fun x ↦ x + ε • v x) ν).toReal) =ᶠ[nhds 0]
      fun ε ↦ C - ∫ x, G ε x ∂μ := by
    filter_upwards [Metric.ball_mem_nhds 0 hε₀] with ε hε
    rw [toReal_klDiv_map_add_smul hvK hΩ hp hpc hp₀ hv hv₀ hμ (hεK hε)
      (fun x hx ↦ (hJT ε x).symm ▸ lt_of_lt_of_le (by norm_num) (hJ hε hx))]
    simp only [hJT, G, C, ν]
  -- The derivative of the integrand.
  set G' : ℝ → E → ℝ := fun ε x ↦ s (x + ε • v x) (v x) + dJ ε (fderiv ℝ v x) / J ε (fderiv ℝ v x)
  have hG'0 (x : E) : G' 0 x = (s x (v x) + divergence ℝ v x) := by
    simp [G', dJ, J, fderiv_det_id_apply, divergence]
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := G) (F' := G')
    (x₀ := 0) (s := Metric.ball 0 ε₀) (bound := fun _ ↦ S * V + 2 * Md)
    (Metric.ball_mem_nhds 0 hε₀) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [neg_eq_zero_sub]
    refine ((hasDerivAt_const 0 C).sub (?_ : HasDerivAt (fun ε : ℝ ↦ ∫ x, G ε x ∂μ)
      (∫ x, (s x (v x) + divergence ℝ v x) ∂μ) 0)).congr_of_eventuallyEq hev
    simpa [integral_congr_ae (.of_forall hG'0)] using hint.2
  · -- Measurability of the integrand.
    refine .of_forall fun ε ↦ Measurable.aestronglyMeasurable ?_
    have hJm : Measurable fun x ↦ J ε (fderiv ℝ v x) :=
      (hJc.comp (continuous_const.prodMk hD)).measurable
    exact ((measurable_log.comp (hp.comp (measurable_id.add
      (measurable_const.smul hvd.continuous.measurable)))).sub (measurable_log.comp hp)).add
      (measurable_log.comp hJm)
  · -- The integrand vanishes at `ε = 0`.
    have hG0 : G 0 = 0 := funext fun x ↦ by simp [G, J]
    rw [hG0]
    exact integrable_zero _ _ _
  · -- Measurability of the derivative at `0`, which is the Stein operator.
    rw [funext hG'0]
    exact (((hsc.clm_apply hvd.continuous.continuousOn).add
      hv.continuous_divergence.continuousOn).integrable_of_ae_mem hΩ hμΩ).aestronglyMeasurable
  · -- Domination of the derivative.
    filter_upwards [hμΩ] with x hx ε hε
    have hT : x + ε • v x ∈ Ω := hvK.add_smul_mem_of_forall_frontier_eq_zero (hεK hε) hv₀ hx
    have hJx := hJ hε hx
    have hdJx : ‖dJ ε (fderiv ℝ v x)‖ ≤ Md :=
      hMd (ε, fderiv ℝ v x) ⟨(hε₀' ε hε).2, mem_image_of_mem _ hx⟩
    have hMd₀ : 0 ≤ Md := (norm_nonneg _).trans hdJx
    have h₁ : ‖s (x + ε • v x) (v x)‖ ≤ S * V := (s _).le_of_opNorm_le_of_le (hS _ hT) (hV x hx)
    have h₂ : ‖dJ ε (fderiv ℝ v x) / J ε (fderiv ℝ v x)‖ ≤ 2 * Md := by
      rw [norm_div, Real.norm_of_nonneg (r := J ε (fderiv ℝ v x)) (by linarith)]
      calc ‖dJ ε (fderiv ℝ v x)‖ / J ε (fderiv ℝ v x) ≤ Md / J ε (fderiv ℝ v x) :=
            div_le_div_of_nonneg_right hdJx (by linarith)
        _ ≤ Md / (1 / 2) := div_le_div_of_nonneg_left hMd₀ (by norm_num) hJx
        _ = 2 * Md := by ring
    exact (norm_add_le _ _).trans (add_le_add h₁ h₂)
  · exact integrable_const _
  · -- Differentiability of the integrand.
    filter_upwards [hμΩ] with x hx ε hε
    have hJx := hJ hε hx
    -- The term `log p (x + ε • v x)`.
    have hline : HasDerivAt (fun ε : ℝ ↦ x + ε • v x) (v x) ε := by
      simpa using ((hasDerivAt_id ε).smul_const (v x)).const_add x
    have h₁ : HasDerivAt (fun ε ↦ log (p (x + ε • v x))) (s (x + ε • v x) (v x)) ε := by
      refine hasDerivAt_log_comp_of_mem_interior_or_const hs hline ?_
      by_cases hxi : x ∈ interior Ω
      · exact .inl (hvK.add_smul_mem_of_forall_frontier_eq_zero (hεK hε)
          (fun y hy ↦ hv₀ y (frontier_interior_subset hy)) hxi)
      · have hvx : v x = 0 := hv₀ x ⟨subset_closure hx, hxi⟩
        exact .inr ⟨funext fun τ ↦ by simp [hvx], hvx⟩
    have := (h₁.fun_sub (hasDerivAt_const ε (log (p x)))).fun_add
      ((hasDerivAt_det_id_add_smul (fderiv ℝ v x) ε).log (by linarith))
    simpa only [sub_zero] using this

end Perturbation

end InformationTheory
