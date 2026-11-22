/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Analysis.Calculus.FDeriv.DetIdAddSMul
public import SBS.Analysis.Normed.PerturbationOfIdentity
public import SBS.InformationTheory.KullbackLeibler.Reweighting
public import SBS.Probability.Stein.Operator
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The first variation of the Kullback–Leibler divergence

Let `Ω` be a compact subset of a finite-dimensional real normed space `E` with an additive Haar
measure `vol`, and let `π = p · vol|_Ω` be a measure with a density `p`, positive and continuous
on `Ω`, whose logarithm has derivative `s` in the interior of `Ω`. Let `v : E → E` be a `C¹`
Lipschitz vector field vanishing on the frontier of `Ω`, and let `μ` be a probability measure with
`KL(μ ‖ π) < ∞`. For small `ε`, the perturbation `Tε = I + ε v` of the identity is a
homeomorphism of `E` mapping `Ω` onto `Ω`, and

  `KL(Tε#μ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ Tε - log p + log det DTε) dμ`

(`InformationTheory.toReal_klDiv_map_add_smul`). No density is needed for `μ`: transporting `μ`
forward amounts to transporting `π` backwards, and `Tε⁻¹#π` has density
`(p ∘ Tε) · det DTε / p` with respect to `π` by the change of variables formula
(`InformationTheory.map_symm_addSMulHomeomorph_eq_withDensity`).

## Main statements

* `InformationTheory.map_symm_addSMulHomeomorph_eq_withDensity`: the density of `Tε⁻¹#π`.
* `InformationTheory.toReal_klDiv_map_add_smul`: the Kullback–Leibler divergence of `Tε#μ`.
* `InformationTheory.hasDerivAt_klDiv_map_add_smul`: **the first variation**,
  `∂ε KL(Tε#μ ‖ π)|_{ε=0} = -E_μ[𝒜_s v]`.

## References

* [Q. Liu, D. Wang, *Stein Variational Gradient Descent*][Liu2016SVGD]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Theorem A.8
-/

@[expose] public section

open MeasureTheory Set Real

open scoped NNReal ENNReal

namespace InformationTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {vol : Measure E} [vol.IsAddHaarMeasure] {Ω : Set E}
  {p : E → ℝ} {v : E → E} {K : ℝ≥0} {ε : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasFDerivAt_add_smul {x : E} (hv : DifferentiableAt ℝ v x) :
    HasFDerivAt (fun y ↦ y + ε • v y) (ContinuousLinearMap.id ℝ E + ε • fderiv ℝ v x) x :=
  (hasFDerivAt_id x).add (hv.hasFDerivAt.const_smul ε)

/-- **The backward transport of `π`.** For small `ε`, the image of `π = p · vol|_Ω` by the inverse
of `Tε = I + ε v` has density `(p ∘ Tε) · det DTε / p` with respect to `π`. -/
theorem map_symm_addSMulHomeomorph_eq_withDensity (hvK : LipschitzWith K v)
    (hε : ‖ε‖₊ * K < 1) (hΩ : IsClosed Ω) (hp : Measurable p) (hp₀ : ∀ x ∈ Ω, 0 < p x)
    (hv : Differentiable ℝ v) (hv₀ : ∀ y ∈ frontier Ω, v y = 0)
    (hdet : ∀ x ∈ Ω, 0 < (fderiv ℝ (fun y ↦ y + ε • v y) x).det) :
    ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)).map (hvK.addSMulHomeomorph hε).symm =
      ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)).withDensity fun x ↦
        .ofReal (p (x + ε • v x) * (fderiv ℝ (fun y ↦ y + ε • v y) x).det / p x) := by
  set T := hvK.addSMulHomeomorph hε
  have hT : ∀ x, HasFDerivAt T (fderiv ℝ (fun y ↦ y + ε • v y) x) x := fun x ↦
    (hasFDerivAt_add_smul (hv x)).differentiableAt.hasFDerivAt
  have hdetm : Measurable fun x ↦ (fderiv ℝ (fun y ↦ y + ε • v y) x).det :=
    (ContinuousLinearMap.contDiff_det (𝕜 := ℝ) (E := E) (r := 0)).continuous.measurable.comp
      (measurable_fderiv ℝ _)
  have hw : Measurable fun x ↦ p (x + ε • v x) * (fderiv ℝ (fun y ↦ y + ε • v y) x).det / p x :=
    ((hp.comp T.continuous.measurable).mul hdetm).div hp
  ext A hA
  have hTA : MeasurableSet (⇑T '' A) := T.measurableEmbedding.measurableSet_image.2 hA
  rw [Measure.map_apply T.symm.continuous.measurable hA, Homeomorph.preimage_symm,
    withDensity_apply _ hTA, Measure.restrict_restrict hTA,
    withDensity_apply _ hA, setLIntegral_withDensity_eq_setLIntegral_mul _
      hp.ennreal_ofReal hw.ennreal_ofReal hA,
    Measure.restrict_restrict hA]
  have himage : ⇑T '' A ∩ Ω = ⇑T '' (A ∩ Ω) := by
    rw [image_inter T.injective, hvK.addSMulHomeomorph_image hε hΩ hv₀]
  rw [himage, lintegral_image_eq_lintegral_abs_det_fderiv_mul vol (hA.inter hΩ.measurableSet)
    (fun x _ ↦ (hT x).hasFDerivWithinAt) T.injective.injOn]
  refine setLIntegral_congr_fun (hA.inter hΩ.measurableSet) fun x hx ↦ ?_
  simp only [Pi.mul_apply]
  rw [abs_of_pos (hdet x hx.2), ← ENNReal.ofReal_mul (hdet x hx.2).le, ← ENNReal.ofReal_mul
    (hp₀ x hx.2).le, mul_div_cancel₀ _ (hp₀ x hx.2).ne', mul_comm]
  rfl

/-- **The Kullback–Leibler divergence of a perturbed measure.** Let `π = p · vol|_Ω`, with `Ω`
compact and `p` continuous and positive on `Ω`, let `v` be a `C¹` `K`-Lipschitz vector field
vanishing on the frontier of `Ω`, and let `μ` be a probability measure with `KL(μ ‖ π) < ∞`. If
`|ε| K < 1` and the Jacobian determinant of `Tε = I + ε v` is positive on `Ω`, then
`KL(Tε#μ ‖ π) = KL(μ ‖ π) - ∫ (log p ∘ Tε - log p + log det DTε) dμ`. -/
theorem toReal_klDiv_map_add_smul {μ : Measure E} [IsProbabilityMeasure μ]
    (hvK : LipschitzWith K v) (hε : ‖ε‖₊ * K < 1) (hΩ : IsCompact Ω) (hp : Measurable p)
    (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x) (hv : ContDiff ℝ 1 v)
    (hv₀ : ∀ y ∈ frontier Ω, v y = 0)
    (hdet : ∀ x ∈ Ω, 0 < (fderiv ℝ (fun y ↦ y + ε • v y) x).det)
    (hμ : klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞) :
    (klDiv (μ.map fun x ↦ x + ε • v x)
        ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal =
      (klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal -
        ∫ x, (log (p (x + ε • v x)) - log (p x) +
          log (fderiv ℝ (fun y ↦ y + ε • v y) x).det) ∂μ := by
  set ν := (vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  set T := hvK.addSMulHomeomorph hε
  obtain ⟨hμν, hllr⟩ := klDiv_ne_top_iff.1 hμ
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity_ofReal (hpc.integrableOn_compact hΩ).hasFiniteIntegral
  have hνΩ : ∀ᵐ x ∂ν, x ∈ Ω :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ.measurableSet)
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := hμν.ae_le hνΩ
  have hTΩ {x : E} (hx : x ∈ Ω) : x + ε • v x ∈ Ω := hvK.add_smul_mem hε hΩ.isClosed hv₀ hx
  -- The weight `w = (p ∘ Tε) · det DTε / p`, its measurability, positivity and integrability.
  set w : E → ℝ := fun x ↦ p (x + ε • v x) * (fderiv ℝ (fun y ↦ y + ε • v y) x).det / p x
  have hdetc : Continuous fun x ↦ (fderiv ℝ (fun y ↦ y + ε • v y) x).det :=
    (ContinuousLinearMap.contDiff_det (𝕜 := ℝ) (E := E) (r := 0)).continuous.comp
      ((contDiff_id.add (hv.const_smul ε)).continuous_fderiv one_ne_zero)
  have hw : Measurable w := ((hp.comp T.continuous.measurable).mul hdetc.measurable).div hp
  have hw₀ {x : E} (hx : x ∈ Ω) : 0 < w x :=
    div_pos (mul_pos (hp₀ _ (hTΩ hx)) (hdet x hx)) (hp₀ x hx)
  have hwc : ContinuousOn w Ω :=
    ((hpc.comp T.continuous.continuousOn fun _ hx ↦ hTΩ hx).mul hdetc.continuousOn).div hpc
      fun x hx ↦ (hp₀ x hx).ne'
  have hlog : Integrable (fun x ↦ log (w x)) μ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hμΩ]
    exact (hwc.log fun x hx ↦ (hw₀ hx).ne').integrableOn_compact hΩ
  -- Transport the first argument forward, or the second one backwards.
  have hνT := map_symm_addSMulHomeomorph_eq_withDensity (vol := vol) hvK hε hΩ.isClosed hp hp₀
    (hv.differentiable one_ne_zero) hv₀ hdet
  have : IsFiniteMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
    rw [← hνT]
    infer_instance
  have hmass : (ν.withDensity fun x ↦ ENNReal.ofReal (w x)).real univ = ν.real univ := by
    rw [← hνT, measureReal_def, Measure.map_apply T.symm.continuous.measurable MeasurableSet.univ,
      preimage_univ, measureReal_def]
  have hmap : μ.map (fun x ↦ x + ε • v x) = μ.map T.toMeasurableEquiv := rfl
  rw [hmap, klDiv_map_measurableEquiv_left, Homeomorph.toMeasurableEquiv_symm_coe, hνT,
    toReal_klDiv_withDensity_right hμν hllr hw (hνΩ.mono fun _ hx ↦ hw₀ hx) hlog, hmass]
  -- The logarithm of the weight.
  have hlogw : (fun x ↦ log (w x)) =ᵐ[μ] fun x ↦ log (p (x + ε • v x)) - log (p x) +
      log (fderiv ℝ (fun y ↦ y + ε • v y) x).det := by
    filter_upwards [hμΩ] with x hx
    rw [log_div (mul_pos (hp₀ _ (hTΩ hx)) (hdet x hx)).ne' (hp₀ x hx).ne',
      log_mul (hp₀ _ (hTΩ hx)).ne' (hdet x hx).ne']
    ring
  rw [integral_congr_ae hlogw]
  ring

/-- **The first variation of the Kullback–Leibler divergence.** Let `π = p · vol|_Ω`, with `Ω`
compact, `p` continuous and positive on `Ω`, and `log p` differentiable in the interior of `Ω` with
derivative `s`, continuous on `Ω`. Let `v` be a `C¹` Lipschitz vector field vanishing on the
frontier of `Ω`, and let `μ` be a probability measure with `KL(μ ‖ π) < ∞`. Then
`ε ↦ KL((I + ε v)#μ ‖ π)` has derivative `-E_μ[𝒜_s v]` at `0`, where
`𝒜_s v = s(v) + div v` is the Stein operator. -/
theorem hasDerivAt_klDiv_map_add_smul {μ : Measure E} [IsProbabilityMeasure μ]
    {s : E → StrongDual ℝ E} (hvK : LipschitzWith K v) (hΩ : IsCompact Ω) (hp : Measurable p)
    (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x)
    (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ log (p y)) (s x) x) (hsc : ContinuousOn s Ω)
    (hv : ContDiff ℝ 1 v) (hv₀ : ∀ y ∈ frontier Ω, v y = 0)
    (hμ : klDiv μ ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x)) ≠ ∞) :
    HasDerivAt (fun ε : ℝ ↦ (klDiv (μ.map fun x ↦ x + ε • v x)
        ((vol.restrict Ω).withDensity fun x ↦ .ofReal (p x))).toReal)
      (-∫ x, ProbabilityTheory.steinOperator s v x ∂μ) 0 := by
  set ν := (vol.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := (klDiv_ne_top_iff.1 hμ).1.ae_le
    ((withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ.measurableSet))
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
  have hJc : Continuous fun q : ℝ × (E →L[ℝ] E) ↦ J q.1 q.2 :=
    (ContinuousLinearMap.contDiff_det (𝕜 := ℝ) (E := E) (r := 0)).continuous.comp
      (continuous_const.add (continuous_fst.smul continuous_snd))
  have hdJc : Continuous fun q : ℝ × (E →L[ℝ] E) ↦ dJ q.1 q.2 :=
    ((ContinuousLinearMap.contDiff_det (𝕜 := ℝ) (E := E) (r := 1)).continuous_fderiv
      one_ne_zero |>.comp (continuous_const.add (continuous_fst.smul continuous_snd))).clm_apply
      continuous_snd
  -- Uniform bounds on the compact set `[-1, 1] × Dv(Ω)`.
  have hKD : IsCompact (fderiv ℝ v '' Ω) := hΩ.image hD
  have hQ : IsCompact (Icc (-1 : ℝ) 1 ×ˢ (fderiv ℝ v '' Ω)) := isCompact_Icc.prod hKD
  obtain ⟨δ, hδ, hδJ⟩ := Metric.uniformContinuousOn_iff.1
    (hQ.uniformContinuousOn_of_continuous hJc.continuousOn) (1 / 2) (by norm_num)
  obtain ⟨Md, hMd⟩ := hQ.exists_bound_of_continuousOn hdJc.continuousOn
  obtain ⟨S, hS⟩ := hΩ.exists_bound_of_continuousOn hsc
  obtain ⟨V, hV⟩ := hΩ.exists_bound_of_continuousOn hvd.continuous.continuousOn
  -- The radius `ε₀` below which `I + ε v` is a homeomorphism with Jacobian at least `1 / 2`.
  set ε₀ : ℝ := min (min δ 1) (1 / (K + 1))
  have hε₀ : 0 < ε₀ := lt_min (lt_min hδ one_pos) (by positivity)
  have hεK {ε : ℝ} (hε : ε ∈ Metric.ball (0 : ℝ) ε₀) : ‖ε‖₊ * K < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_mul, coe_nnNorm, NNReal.coe_one]
    have h1 : ‖ε‖ < 1 / (K + 1) := by
      simpa using (mem_ball_zero_iff.1 hε).trans_le (min_le_right _ _)
    calc ‖ε‖ * K ≤ 1 / (K + 1) * K := by gcongr
      _ < 1 := by rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
  have hJ {ε : ℝ} (hε : ε ∈ Metric.ball (0 : ℝ) ε₀) {x : E} (hx : x ∈ Ω) :
      1 / 2 ≤ J ε (fderiv ℝ v x) := by
    have hε' : |ε| < min δ 1 := by simpa using (mem_ball_zero_iff.1 hε).trans_le (min_le_left _ _)
    have h := hδJ (ε, fderiv ℝ v x)
      ⟨⟨by linarith [neg_abs_le ε, lt_min_iff.1 hε'], by linarith [le_abs_self ε, lt_min_iff.1 hε']⟩,
        mem_image_of_mem _ hx⟩
      (0, fderiv ℝ v x) ⟨⟨by norm_num, by norm_num⟩, mem_image_of_mem _ hx⟩
      (by simpa [Prod.dist_eq] using (lt_min_iff.1 hε').1)
    have h0 : J 0 (fderiv ℝ v x) = 1 := by simp [J]
    rw [h0, Real.dist_eq] at h
    linarith [abs_lt.1 h]
  -- For small `ε`, the Kullback–Leibler divergence is given by the change of variables.
  set G : ℝ → E → ℝ := fun ε x ↦ log (p (x + ε • v x)) - log (p x) + log (J ε (fderiv ℝ v x))
  set C := (klDiv μ ν).toReal
  have hev : (fun ε : ℝ ↦ (klDiv (μ.map fun x ↦ x + ε • v x) ν).toReal) =ᶠ[nhds 0]
      fun ε ↦ C - ∫ x, G ε x ∂μ := by
    filter_upwards [Metric.ball_mem_nhds 0 hε₀] with ε hε
    rw [toReal_klDiv_map_add_smul hvK (hεK hε) hΩ hp hpc hp₀ hv hv₀
      (fun x hx ↦ (hJT ε x).symm ▸ lt_of_lt_of_le (by norm_num) (hJ hε hx)) hμ]
    simp only [hJT, G, C, ν]
  -- The derivative of the integrand.
  set G' : ℝ → E → ℝ := fun ε x ↦ s (x + ε • v x) (v x) + dJ ε (fderiv ℝ v x) / J ε (fderiv ℝ v x)
  have hG'0 (x : E) : G' 0 x = ProbabilityTheory.steinOperator s v x := by
    simp only [G', dJ, J, zero_smul, add_zero, ContinuousLinearMap.coe_id, LinearMap.det_id,
      div_one, fderiv_det_id_apply, ProbabilityTheory.steinOperator, divergence]
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := G) (F' := G')
    (x₀ := 0) (s := Metric.ball 0 ε₀) (bound := fun _ ↦ S * V + 2 * Md)
    (Metric.ball_mem_nhds 0 hε₀) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [neg_eq_zero_sub]
    refine ((hasDerivAt_const 0 C).sub (?_ : HasDerivAt (fun ε : ℝ ↦ ∫ x, G ε x ∂μ)
      (∫ x, ProbabilityTheory.steinOperator s v x ∂μ) 0)).congr_of_eventuallyEq hev
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
    rw [funext hG'0, ← Measure.restrict_eq_self_of_ae_mem hμΩ]
    exact ((hsc.clm_apply hvd.continuous.continuousOn).add
      hv.continuous_divergence.continuousOn).aestronglyMeasurable hΩ.measurableSet
  · -- Domination of the derivative.
    filter_upwards [hμΩ] with x hx ε hε
    have hT : x + ε • v x ∈ Ω := hvK.add_smul_mem (hεK hε) hΩ.isClosed hv₀ hx
    have hε1 : ε ∈ Icc (-1 : ℝ) 1 := by
      have := (mem_ball_zero_iff.1 hε).trans_le ((min_le_left _ _).trans (min_le_right _ _))
      rw [Real.norm_eq_abs] at this
      exact ⟨by linarith [neg_abs_le ε], by linarith [le_abs_self ε]⟩
    have hJx := hJ hε hx
    have hdJx : ‖dJ ε (fderiv ℝ v x)‖ ≤ Md := hMd (ε, fderiv ℝ v x) ⟨hε1, mem_image_of_mem _ hx⟩
    have hMd₀ : 0 ≤ Md := (norm_nonneg _).trans hdJx
    have h₁ : ‖s (x + ε • v x) (v x)‖ ≤ S * V :=
      ((s (x + ε • v x)).le_opNorm (v x)).trans (mul_le_mul (hS _ hT) (hV x hx) (norm_nonneg _)
        ((norm_nonneg _).trans (hS _ hT)))
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
    set T := hvK.addSMulHomeomorph (hεK hε)
    have hJx := hJ hε hx
    -- The term `log p (x + ε • v x)`.
    have h₁ : HasDerivAt (fun ε ↦ log (p (x + ε • v x))) (s (x + ε • v x) (v x)) ε := by
      by_cases hxi : x ∈ interior Ω
      · have hTi : x + ε • v x ∈ interior Ω := by
          have hint : ⇑T '' interior Ω = interior Ω := by
            rw [T.image_interior, hvK.addSMulHomeomorph_image (hεK hε) hΩ.isClosed hv₀]
          exact hint ▸ mem_image_of_mem T hxi
        have hline : HasDerivAt (fun ε : ℝ ↦ x + ε • v x) (v x) ε := by
          simpa using ((hasDerivAt_id ε).smul_const (v x)).const_add x
        exact (hs _ hTi).comp_hasDerivAt ε hline
      · have hvx : v x = 0 := hv₀ x ⟨subset_closure hx, hxi⟩
        simpa [hvx] using hasDerivAt_const ε (log (p x))
    have := (h₁.fun_sub (hasDerivAt_const ε (log (p x)))).fun_add
      ((hasDerivAt_det_id_add_smul (fderiv ℝ v x) ε).log (by linarith))
    simpa only [sub_zero] using this

end InformationTheory
