/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import SBS.Probability.SVGD.MeanField
public import SBS.Probability.SVGD.SteinDiscrepancy
public import SBS.Probability.Stein.Dissipation

/-!
# The Kullback–Leibler divergence decreases along SVGD

Let `Ω ⊆ ℝᵈ` be compact and let `π = p · λ|_Ω`, where `p` is continuous and positive on `Ω` and
`log p` has derivative `s` in the interior of `Ω`, with `s` continuous on `Ω`. Let `Φ` be an
admissible feature map, let `m : ℝ → 𝓗` be a continuous bounded curve of update directions with
flow `Tₜ = trajectory Φ m 0 · t`, and let `μ` be a probability measure with `KL(μ ‖ π) < ∞`. Then
`μₜ = (Tₜ)#μ` satisfies `KL(μₜ ‖ π) < ∞` (`SVGD.klDiv_map_trajectory_ne_top`) and

  `∂ₜ KL(μₜ ‖ π) = -⟪m t, φ*_{μₜ}⟫`

(`SVGD.hasDerivAt_toReal_klDiv_map_trajectory`). For the mean-field SVGD flow, where
`m t = φ*_{μₜ}` for `t ≥ 0` (`SVGD.exists_meanField`), this is Theorem A.11 of [Serre2025]:

* `∂ₜ KL(μₜ ‖ π) = -𝔎(μₜ)` for `t ≥ 0`
  (`SVGD.hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction`);
* `KL(μₜ ‖ π) = KL(μ ‖ π) - ∫₀ᵗ 𝔎(μ_τ) dτ` (`SVGD.toReal_klDiv_map_trajectory_eq`);
* consequently, `t ↦ KL(μₜ ‖ π)` is antitone on `[0, ∞)`
  (`SVGD.antitoneOn_toReal_klDiv_map_trajectory`), `τ ↦ 𝔎(μ_τ)` is integrable on `[0, t]`
  (`SVGD.intervalIntegrable_kernelSteinDiscrepancy`) and `∫₀ᵗ 𝔎(μ_τ) dτ ≤ KL(μ ‖ π)`
  (`SVGD.integral_kernelSteinDiscrepancy_le`).

The last bound is the starting point of the convergence analysis of SVGD (Theorem 3.1 of
[Serre2025]). The proof is Lagrangian (`InformationTheory.hasDerivAt_toReal_klDiv_map_flow`): no
density or continuity equation is needed for `μₜ`.

## Main statements

* `SVGD.hasDerivAt_toReal_klDiv_map_trajectory`: the dissipation of the Kullback–Leibler
  divergence along the flow of any curve of update directions.
* `SVGD.hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction`: **Theorem A.11**,
  `∂ₜ KL(μₜ ‖ π) = -𝔎(μₜ)` along the mean-field SVGD flow.
* `SVGD.toReal_klDiv_map_trajectory_eq`: the integrated form.

## References

* [Q. Liu, *Stein Variational Gradient Descent as Gradient Flow*][Liu2017]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Theorem A.11
-/

@[expose] public section

open MeasureTheory Set Function InformationTheory

open scoped NNReal ENNReal RealInnerProductSpace

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
  {Φ : EuclideanSpace ℝ (Fin d) → H₀} {m : ℝ → 𝓗[d, H₀]}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {Ω : Set (EuclideanSpace ℝ (Fin d))} {K C B : ℝ≥0} {p : EuclideanSpace ℝ (Fin d) → ℝ}
  {π μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
  (hΦ : AdmissibleFeatureMap Φ Ω K C) (hΩ : IsCompact Ω)
  (hπ : π = (volume.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x))
  (hp : Measurable p) (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x) (hμ : klDiv μ π ≠ ∞)
  (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B)
include hΦ hΩ hπ hp hpc hp₀ hμ hm hmB

/-- **The flow of SVGD preserves the finiteness of the Kullback–Leibler divergence.** -/
theorem klDiv_map_trajectory_ne_top (t : ℝ) : klDiv (μ.map (trajectory Φ m 0 · t)) π ≠ ∞ := by
  subst hπ
  exact klDiv_map_flow_ne_top hΩ hp hpc hp₀ (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField hΦ.lipschitzWith (hmB t))
    (fun t y ↦ hasFDerivAt_toVectorField (hΦ.contDiff.differentiable one_ne_zero y).hasFDerivAt)
    (continuous_uncurry_pairing_comp_fderiv hΦ.contDiff hm)
    (fun t y hy ↦ toVectorField_eq_zero_of_eq_zero (hΦ.eq_zero_of_mem_frontier y hy))
    (hasDerivAt_trajectory hm hmB hΦ.lipschitzWith hΦ.norm_le 0)
    (trajectory_self hm hmB hΦ.lipschitzWith hΦ.norm_le 0) hμ t

variable [CompleteSpace H₀] (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ Real.log (p y)) (s x) x)
  (hsc : ContinuousOn s Ω)
include hs hsc

omit [CompleteSpace H₀] hp hpc hp₀ hs in
/-- Along the flow, the Stein feature map is integrable against `μₜ`. -/
private theorem integrable_steinFeature_map_trajectory (t : ℝ) :
    Integrable (steinFeature Φ s) (μ.map (trajectory Φ m 0 · t)) := by
  have hμΩ : ∀ᵐ x ∂μ, x ∈ Ω := ae_mem_of_klDiv_ne_top hΩ.measurableSet (hπ ▸ hμ)
  exact integrable_steinFeature hΩ hΦ.contDiff hsc (ae_mem_map hΩ hμΩ
    (continuous_trajectory_apply hm hmB hΦ.lipschitzWith hΦ.norm_le 0 t) fun x hx ↦
      trajectory_mem hm hmB hΦ.lipschitzWith hΦ.norm_le hΩ.isClosed hΦ.eq_zero_of_mem_frontier
        hx t)

omit hp hpc hp₀ hs in
/-- Along the flow, `𝔎(μₜ) = ‖φ*_{μₜ}‖²`. -/
private theorem kernelSteinDiscrepancy_map_trajectory (t : ℝ) :
    kernelSteinDiscrepancy Φ s (μ.map (trajectory Φ m 0 · t)) =
      ‖direction Φ s (μ.map (trajectory Φ m 0 · t))‖ ^ 2 :=
  kernelSteinDiscrepancy_eq (.of_forall (hΦ.contDiff.differentiable one_ne_zero))
    (integrable_steinFeature_map_trajectory hΦ hΩ hπ hμ hm hmB hsc t)

/-- **The dissipation of the Kullback–Leibler divergence along the flow of `m`.** The map
`t ↦ KL(μₜ ‖ π)` has derivative `-⟪m t, φ*_{μₜ}⟫` at every time `t`. -/
theorem hasDerivAt_toReal_klDiv_map_trajectory (t : ℝ) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal)
      (-⟪m t, direction Φ s (μ.map (trajectory Φ m 0 · t))⟫) t := by
  rw [← integral_steinOperator_eq_inner (.of_forall (hΦ.contDiff.differentiable one_ne_zero))
    (integrable_steinFeature_map_trajectory hΦ hΩ hπ hμ hm hmB hsc t)]
  subst hπ
  exact hasDerivAt_toReal_klDiv_map_flow hΩ hp hpc hp₀ (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField hΦ.lipschitzWith (hmB t))
    (fun t y ↦ hasFDerivAt_toVectorField (hΦ.contDiff.differentiable one_ne_zero y).hasFDerivAt)
    (continuous_uncurry_pairing_comp_fderiv hΦ.contDiff hm)
    (fun t y hy ↦ toVectorField_eq_zero_of_eq_zero (hΦ.eq_zero_of_mem_frontier y hy))
    (hasDerivAt_trajectory hm hmB hΦ.lipschitzWith hΦ.norm_le 0)
    (trajectory_self hm hmB hΦ.lipschitzWith hΦ.norm_le 0) hμ hs hsc t

variable (hmφ : ∀ t, 0 ≤ t → m t = direction Φ s (μ.map (trajectory Φ m 0 · t)))
include hmφ

/-- Along the mean-field SVGD flow, `t ↦ KL(μₜ ‖ π)` has derivative `-‖m t‖²` for `t ≥ 0`. -/
private theorem hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction' {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal) (-‖m t‖ ^ 2) t := by
  have := hasDerivAt_toReal_klDiv_map_trajectory hΦ hΩ hπ hp hpc hp₀ hμ hm hmB hs hsc t
  rwa [← hmφ t ht, real_inner_self_eq_norm_sq] at this

omit hp hpc hp₀ hs in
/-- Along the mean-field SVGD flow, `𝔎(μₜ) = ‖m t‖²` for `t ≥ 0`. -/
private theorem kernelSteinDiscrepancy_map_trajectory_eq {t : ℝ} (ht : 0 ≤ t) :
    kernelSteinDiscrepancy Φ s (μ.map (trajectory Φ m 0 · t)) = ‖m t‖ ^ 2 := by
  rw [kernelSteinDiscrepancy_map_trajectory hΦ hΩ hπ hμ hm hmB hsc, ← hmφ t ht]

/-- **The Kullback–Leibler divergence decreases along SVGD** (Theorem A.11). Along the mean-field
SVGD flow, `∂ₜ KL(μₜ ‖ π) = -𝔎(μₜ)` for every `t ≥ 0`. -/
theorem hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal)
      (-kernelSteinDiscrepancy Φ s (μ.map (trajectory Φ m 0 · t))) t := by
  rw [kernelSteinDiscrepancy_map_trajectory_eq hΦ hΩ hπ hμ hm hmB hsc hmφ ht]
  exact hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction' hΦ hΩ hπ hp hpc hp₀ hμ hm hmB hs
    hsc hmφ ht

omit hp hpc hp₀ hs in
/-- Along the mean-field SVGD flow, `τ ↦ 𝔎(μ_τ)` is integrable on `[0, t]`. -/
theorem intervalIntegrable_kernelSteinDiscrepancy {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ ↦ kernelSteinDiscrepancy Φ s (μ.map (trajectory Φ m 0 · τ)))
      volume 0 t :=
  ((hm.norm.pow 2).intervalIntegrable 0 t).congr fun τ hτ ↦ by
    rw [uIoc_of_le ht] at hτ
    exact (kernelSteinDiscrepancy_map_trajectory_eq hΦ hΩ hπ hμ hm hmB hsc hmφ hτ.1.le).symm

/-- **The integrated form of Theorem A.11.** Along the mean-field SVGD flow,
`KL(μₜ ‖ π) = KL(μ ‖ π) - ∫₀ᵗ 𝔎(μ_τ) dτ` for every `t ≥ 0`. -/
theorem toReal_klDiv_map_trajectory_eq {t : ℝ} (ht : 0 ≤ t) :
    (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal =
      (klDiv μ π).toReal -
        ∫ τ in 0..t, kernelSteinDiscrepancy Φ s (μ.map (trajectory Φ m 0 · τ)) := by
  have hτ {τ : ℝ} (hτ : τ ∈ uIcc 0 t) : 0 ≤ τ := by
    rw [uIcc_of_le ht] at hτ
    exact hτ.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ hτ' ↦
    hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction' hΦ hΩ hπ hp hpc hp₀ hμ hm hmB hs hsc
      hmφ (hτ hτ')) ((hm.norm.pow 2).neg.intervalIntegrable 0 t)
  have h₀ : (trajectory Φ m 0 · 0) = id :=
    funext (trajectory_self hm hmB hΦ.lipschitzWith hΦ.norm_le 0)
  rw [h₀, Measure.map_id, intervalIntegral.integral_neg] at hFTC
  have hK : ∫ τ in 0..t, kernelSteinDiscrepancy Φ s (μ.map (trajectory Φ m 0 · τ)) =
      ∫ τ in 0..t, ‖m τ‖ ^ 2 := intervalIntegral.integral_congr fun τ hτ' ↦
    kernelSteinDiscrepancy_map_trajectory_eq hΦ hΩ hπ hμ hm hmB hsc hmφ (hτ hτ')
  rw [hK]
  linarith

/-- Along the mean-field SVGD flow, `t ↦ KL(μₜ ‖ π)` is antitone on `[0, ∞)`. -/
theorem antitoneOn_toReal_klDiv_map_trajectory :
    AntitoneOn (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t)) π).toReal) (Ici 0) := by
  have hderiv {t : ℝ} (ht : 0 ≤ t) := hasDerivAt_toReal_klDiv_map_trajectory_of_eq_direction' hΦ
    hΩ hπ hp hpc hp₀ hμ hm hmB hs hsc hmφ ht
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun t ht ↦ (hderiv ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv (interior_subset ht)).differentiableAt.differentiableWithinAt)
    fun t ht ↦ ?_
  rw [(hderiv (interior_subset ht)).deriv, neg_nonpos]
  positivity

/-- **Integrated bound on the kernelized Stein discrepancy.** Along the mean-field SVGD flow,
`∫₀ᵗ 𝔎(μ_τ) dτ ≤ KL(μ ‖ π)` for every `t ≥ 0`. -/
theorem integral_kernelSteinDiscrepancy_le {t : ℝ} (ht : 0 ≤ t) :
    ∫ τ in 0..t, kernelSteinDiscrepancy Φ s (μ.map (trajectory Φ m 0 · τ)) ≤
      (klDiv μ π).toReal := by
  have := toReal_klDiv_map_trajectory_eq hΦ hΩ hπ hp hpc hp₀ hμ hm hmB hs hsc hmφ ht
  linarith [ENNReal.toReal_nonneg (a := klDiv (μ.map (trajectory Φ m 0 · t)) π)]

end SVGD
