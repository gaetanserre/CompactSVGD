/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Probability.SVGD.Regularity
public import SBS.Probability.SVGD.Trajectory
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Analysis.Convex.SchauderFixedPoint

/-!
# The mean-field SVGD equation on a compact time interval

Let `Ω ⊆ ℝᵈ` be compact and let `ν` be a probability measure concentrated on `Ω`. The mean-field
SVGD dynamics started from `ν` at time `a` is the McKean–Vlasov equation

  `∂ₜ Xₜ(x) = φ*_{μₜ}(Xₜ(x))`, `X_a = id`, `μₜ = (Xₜ)#ν`,

where `φ*_μ = SVGD.direction Φ s μ`. In terms of the curve `m t = φ*_{μₜ}` of update directions, a
solution is a fixed point of the map sending a curve `m` to `t ↦ φ*_{(Xᵐₜ)#ν}`, where `Xᵐ` is the
flow of the vector field of `m` (`SVGD.trajectory`).

This file proves that such a fixed point exists on every compact interval `[a, b]`
(`SVGD.exists_meanField_Icc`). The only assumption on the target distribution is that its score `s`
is continuous on `Ω`; in particular, no Lipschitz condition on `s` is needed, and no uniqueness is
claimed. The proof applies Schauder's fixed-point theorem in the Banach space of bounded continuous
curves `[a, b] → 𝓗`, on the closed convex set of curves with values in the closed convex hull `𝒦`
of `ξ(Ω)`, which is compact.

* The fixed-point map preserves this set, since every update direction lies in `𝒦`
  (`SVGD.direction_mem_closedConvexHull`) and trajectories stay in `Ω`.
* Its image is equicontinuous, since trajectories have bounded speed and `ξ` is uniformly
  continuous on `Ω`. With values in the compact set `𝒦`, the Arzelà–Ascoli theorem shows that it is
  relatively compact.
* It is continuous, since trajectories depend continuously on the curve (Grönwall's inequality).

## Main definitions

* `SVGD.AdmissibleFeatureMap Φ Ω K C`: `Φ` is `C¹`, `K`-Lipschitz, bounded by `C`, and vanishes on
  the frontier of `Ω`.

## Main statements

* `SVGD.norm_direction_map_sub_direction_map_le`: the update directions of two image measures
  are close when the two maps are uniformly close on `Ω`.
* `SVGD.exists_meanField_Icc`: existence of a solution of the mean-field SVGD equation on `[a, b]`.

## References

* [Q. Liu, *Stein Variational Gradient Descent as Gradient Flow*][Liu2017]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025]
-/

@[expose] public section

open MeasureTheory Set Metric Filter Function

open scoped NNReal Topology BoundedContinuousFunction

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- The product space `𝓗[d, H₀] = H₀ᵈ` of the update directions of SVGD. -/
local notation "𝓗[" d ", " H₀ "]" => PiLp 2 fun _ : Fin d ↦ H₀

/-- The assumptions on the feature map `Φ` of the kernel for the SVGD flow on `Ω`: `Φ` is `C¹`,
`K`-Lipschitz and bounded by `C`, and it vanishes on the frontier of `Ω`. The last condition makes
every update direction vanish on the frontier of `Ω`, so that the particles stay in `Ω`. Only the
values of `Φ` near `Ω` matter, so that the global conditions can always be met by modifying `Φ`
away from `Ω`. -/
structure AdmissibleFeatureMap (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (K C : ℝ≥0) : Prop where
  contDiff : ContDiff ℝ 1 Φ
  lipschitzWith : LipschitzWith K Φ
  norm_le : ∀ y, ‖Φ y‖ ≤ C
  eq_zero_of_mem_frontier : ∀ y ∈ frontier Ω, Φ y = 0

variable [CompleteSpace H₀] {Φ : EuclideanSpace ℝ (Fin d) → H₀}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {Ω : Set (EuclideanSpace ℝ (Fin d))} {K C : ℝ≥0}
  {ν : Measure (EuclideanSpace ℝ (Fin d))}

section ImageMeasure

variable (hΩ : IsCompact Ω) (hΦ : ContDiff ℝ 1 Φ) (hs : ContinuousOn s Ω)
  [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω)
include hΩ hν

omit [CompleteSpace H₀] [IsProbabilityMeasure ν] in
theorem ae_mem_map {X : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hX : Continuous X)
    (hXΩ : ∀ x ∈ Ω, X x ∈ Ω) :
    ∀ᵐ y ∂ν.map X, y ∈ Ω :=
  (ae_map_iff hX.aemeasurable hΩ.isClosed.measurableSet).2 (hν.mono hXΩ)

include hΦ hs

omit [CompleteSpace H₀] in
/-- **The update direction depends continuously on the transport map.** Let `X` and `Y` be
continuous maps preserving `Ω`. If `ξ` varies by at most `ε` on pairs of points of `Ω` at distance
less than `η`, and `X` and `Y` are at distance less than `η` on `Ω`, then the update directions of
`X#ν` and `Y#ν` are at distance at most `ε`. -/
theorem norm_direction_map_sub_direction_map_le
    {X Y : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hX : Continuous X)
    (hY : Continuous Y) (hXΩ : ∀ x ∈ Ω, X x ∈ Ω) (hYΩ : ∀ x ∈ Ω, Y x ∈ Ω) {ε η : ℝ}
    (hη : ∀ x ∈ Ω, ∀ y ∈ Ω, dist x y < η → dist (steinFeature Φ s x) (steinFeature Φ s y) ≤ ε)
    (hXY : ∀ x ∈ Ω, dist (X x) (Y x) < η) :
    ‖direction Φ s (ν.map X) - direction Φ s (ν.map Y)‖ ≤ ε := by
  have hξX := integrable_steinFeature hΩ hΦ hs (ae_mem_map hΩ hν hX hXΩ)
  have hξY := integrable_steinFeature hΩ hΦ hs (ae_mem_map hΩ hν hY hYΩ)
  have hξX' : Integrable (fun x ↦ steinFeature Φ s (X x)) ν :=
    hξX.comp_aemeasurable hX.aemeasurable
  have hξY' : Integrable (fun x ↦ steinFeature Φ s (Y x)) ν :=
    hξY.comp_aemeasurable hY.aemeasurable
  rw [direction_map hX.aemeasurable hξX.aestronglyMeasurable,
    direction_map hY.aemeasurable hξY.aestronglyMeasurable, ← integral_sub hξX' hξY']
  simpa using norm_integral_le_of_norm_le_const (hν.mono fun x hx ↦ by
    simpa [dist_eq_norm] using hη _ (hXΩ x hx) _ (hYΩ x hx) (hXY x hx))

end ImageMeasure

/-- The update directions lie in a ball. -/
theorem exists_norm_le_of_mem_closedConvexHull (hΩ : IsCompact Ω) (hΦ : ContDiff ℝ 1 Φ)
    (hs : ContinuousOn s Ω) :
    ∃ B : ℝ≥0, ∀ h ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω), ‖h‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedConvexHull_steinFeature hΩ hΦ hs).isBounded.exists_norm_le
  exact ⟨B.toNNReal, fun h hh ↦ (hB h hh).trans (Real.le_coe_toNNReal B)⟩

/-- **Existence of the mean-field SVGD flow on a compact time interval.** Let `Ω` be compact, let
the score `s` be continuous on `Ω`, and let `Φ` be an admissible feature map. For every probability
measure `ν` concentrated on `Ω` and every `a ≤ b`, there is a continuous curve `m` of update
directions such that `m t = φ*_{(Xₜ)#ν}` for `t ∈ [a, b]`, where `Xₜ = trajectory Φ m a · t` is the
flow of the vector field of `m`. -/
theorem exists_meanField_Icc (hΦ : AdmissibleFeatureMap Φ Ω K C) (hΩ : IsCompact Ω)
    (hs : ContinuousOn s Ω) [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ m : ℝ → 𝓗[d, H₀], Continuous m ∧ (∀ t, m t ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω)) ∧
      ∀ t ∈ Icc a b, m t = direction Φ s (ν.map (trajectory Φ m a · t)) := by
  set 𝒦 := closedConvexHull ℝ (steinFeature Φ s '' Ω)
  obtain ⟨B, hB⟩ := exists_norm_le_of_mem_closedConvexHull hΩ hΦ.contDiff hs
  have h𝒦 : IsCompact 𝒦 := isCompact_closedConvexHull_steinFeature hΩ hΦ.contDiff hs
  classical
  have hΩne : Ω.Nonempty := hν.exists
  -- The set `S` of bounded continuous curves on `[a, b]` with values in `𝒦`.
  set S : Set (Icc a b →ᵇ 𝓗[d, H₀]) := {g | ∀ t, g t ∈ 𝒦}
  have hSc : IsClosed S := by
    have : S = ⋂ t, (fun g : Icc a b →ᵇ 𝓗[d, H₀] ↦ g t) ⁻¹' 𝒦 := by
      ext
      simp [S]
    rw [this]
    exact isClosed_iInter fun t ↦ isClosed_closedConvexHull.preimage (continuous_eval_const t)
  have hSconv : Convex ℝ S := fun g hg g' hg' c c' hc hc' hcc' t ↦ by
    simpa using convex_closedConvexHull (hg t) (hg' t) hc hc' hcc'
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hΩne
    exact ⟨BoundedContinuousFunction.const _ (steinFeature Φ s x),
      fun _ ↦ subset_closedConvexHull (mem_image_of_mem _ hx)⟩
  -- Curves of `S`, extended to `ℝ`, satisfy the assumptions on trajectories.
  have hext {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) :
      Continuous (IccExtend hab ⇑g) ∧ ∀ τ, ‖IccExtend hab (⇑g) τ‖ ≤ B :=
    ⟨g.continuous.Icc_extend', fun τ ↦ hB _ (hg _)⟩
  have htraj {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) {t : ℝ} (ht : a ≤ t) :
      Continuous (trajectory Φ (IccExtend hab ⇑g) a · t) ∧
        ∀ x ∈ Ω, trajectory Φ (IccExtend hab ⇑g) a x t ∈ Ω :=
    ⟨continuous_trajectory_apply (hext hg).1 (hext hg).2 hΦ.lipschitzWith hΦ.norm_le ht,
      fun _ hx ↦ trajectory_mem (hext hg).1 (hext hg).2 hΦ.lipschitzWith hΦ.norm_le
        hΩ.isClosed hΦ.eq_zero_of_mem_frontier hx t⟩
  -- The fixed-point map, on raw functions.
  let F (g : Icc a b →ᵇ 𝓗[d, H₀]) (t : Icc a b) : 𝓗[d, H₀] :=
    direction Φ s (ν.map (trajectory Φ (IccExtend hab ⇑g) a · t))
  have hFS {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) (t : Icc a b) : F g t ∈ 𝒦 := by
    exact direction_mem_closedConvexHull hΩ hΦ.contDiff hs
      (ae_mem_map hΩ hν (htraj hg t.property.1).1 (htraj hg t.property.1).2)
  -- Uniform continuity of `ξ` on `Ω`.
  have hξ := Metric.uniformContinuousOn_iff.1
    (uniformContinuousOn_steinFeature hΩ hΦ.contDiff hs)
  -- Equicontinuity of the images.
  have hequi : ∀ ε > 0, ∃ δ > 0, ∀ g ∈ S, ∀ t t' : Icc a b, dist t t' < δ →
      dist (F g t) (F g t') ≤ ε := by
    intro ε hε
    obtain ⟨η, hη, hηξ⟩ := hξ ε hε
    refine ⟨η / (B * C + 1), by positivity, fun g hg t t' htt' ↦ ?_⟩
    rw [dist_eq_norm]
    refine norm_direction_map_sub_direction_map_le hΩ hΦ.contDiff hs hν (htraj hg t.property.1).1
      (htraj hg t'.property.1).1 (htraj hg t.property.1).2 (htraj hg t'.property.1).2
      (fun x hx y hy hxy ↦ (hηξ x hx y hy hxy).le) fun x _ ↦ ?_
    calc dist (trajectory Φ (IccExtend hab ⇑g) a x t) (trajectory Φ (IccExtend hab ⇑g) a x t')
        ≤ B * C * dist (t : ℝ) t' :=
          dist_trajectory_le (hext hg).1 (hext hg).2 hΦ.lipschitzWith hΦ.norm_le a x t t'
      _ ≤ B * C * (η / (B * C + 1)) := by gcongr; exact htt'.le
      _ < η := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [mul_nonneg B.coe_nonneg C.coe_nonneg]
  have hFc {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) : Continuous (F g) :=
    Metric.continuous_iff.2 fun t ε hε ↦ by
      obtain ⟨δ, hδ, hδF⟩ := hequi (ε / 2) (half_pos hε)
      exact ⟨δ, hδ, fun t' ht' ↦ (hδF g hg t' t ht').trans_lt (half_lt_self hε)⟩
  -- The fixed-point map on bounded continuous curves.
  let G (g : Icc a b →ᵇ 𝓗[d, H₀]) : Icc a b →ᵇ 𝓗[d, H₀] :=
    if hg : g ∈ S then BoundedContinuousFunction.mkOfCompact ⟨F g, hFc hg⟩ else g
  have hG {g : Icc a b →ᵇ 𝓗[d, H₀]} (hg : g ∈ S) (t : Icc a b) : G g t = F g t := by
    simp [G, hg]
  have hGS : MapsTo G S S := fun g hg t ↦ by
    rw [hG hg]
    exact hFS hg t
  -- Continuity of the fixed-point map on `S`.
  have hGc : ContinuousOn G S := by
    refine Metric.continuousOn_iff.2 fun g hg ε hε ↦ ?_
    obtain ⟨η, hη, hηξ⟩ := hξ (ε / 2) (half_pos hε)
    have hgr : Tendsto (fun δ ↦ gronwallBound 0 (B * K) (C * δ) (b - a)) (𝓝 0) (𝓝 0) := by
      have := ((gronwallBound_continuous_ε 0 (B * K) (b - a)).comp
        (continuous_const_mul (C : ℝ))).tendsto 0
      simpa [gronwallBound_ε0, Function.comp_def] using this
    obtain ⟨δ, hδ, hδgr⟩ := Metric.tendsto_nhds_nhds.1 hgr η hη
    refine ⟨δ, hδ, fun g' hg' hgg' ↦ ?_⟩
    refine ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun t ↦ ?_).trans_lt
      (half_lt_self hε)
    rw [hG hg', hG hg, dist_eq_norm]
    refine norm_direction_map_sub_direction_map_le hΩ hΦ.contDiff hs hν (htraj hg' t.property.1).1
      (htraj hg t.property.1).1 (htraj hg' t.property.1).2 (htraj hg t.property.1).2
      (fun x hx y hy hxy ↦ (hηξ x hx y hy hxy).le) fun x _ ↦ ?_
    have hδ' : ∀ τ ∈ Icc a t, ‖IccExtend hab (⇑g') τ - IccExtend hab (⇑g) τ‖ ≤ dist g' g :=
      fun τ _ ↦ by
        rw [← dist_eq_norm]
        exact BoundedContinuousFunction.dist_coe_le_dist (f := g') (g := g) _
    calc dist (trajectory Φ (IccExtend hab ⇑g') a x t) (trajectory Φ (IccExtend hab ⇑g) a x t)
        ≤ gronwallBound 0 (B * K) (C * dist g' g) (t - a) :=
          dist_trajectory_trajectory_le_of_dist_le (hext hg').1 (hext hg').2 hΦ.lipschitzWith
            hΦ.norm_le (hext hg).1 (hext hg).2 t.property.1 hδ' x
      _ ≤ gronwallBound 0 (B * K) (C * dist g' g) (b - a) :=
          gronwallBound_mono le_rfl (by positivity) (by positivity) (by linarith [t.property.2])
      _ < η := (le_abs_self _).trans_lt (by
          simpa [Real.dist_eq] using
            hδgr (by simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hgg'))
  -- Relative compactness of the image, by the Arzelà–Ascoli theorem.
  have hGK : IsCompact (closure (G '' S)) := by
    refine BoundedContinuousFunction.arzela_ascoli 𝒦 h𝒦 _ ?_ ?_
    · rintro _ t ⟨g, hg, rfl⟩
      exact hGS hg t
    · refine (Metric.uniformEquicontinuous_iff.2 fun ε hε ↦ ?_).equicontinuous
      obtain ⟨δ, hδ, hδF⟩ := hequi (ε / 2) (half_pos hε)
      refine ⟨δ, hδ, fun t t' htt' ⟨_, g, hg, rfl⟩ ↦ ?_⟩
      simp only [hG hg]
      exact (hδF g hg t t' htt').trans_lt (half_lt_self hε)
  -- Schauder's fixed-point theorem.
  obtain ⟨g, hg, hgG⟩ :=
    TauCeti.schauderFixedPoint_closedConvex_continuousOn hSc hSconv hSne hGc hGS hGK
  refine ⟨IccExtend hab ⇑g, (hext hg).1, fun τ ↦ hg _, fun t ht ↦ ?_⟩
  rw [IccExtend_of_mem hab _ ht]
  exact (DFunLike.congr_fun hgG.eq _).symm.trans (hG hg ⟨t, ht⟩)

end SVGD
