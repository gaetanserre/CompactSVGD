/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic

import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Order.ProjIcc

/-!
# Fixed points of causal maps on curves

Let `G` map curves `g : [a, b] → X` with values in a compact set `𝒦` to such curves. Assume that
`G` is continuous, that its images are equicontinuous, and that `G` is causal: `G g` at time `τ`
only depends on `g` before `τ`, and `G g` at time `a` does not depend on `g`. Then `G` has a fixed
point. This is Tonelli's proof of Peano's theorem, and it uses no fixed-point theorem.

For `h > 0`, the delayed equation `g t = G g (t - h)` is solved by finitely many iterations, by
causality. The delayed solutions are close to their images by equicontinuity, and these images
accumulate at a fixed point of `G` by the Arzelà–Ascoli theorem.

## Main statements

* `BoundedContinuousFunction.exists_isFixedPt_of_causal`: a causal map has a fixed point.
-/

@[expose] public section

open Set Filter Function

open scoped Topology BoundedContinuousFunction

namespace BoundedContinuousFunction

/-- **Fixed points of causal maps** (Tonelli). Let `G` map curves on `[a, b]` with values in the
compact set `𝒦` to such curves, continuously and with equicontinuous images. If `G g` at time `τ`
only depends on `g` before `τ`, and `G g` at time `a` does not depend on `g`, then `G` has a fixed
point. -/
theorem exists_isFixedPt_of_causal {X : Type*} [MetricSpace X] {a b : ℝ} (hab : a ≤ b)
    {𝒦 : Set X} (h𝒦 : IsCompact 𝒦) (h𝒦ne : 𝒦.Nonempty) {G : (Icc a b →ᵇ X) → Icc a b →ᵇ X}
    (hGS : MapsTo G {g | ∀ t, g t ∈ 𝒦} {g | ∀ t, g t ∈ 𝒦})
    (hGc : ContinuousOn G {g | ∀ t, g t ∈ 𝒦})
    (hequi : Equicontinuous fun g : {g : Icc a b →ᵇ X // ∀ t, g t ∈ 𝒦} ↦ ⇑(G g))
    (hcaus : ∀ g g' : Icc a b →ᵇ X, (∀ t, g t ∈ 𝒦) → (∀ t, g' t ∈ 𝒦) → ∀ τ,
      (∀ t ≤ τ, g t = g' t) → G g τ = G g' τ)
    (h₀ : ∀ g g' : Icc a b →ᵇ X, (∀ t, g t ∈ 𝒦) → (∀ t, g' t ∈ 𝒦) →
      G g ⟨a, left_mem_Icc.2 hab⟩ = G g' ⟨a, left_mem_Icc.2 hab⟩) :
    ∃ g : Icc a b →ᵇ X, (∀ t, g t ∈ 𝒦) ∧ IsFixedPt G g := by
  set S : Set (Icc a b →ᵇ X) := {g | ∀ t, g t ∈ 𝒦}
  -- On the compact interval `[a, b]`, the images are uniformly equicontinuous.
  have hequi' : ∀ ε > 0, ∃ δ > 0, ∀ g ∈ S, ∀ t t', dist t t' < δ → dist (G g t) (G g t') < ε :=
    fun ε hε ↦ by
      obtain ⟨δ, hδ, h⟩ := Metric.uniformEquicontinuous_iff.1
        (CompactSpace.uniformEquicontinuous_of_equicontinuous hequi) ε hε
      exact ⟨δ, hδ, fun g hg t t' htt' ↦ h t t' htt' ⟨g, hg⟩⟩
  have hSc : IsClosed S := by
    have : S = ⋂ t, (fun g : Icc a b →ᵇ X ↦ g t) ⁻¹' 𝒦 := by
      ext
      simp [S]
    rw [this]
    exact isClosed_iInter fun t ↦ h𝒦.isClosed.preimage (continuous_eval_const t)
  -- Relative compactness of the image, by the Arzelà–Ascoli theorem.
  have hGK : IsCompact (closure (G '' S)) := by
    refine arzela_ascoli 𝒦 h𝒦 _ ?_ ?_
    · rintro _ t ⟨g, hg, rfl⟩
      exact hGS hg t
    · refine (Metric.uniformEquicontinuous_iff.2 fun ε hε ↦ ?_).equicontinuous
      obtain ⟨δ, hδ, hδG⟩ := hequi' ε hε
      exact ⟨δ, hδ, fun t t' htt' ⟨_, g, hg, rfl⟩ ↦ hδG g hg t t' htt'⟩
  -- The delayed map: `D h g` follows `G g` with delay `h`.
  let delay (h : ℝ) : C(Icc a b, Icc a b) :=
    ⟨fun t ↦ projIcc a b hab (t - h), continuous_projIcc.comp
      (continuous_subtypeVal.sub continuous_const)⟩
  let D (h : ℝ) (g : Icc a b →ᵇ X) : Icc a b →ᵇ X := (G g).compContinuous (delay h)
  have hDS (h : ℝ) : MapsTo (D h) S S := fun g hg t ↦ hGS hg (delay h t)
  -- The iterates of `D h` agree on `[a, a + k h)`, whatever the initial curve.
  have hiter {h : ℝ} (k : ℕ) {g g' : Icc a b →ᵇ X} (hg : g ∈ S) (hg' : g' ∈ S) (t : Icc a b)
      (ht : (t : ℝ) < a + k * h) : (D h)^[k] g t = (D h)^[k] g' t := by
    induction k generalizing t with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero] at ht
      exact absurd t.property.1 (not_le.2 ht)
    | succ k ih =>
      rw [iterate_succ_apply', iterate_succ_apply']
      change G _ (projIcc a b hab (t - h)) = G _ (projIcc a b hab (t - h))
      rcases le_or_gt ((t : ℝ) - h) a with hta | hta
      · rw [projIcc_of_le_left hab hta]
        exact h₀ _ _ ((hDS h).iterate k hg) ((hDS h).iterate k hg')
      · refine hcaus _ _ ((hDS h).iterate k hg) ((hDS h).iterate k hg') _ fun t' ht' ↦ ih t' ?_
        have : (t' : ℝ) ≤ t - h := (Subtype.coe_le_coe.2 ht').trans (by
          rw [coe_projIcc]
          exact max_le hta.le (min_le_right _ _))
        push_cast at ht
        linarith
  -- For `h > 0`, the delayed equation `g = D h g` has a solution in `S`.
  have hfix {h : ℝ} (hh : 0 < h) : ∃ g ∈ S, D h g = g := by
    obtain ⟨x, hx⟩ := h𝒦ne
    have hg₀ : const (Icc a b) x ∈ S := fun _ ↦ hx
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / h)
    refine ⟨(D h)^[N] (const _ x), (hDS h).iterate N hg₀, ext fun t ↦ ?_⟩
    rw [← iterate_succ_apply' (D h), iterate_succ_apply]
    exact hiter (h := h) N (hDS h hg₀) hg₀ t (by
      have := (div_lt_iff₀ hh).1 hN
      linarith [t.property.2])
  choose u hu hDu using fun n : ℕ ↦ hfix (h := 1 / (n + 1)) (by positivity)
  -- By equicontinuity, `G (u n)` is close to `u n`, which follows `G (u n)` with a small delay.
  have hGu : Tendsto (fun n ↦ dist (G (u n)) (u n)) atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    obtain ⟨δ, hδ, hδG⟩ := hequi' (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_zero_right, Real.norm_of_nonneg dist_nonneg]
    refine ((dist_le (half_pos hε).le).2 fun t ↦ ?_).trans_lt (half_lt_self hε)
    have hdist : dist t (projIcc a b hab (t - 1 / (n + 1))) < δ := by
      calc dist t (projIcc a b hab (t - 1 / (n + 1)))
          = dist (projIcc a b hab t) (projIcc a b hab (t - 1 / (n + 1))) := by
            rw [projIcc_val]
        _ ≤ dist (t : ℝ) (t - 1 / (n + 1)) := by
            simpa using (LipschitzWith.projIcc hab).dist_le_mul t (t - 1 / (n + 1))
        _ = 1 / (n + 1) := by rw [Real.dist_eq, sub_sub_cancel, abs_of_pos (by positivity)]
        _ ≤ 1 / (N + 1) := by gcongr
        _ < δ := hN
    have hut : u n t = G (u n) (projIcc a b hab (t - 1 / (n + 1))) :=
      (DFunLike.congr_fun (hDu n) t).symm
    rw [hut]
    exact (hδG (u n) (hu n) t _ hdist).le
  -- A cluster point of `G (u n)` is a fixed point of `G`.
  obtain ⟨g, hgK, φ, hφ, hlim⟩ :=
    hGK.tendsto_subseq fun n ↦ subset_closure (mem_image_of_mem G (hu n))
  have hg : g ∈ S := hSc.closure_subset_iff.2 (image_subset_iff.2 hGS) hgK
  have hlim' : Tendsto (u ∘ φ) atTop (𝓝 g) := hlim.congr_dist (hGu.comp hφ.tendsto_atTop)
  exact ⟨g, hg, tendsto_nhds_unique
    ((hGc g hg).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim', .of_forall fun n ↦ hu (φ n)⟩))
    hlim⟩

end BoundedContinuousFunction
