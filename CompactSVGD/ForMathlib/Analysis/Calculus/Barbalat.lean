/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Barbalat's lemma

If `f : ℝ → E` has a limit at `+∞` and its derivative `f'` on `[a, ∞)` is uniformly continuous
there, then `f' t → 0` as `t → ∞`. In particular, if `f : ℝ → ℝ` is bounded below on `[a, ∞)` with
derivative `-g ≤ 0` there and `g` is uniformly continuous, then `g t → 0`.

## Main statements

* `tendsto_zero_of_hasDerivWithinAt_of_tendsto`: **Barbalat's lemma**.
* `tendsto_zero_of_hasDerivWithinAt_neg_of_uniformContinuousOn`: the case of a function bounded
  below with nonpositive derivative.

## References

* [H. K. Khalil, *Nonlinear Systems*][Khalil2002], Lemma 8.2
-/

@[expose] public section

open Filter Topology Set

/-- **Barbalat's lemma.** If `f` has a limit at `+∞` and its derivative `f'` on `[a, ∞)` is
uniformly continuous there, then `f' t → 0` as `t → ∞`. -/
theorem tendsto_zero_of_hasDerivWithinAt_of_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f f' : ℝ → E} {a : ℝ} {l : E}
    (hf : ∀ t ∈ Ici a, HasDerivWithinAt f (f' t) (Ici a) t) (hfl : Tendsto f atTop (𝓝 l))
    (hf' : UniformContinuousOn f' (Ici a)) : Tendsto f' atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 hf' (ε / 2) (half_pos hε)
  -- The increase of `f` on windows of length `δ / 2` tends to `0`.
  have hdiff : Tendsto (fun t ↦ f (t + δ / 2) - f t) atTop (𝓝 0) := by
    simpa using (hfl.comp (tendsto_atTop_add_const_right _ (δ / 2) tendsto_id)).sub hfl
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdiff (ε * (δ / 2) / 2) (by positivity)
  refine ⟨max N a, fun t ht ↦ ?_⟩
  have hta : a ≤ t := (le_max_right N a).trans ht
  -- On `[t, t + δ / 2]`, `x ↦ f x - (x - t) • f' t` has derivative `f' x - f' t`, of norm at most
  -- `ε / 2` by uniform continuity, so it varies by at most `ε / 2 * (δ / 2)`.
  have hsub : Icc t (t + δ / 2) ⊆ Ici a := Icc_subset_Ici_self.trans (Ici_subset_Ici.2 hta)
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun x ↦ f x - (x - t) • f' t)
    (f' := fun x ↦ f' x - f' t) (C := ε / 2)
    (fun x hx ↦ by
      simpa using ((hf x (hsub hx)).mono hsub).fun_sub
        (((hasDerivWithinAt_id x _).sub_const t).smul_const (f' t)))
    (fun x hx ↦ by
      rw [← dist_eq_norm]
      refine (hδf x (hsub (Ico_subset_Icc_self hx)) t hta ?_).le
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2])
    (t + δ / 2) (right_mem_Icc.2 (by linarith))
  have h₂ := hN t ((le_max_left N a).trans ht)
  rw [dist_zero_right] at h₂ ⊢
  simp only [add_sub_cancel_left, sub_self, zero_smul, sub_zero] at key
  -- Hence `δ / 2 * ‖f' t‖` is at most the increase of `f` plus `ε / 2 * (δ / 2)`.
  have h₃ : δ / 2 * ‖f' t‖ ≤ ‖f (t + δ / 2) - f t‖ + ε / 2 * (δ / 2) := by
    rw [← norm_smul_of_nonneg (by positivity)]
    calc ‖(δ / 2) • f' t‖ =
        ‖(f (t + δ / 2) - f t) - (f (t + δ / 2) - f t - (δ / 2) • f' t)‖ := by
          congr 1
          abel
      _ ≤ _ := (norm_sub_le _ _).trans (by gcongr; simpa [sub_sub, add_comm] using key)
  nlinarith

/-- **Barbalat's lemma** for a function bounded below with nonpositive derivative. If `f` is
bounded below on `[a, ∞)` and has derivative `-g` there, with `g ≥ 0` uniformly continuous on
`[a, ∞)`, then `g t → 0` as `t → ∞`. -/
theorem tendsto_zero_of_hasDerivWithinAt_neg_of_uniformContinuousOn {f g : ℝ → ℝ} {a c : ℝ}
    (hf : ∀ t ∈ Ici a, HasDerivWithinAt f (-g t) (Ici a) t) (hfc : ∀ t ∈ Ici a, c ≤ f t)
    (hg₀ : ∀ t ∈ Ici a, 0 ≤ g t) (hgu : UniformContinuousOn g (Ici a)) :
    Tendsto g atTop (𝓝 0) := by
  have hanti : AntitoneOn f (Ici a) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
    (fun t ht ↦ (hf t ht).continuousWithinAt)
    (fun t ht ↦ (hf t (interior_subset ht)).mono interior_subset)
    (fun t ht ↦ neg_nonpos.2 (hg₀ t (interior_subset ht)))
  -- `t ↦ f (max t a)` is antitone and bounded below, hence converges.
  have hF : Antitone fun t ↦ f (max t a) := fun x y hxy ↦
    hanti (le_max_right x a) (le_max_right y a) (max_le_max_right a hxy)
  have hlim := tendsto_atTop_ciInf hF ⟨c, by rintro _ ⟨t, rfl⟩; exact hfc _ (le_max_right t a)⟩
  have hfl : Tendsto f atTop (𝓝 (⨅ t, f (max t a))) :=
    hlim.congr' (eventually_atTop.2 ⟨a, fun t ht ↦ by rw [max_eq_left ht]⟩)
  simpa using (tendsto_zero_of_hasDerivWithinAt_of_tendsto (f' := fun t ↦ -g t)
    hf hfl (uniformContinuous_neg.comp_uniformContinuousOn hgu)).neg
