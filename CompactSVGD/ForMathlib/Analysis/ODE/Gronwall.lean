/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# Complements on Grönwall's inequality

With zero initial value, the Grönwall bound `gronwallBound 0 K ε x` is linear in the error rate `ε`.
For a curve on the whole line with `‖γ'‖ ≤ K ‖γ‖ + ε`, Grönwall's inequality holds in both time
directions, by time reversal.

## Main statements

* `norm_le_gronwallBound_of_norm_deriv_le`: the two-sided Grönwall inequality.
-/

@[expose] public section

open Set

theorem gronwallBound_δ0 (K ε x : ℝ) :
    gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x := by
  unfold gronwallBound
  split_ifs <;> ring

/-- **Two-sided Grönwall inequality.** If `‖γ' s‖ ≤ K ‖γ s‖ + ε` for every `s` between `t₀` and
`t`, then `‖γ t‖ ≤ gronwallBound ‖γ t₀‖ K ε |t - t₀|`. -/
theorem norm_le_gronwallBound_of_norm_deriv_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {γ γ' : ℝ → E} {K ε t₀ t : ℝ} (hγ : ∀ s ∈ uIcc t₀ t, HasDerivAt γ (γ' s) s)
    (hb : ∀ s ∈ uIcc t₀ t, ‖γ' s‖ ≤ K * ‖γ s‖ + ε) :
    ‖γ t‖ ≤ gronwallBound ‖γ t₀‖ K ε |t - t₀| := by
  wlog h : t₀ ≤ t generalizing γ γ' t₀ t
  · -- Backwards in time, apply the forward case to `s ↦ γ (-s)`.
    have hmem {s : ℝ} (hs : s ∈ uIcc (-t₀) (-t)) : -s ∈ uIcc t₀ t := by
      rw [← image_neg_uIcc] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      rwa [neg_neg]
    have := this (γ := fun s ↦ γ (-s)) (γ' := fun s ↦ -γ' (-s))
      (fun s hs ↦ ((hγ (-s) (hmem hs)).scomp s (hasDerivAt_neg s)).congr_deriv (by simp))
      (fun s hs ↦ by simpa using hb (-s) (hmem hs)) (by linarith)
    rwa [neg_neg, neg_neg, neg_sub_neg, abs_sub_comm] at this
  rw [uIcc_of_le h] at hγ hb
  rw [abs_of_nonneg (sub_nonneg.2 h)]
  exact norm_le_gronwallBound_of_norm_deriv_right_le
    (fun s hs ↦ (hγ s hs).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hγ s (Ico_subset_Icc_self hs)).hasDerivWithinAt) le_rfl
    (fun s hs ↦ hb s (Ico_subset_Icc_self hs)) t ⟨h, le_rfl⟩
