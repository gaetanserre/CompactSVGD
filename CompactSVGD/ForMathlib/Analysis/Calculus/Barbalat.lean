/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Barbalat's lemma

Let `u ≥ 0` be uniformly continuous on `[0, ∞)`, with `∫₀ᵃ u ≤ M` for every `a ≥ 0`. Then
`u t → 0` as `t → ∞`. Without uniform continuity, `u` could be a sum of thinner and thinner spikes
of height `1`, with a finite integral.

The proof is by contradiction. If `η ≤ u tₙ` for a sequence `tₙ → ∞`, uniform continuity gives
`δ > 0` such that `η / 2 ≤ u` on every interval `[tₙ, tₙ + δ]`. These intervals contribute
`δ η / 2` each to the integral, which is thus unbounded.

## Main statements

* `tendsto_zero_of_uniformContinuousOn_of_integral_le`: **Barbalat's lemma**.

## References

* [H. K. Khalil, *Nonlinear Systems*][Khalil2002], Lemma 8.2
-/

@[expose] public section

open Filter Topology Set MeasureTheory

/-- **Barbalat's lemma.** Let `u ≥ 0` be uniformly continuous on `[0, ∞)`, with `∫₀ᵃ u ≤ M` for
every `a ≥ 0`. Then `u t → 0` as `t → ∞`. -/
theorem tendsto_zero_of_uniformContinuousOn_of_integral_le {u : ℝ → ℝ} {M : ℝ}
    (hu : UniformContinuousOn u (Ici 0)) (hu₀ : ∀ t ∈ Ici (0 : ℝ), 0 ≤ u t)
    (hM : ∀ a ∈ Ici (0 : ℝ), ∫ t in 0..a, u t ≤ M) : Tendsto u atTop (𝓝 0) := by
  -- Suppose that `u t` does not tend to `0`: `η ≤ u t` for arbitrarily large `t`.
  by_contra hlim
  obtain ⟨η, hη, hfreq⟩ : ∃ η > 0, ∀ T, ∃ t ≥ T, η ≤ u t := by
    rw [Metric.tendsto_atTop] at hlim
    push Not at hlim
    obtain ⟨η, hη, h⟩ := hlim
    refine ⟨η, hη, fun T ↦ ?_⟩
    obtain ⟨t, ht, hηt⟩ := h (max T 0)
    refine ⟨t, (le_max_left _ _).trans ht, ?_⟩
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hu₀ t ((le_max_right _ _).trans ht))] at hηt
  -- A sequence `tₙ ≥ 0` with `η ≤ u tₙ` and `tₙ + 1 ≤ tₙ₊₁`.
  choose f hf hfη using hfreq
  let t : ℕ → ℝ := fun n ↦ Nat.rec (f 0) (fun _ tn ↦ f (tn + 1)) n
  have htsucc (n : ℕ) : t n + 1 ≤ t (n + 1) := hf _
  have htη (n : ℕ) : η ≤ u (t n) := by
    cases n <;> exact hfη _
  have ht₀ (n : ℕ) : 0 ≤ t n := by
    induction n with
    | zero => exact hf 0
    | succ n ih => linarith [htsucc n]
  -- By uniform continuity, `η / 2 ≤ u` on `[tₙ, tₙ + δ]`, with `δ < 1`.
  obtain ⟨δ', hδ', hδu⟩ := Metric.uniformContinuousOn_iff_le.1 hu (η / 2) (half_pos hη)
  set δ := min δ' (1 / 2)
  have hδ : 0 < δ := lt_min hδ' one_half_pos
  have hδ₁ : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hlow (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc (t n) (t n + δ)) : η / 2 ≤ u τ := by
    have hdist : dist τ (t n) ≤ δ' := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hτ.1])]
      linarith [hτ.2, min_le_left δ' (1 / 2)]
    have := hδu τ ((ht₀ n).trans hτ.1) (t n) (ht₀ n) hdist
    rw [Real.dist_eq] at this
    linarith [abs_le.1 this, htη n]
  -- `u` is integrable on every interval of `[0, ∞)`.
  have hint {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable u volume a b := by
    refine ContinuousOn.intervalIntegrable (hu.continuousOn.mono fun τ hτ ↦ ?_)
    exact (le_min ha hb).trans hτ.1
  have hpos {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : 0 ≤ ∫ τ in a..b, u τ :=
    intervalIntegral.integral_nonneg hab fun τ hτ ↦ hu₀ τ (ha.trans hτ.1)
  -- Each interval `[tₙ, tₙ + δ]` contributes at least `δ η / 2` to the integral.
  have hpiece (n : ℕ) : δ * (η / 2) ≤ ∫ τ in t n..t n + δ, u τ := by
    have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hint (ht₀ n) (by linarith [ht₀ n])) fun τ hτ ↦ hlow n hτ
    simp only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
    linarith
  -- Thus, `(N + 1) δ η / 2 ≤ ∫₀^{t_N + δ} u`.
  have hsum (N : ℕ) : (N + 1) * (δ * (η / 2)) ≤ ∫ τ in 0..t N + δ, u τ := by
    induction N with
    | zero =>
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hint (a := 0) (b := t 0) le_rfl (ht₀ 0)) (hint (b := t 0 + δ) (ht₀ 0) (by linarith [ht₀ 0]))
      push_cast
      linarith [hpos le_rfl (ht₀ 0), hpiece 0]
    | succ N ih =>
      have hN : 0 ≤ t N + δ := by linarith [ht₀ N]
      have hN₁ := ht₀ (N + 1)
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hint (a := 0) (b := t N + δ) le_rfl hN) (hint (b := t (N + 1)) hN hN₁)
      have h' := intervalIntegral.integral_add_adjacent_intervals
        (hint (a := 0) (b := t (N + 1)) le_rfl hN₁) (hint (b := t (N + 1) + δ) hN₁ (by linarith))
      push_cast at ih ⊢
      linarith [hpos hN (by linarith [htsucc N] : t N + δ ≤ t (N + 1)), hpiece (N + 1)]
  -- This contradicts the bound `M`.
  obtain ⟨N, hN⟩ := exists_nat_gt (M / (δ * (η / 2)))
  have hM' := (hsum N).trans (hM _ (by linarith [ht₀ N] : (0 : ℝ) ≤ t N + δ))
  rw [div_lt_iff₀ (by positivity)] at hN
  linarith [mul_pos hδ (half_pos hη)]
