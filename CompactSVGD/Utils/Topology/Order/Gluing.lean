/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Gluing continuous functions along the intervals `[n, n + 1]`

A function `f : ℝ → β` that agrees with a continuous function `g 0` on `(-∞, 1]` and with a
continuous function `g n` on `[n, n + 1]` for every `n : ℕ` is continuous
(`continuous_of_eqOn_Icc_nat`).
-/

@[expose] public section

open Set Filter

open scoped Topology

/-- A function that agrees with a continuous function `g 0` on `(-∞, 1]` and with a continuous
function `g n` on `[n, n + 1]` for every `n` is continuous. -/
theorem continuous_of_eqOn_Icc_nat {β : Type*} [TopologicalSpace β] {f : ℝ → β}
    {g : ℕ → ℝ → β} (hg : ∀ n, Continuous (g n)) (h₀ : EqOn f (g 0) (Iic 1))
    (h : ∀ n : ℕ, EqOn f (g n) (Icc n (n + 1))) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  rcases lt_or_ge t 1 with ht | ht
  · refine (hg 0).continuousAt.congr ?_
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact (h₀ (le_of_lt hu)).symm
  set n := ⌊t⌋₊ with hn
  have hn₁ : 1 ≤ n := Nat.le_floor (by simpa using ht)
  have hnt : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htn : t < n + 1 := Nat.lt_floor_add_one t
  rcases hnt.lt_or_eq with hlt | heq
  · refine (hg n).continuousAt.congr ?_
    filter_upwards [Ioo_mem_nhds hlt htn] with u hu
    exact (h n (Ioo_subset_Icc_self hu)).symm
  -- At the integer `t = n ≥ 1`, glue `g (n - 1)` on the left and `g n` on the right.
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub hn₁]
    ring
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · refine (hg (n - 1)).continuousWithinAt.congr_of_eventuallyEq ?_
      (h (n - 1) ⟨by rw [← heq, ← hcast]; linarith, by rw [hcast, heq]⟩)
    filter_upwards [Icc_mem_nhdsLE (show ((n - 1 : ℕ) : ℝ) < t by rw [← heq, ← hcast]; linarith)]
      with u hu
    exact h (n - 1) ⟨hu.1, hu.2.trans (by rw [hcast, heq])⟩
  · refine (hg n).continuousWithinAt.congr_of_eventuallyEq ?_ (h n ⟨hnt, htn.le⟩)
    filter_upwards [Icc_mem_nhdsGE htn] with u hu
    exact h n ⟨hnt.trans hu.1, hu.2⟩
