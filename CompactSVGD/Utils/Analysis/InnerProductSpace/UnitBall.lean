/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Maximizing a linear form on the unit ball of a real inner product space

Let `v` be a vector of a real inner product space. On the closed unit ball, the linear form
`h ↦ ⟪h, v⟫` is maximized at `v / ‖v‖`, with maximum `‖v‖`, and this maximizer is unique when
`v ≠ 0`. Consequently, the supremum of `⟪h, v⟫²` over the unit ball is `‖v‖²`.

## Main statements

* `isMaxOn_inner_closedBall`: `v / ‖v‖` maximizes `⟪·, v⟫` on the unit ball.
* `eq_inv_norm_smul_of_inner_eq_norm`: it is the unique maximizer when `v ≠ 0`.
* `iSup_closedBall_inner_sq`: `⨆_{‖h‖ ≤ 1} ⟪h, v⟫² = ‖v‖²`.
-/

@[expose] public section

open Metric Set

open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {h v : F}

theorem inner_le_norm_of_mem_closedBall (hh : h ∈ closedBall (0 : F) 1) : ⟪h, v⟫ ≤ ‖v‖ :=
  (real_inner_le_norm h v).trans
    (mul_le_of_le_one_left (norm_nonneg _) (by simpa using hh))

theorem abs_inner_le_norm_of_mem_closedBall (hh : h ∈ closedBall (0 : F) 1) : |⟪h, v⟫| ≤ ‖v‖ :=
  (abs_real_inner_le_norm h v).trans
    (mul_le_of_le_one_left (norm_nonneg _) (by simpa using hh))

@[simp]
theorem inner_inv_norm_smul_self (v : F) : ⟪‖v‖⁻¹ • v, v⟫ = ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hv), one_mul]

/-- On the closed unit ball, `h ↦ ⟪h, v⟫` is maximized at `v / ‖v‖`. -/
theorem isMaxOn_inner_closedBall (v : F) :
    IsMaxOn (fun h ↦ ⟪h, v⟫) (closedBall (0 : F) 1) (‖v‖⁻¹ • v) := fun _ hh ↦ by
  simpa using inner_le_norm_of_mem_closedBall hh

/-- **Uniqueness of the maximizer.** If `v ≠ 0`, `‖h‖ ≤ 1` and `⟪h, v⟫ = ‖v‖`, then
`h = v / ‖v‖`. -/
theorem eq_inv_norm_smul_of_inner_eq_norm (hv : v ≠ 0) (hh : h ∈ closedBall (0 : F) 1)
    (heq : ⟪h, v⟫ = ‖v‖) : h = ‖v‖⁻¹ • v := by
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  refine eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) ?_ ?_
  · simpa [norm_smul, hv'] using hh
  · simp [real_inner_smul_right, heq, norm_smul, hv']

/-- The supremum of `⟪h, v⟫²` over the closed unit ball is `‖v‖²`. -/
theorem iSup_closedBall_inner_sq (v : F) :
    ⨆ h : closedBall (0 : F) 1, ⟪(h : F), v⟫ ^ 2 = ‖v‖ ^ 2 := by
  have hle (h : closedBall (0 : F) 1) : ⟪(h : F), v⟫ ^ 2 ≤ ‖v‖ ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le (abs_inner_le_norm_of_mem_closedBall h.property))
      (le_of_abs_le (abs_inner_le_norm_of_mem_closedBall h.property))
  have : Nonempty (closedBall (0 : F) 1) := ⟨⟨0, by simp⟩⟩
  refine le_antisymm (ciSup_le hle) ?_
  refine le_ciSup_of_le ⟨‖v‖ ^ 2, forall_mem_range.2 hle⟩
    ⟨‖v‖⁻¹ • v, inv_norm_smul_mem_unitClosedBall v⟩ ?_
  simp
