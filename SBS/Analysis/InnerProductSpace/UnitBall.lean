/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Maximizing a linear form on the unit ball of a real inner product space

Let `v` be a vector of a real inner product space. On the closed unit ball, the linear form
`h ↦ ⟪h, v⟫` is maximized at `v / ‖v‖`, with maximum `‖v‖` (`isMaxOn_inner_closedBall`). When
`v ≠ 0`, this maximizer is unique (`eq_of_inner_eq_norm`), by the case of equality in the
Cauchy–Schwarz inequality. Consequently, the supremum of `⟪h, v⟫²` over the unit ball is `‖v‖²`
(`iSup_closedBall_inner_sq`).

## Main statements

* `inner_le_norm_of_mem_closedBall`: `⟪h, v⟫ ≤ ‖v‖` for `‖h‖ ≤ 1`.
* `inner_inv_norm_smul_self`: `⟪v / ‖v‖, v⟫ = ‖v‖`.
* `isMaxOn_inner_closedBall`: `v / ‖v‖` maximizes `⟪·, v⟫` on the unit ball.
* `eq_of_inner_eq_norm`: it is the unique maximizer when `v ≠ 0`.
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

theorem inv_norm_smul_mem_closedBall (v : F) : ‖v‖⁻¹ • v ∈ closedBall (0 : F) 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]

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
theorem eq_of_inner_eq_norm (hv : v ≠ 0) (hh : h ∈ closedBall (0 : F) 1) (heq : ⟪h, v⟫ = ‖v‖) :
    h = ‖v‖⁻¹ • v := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hh' : ‖h‖ ≤ 1 := by simpa using hh
  -- Cauchy–Schwarz is an equality, and `‖h‖ = 1`.
  have h1 : ‖h‖ = 1 := le_antisymm hh' <| (le_mul_iff_one_le_left hv').1 <|
    heq ▸ real_inner_le_norm h v
  have := inner_eq_norm_mul_iff_real.1 (by rw [heq, h1, one_mul])
  rw [h1, one_smul] at this
  exact (eq_inv_smul_iff₀ hv'.ne').2 this

/-- The supremum of `⟪h, v⟫²` over the closed unit ball is `‖v‖²`. -/
theorem iSup_closedBall_inner_sq (v : F) :
    ⨆ h : closedBall (0 : F) 1, ⟪(h : F), v⟫ ^ 2 = ‖v‖ ^ 2 := by
  have hle (h : closedBall (0 : F) 1) : ⟪(h : F), v⟫ ^ 2 ≤ ‖v‖ ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le (abs_inner_le_norm_of_mem_closedBall h.property))
      (le_of_abs_le (abs_inner_le_norm_of_mem_closedBall h.property))
  have : Nonempty (closedBall (0 : F) 1) := ⟨⟨0, by simp⟩⟩
  refine le_antisymm (ciSup_le hle) ?_
  refine le_ciSup_of_le ⟨‖v‖ ^ 2, forall_mem_range.2 hle⟩
    ⟨‖v‖⁻¹ • v, inv_norm_smul_mem_closedBall v⟩ ?_
  simp
