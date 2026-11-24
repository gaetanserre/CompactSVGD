/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# The modulus of continuity of a function on a set

This file is the API of `modulusOfContinuityOn f s`, defined in `CompactSVGD/Definitions.lean`:
`ω(r)` is the supremum of `dist (f x) (f y)` over the points `x, y ∈ s` with `dist x y ≤ r`.

## Main statements

* `dist_le_modulusOfContinuityOn`: `dist (f x) (f y) ≤ ω(dist x y)` on `s`, when `f` is bounded on
  `s`.
* `monotone_modulusOfContinuityOn`: `ω` is nondecreasing, when `f` is bounded on `s`.
* `tendsto_modulusOfContinuityOn`: `ω(r) → 0` as `r → 0`, when `f` is uniformly continuous on `s`.
* `exists_pos_forall_modulusOfContinuityOn_mul_lt`: `ω(c r) < ε` for every small enough `r ≥ 0`.
-/

@[expose] public section

open Set Filter Topology

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} {s : Set α}
  {r : ℝ}

theorem modulusOfContinuityOn_nonneg (f : α → β) (s : Set α) (r : ℝ) :
    0 ≤ modulusOfContinuityOn f s r :=
  Real.sSup_nonneg fun _ ⟨_, _, _, _, _, he⟩ ↦ he ▸ dist_nonneg

/-- The modulus of continuity is at most `a` as soon as every distance that it bounds is. -/
theorem modulusOfContinuityOn_le {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ r → dist (f x) (f y) ≤ a) :
    modulusOfContinuityOn f s r ≤ a :=
  Real.sSup_le (fun _ ⟨x, hx, y, hy, hxy, he⟩ ↦ he ▸ h x hx y hy hxy) ha

theorem dist_le_modulusOfContinuityOn (hf : Bornology.IsBounded (f '' s)) {x y : α} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : dist x y ≤ r) : dist (f x) (f y) ≤ modulusOfContinuityOn f s r := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hf
  exact le_csSup ⟨C, fun _ ⟨x, hx, y, hy, _, he⟩ ↦
    he ▸ hC (mem_image_of_mem f hx) (mem_image_of_mem f hy)⟩ ⟨x, hx, y, hy, hxy, rfl⟩

theorem monotone_modulusOfContinuityOn (hf : Bornology.IsBounded (f '' s)) :
    Monotone (modulusOfContinuityOn f s) := fun _ _ hr ↦
  modulusOfContinuityOn_le (modulusOfContinuityOn_nonneg f s _) fun _ hx _ hy hxy ↦
    dist_le_modulusOfContinuityOn hf hx hy (hxy.trans hr)

/-- The modulus of continuity of a uniformly continuous function tends to `0` at `0`. -/
theorem tendsto_modulusOfContinuityOn (hf : UniformContinuousOn f s) :
    Tendsto (modulusOfContinuityOn f s) (𝓝 0) (𝓝 0) := by
  refine Metric.tendsto_nhds_nhds.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1 hf (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun r hr ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulusOfContinuityOn_nonneg f s r)]
  refine (modulusOfContinuityOn_le (half_pos hε).le fun x hx y hy hxy ↦ (h x hx y hy ?_).le)
    |>.trans_lt (half_lt_self hε)
  exact hxy.trans_lt ((le_abs_self r).trans_lt (by rwa [Real.dist_eq, sub_zero] at hr))

/-- For a uniformly continuous function, `ω(c r) < ε` for every small enough `r ≥ 0`. -/
theorem exists_pos_forall_modulusOfContinuityOn_mul_lt (hf : UniformContinuousOn f s) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → modulusOfContinuityOn f s (c * r) < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.tendsto_nhds_nhds.1 ((tendsto_modulusOfContinuityOn hf).comp
    ((continuous_const_mul c).tendsto' 0 0 (mul_zero c))) ε hε
  refine ⟨δ, hδ, fun r hr hrδ ↦ ?_⟩
  have := h (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg hr])
  rw [Function.comp_apply, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans_lt this
