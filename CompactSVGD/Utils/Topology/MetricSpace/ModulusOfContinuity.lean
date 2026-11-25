/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions

/-!
# The modulus of continuity of a function on a set

This file is the API of `modulusOfContinuityOn f s`, defined in `CompactSVGD/Definitions.lean`:
`ω(r)` is the supremum of `dist (f x) (f y)` over the points `x, y ∈ s` with `dist x y ≤ r`. When
`f` is uniformly continuous on `s`, it is a continuity modulus of `f` on `s`, in the sense of
`Metric.uniformEquicontinuous_of_continuity_modulus`: `dist (f x) (f y) ≤ ω(dist x y)` and
`ω(r) → 0` as `r → 0`.

## Main statements

* `dist_le_modulusOfContinuityOn`: `dist (f x) (f y) ≤ ω(dist x y)` on `s`, when `f` is bounded on
  `s`.
* `monotone_modulusOfContinuityOn`: `ω` is nondecreasing, when `f` is bounded on `s`.
* `UniformContinuousOn.tendsto_modulusOfContinuityOn`: `ω(r) → 0` as `r → 0`, when `f` is
  uniformly continuous on `s`.
* `Metric.uniformContinuous_of_continuity_modulus`: a function with a continuity modulus is
  uniformly continuous.
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
theorem UniformContinuousOn.tendsto_modulusOfContinuityOn (hf : UniformContinuousOn f s) :
    Tendsto (modulusOfContinuityOn f s) (𝓝 0) (𝓝 0) := by
  refine Metric.tendsto_nhds_nhds.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1 hf (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun r hr ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulusOfContinuityOn_nonneg f s r)]
  refine (modulusOfContinuityOn_le (half_pos hε).le fun x hx y hy hxy ↦ (h x hx y hy ?_).le)
    |>.trans_lt (half_lt_self hε)
  exact hxy.trans_lt ((le_abs_self r).trans_lt (by rwa [Real.dist_eq, sub_zero] at hr))

/-- For a uniformly continuous function, `ω(c r) → 0` as `r → 0`. -/
theorem UniformContinuousOn.tendsto_modulusOfContinuityOn_comp_mul_left
    (hf : UniformContinuousOn f s) (c : ℝ) :
    Tendsto (fun r ↦ modulusOfContinuityOn f s (c * r)) (𝓝 0) (𝓝 0) :=
  hf.tendsto_modulusOfContinuityOn.comp ((continuous_const_mul c).tendsto' 0 0 (mul_zero c))

/-- A function with a continuity modulus `b`, i.e. `dist (f x) (f y) ≤ b (dist x y)` with
`b(r) → 0` as `r → 0`, is uniformly continuous. This is the case of a single function of
`Metric.uniformEquicontinuous_of_continuity_modulus`. -/
theorem Metric.uniformContinuous_of_continuity_modulus {γ : Type*} [PseudoMetricSpace γ]
    (b : ℝ → ℝ) (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (g : γ → β)
    (H : ∀ x y, dist (g x) (g y) ≤ b (dist x y)) : UniformContinuous g :=
  (uniformEquicontinuous_of_continuity_modulus b b_lim (fun _ : Unit ↦ g)
    fun x y _ ↦ H x y).uniformContinuous ()
