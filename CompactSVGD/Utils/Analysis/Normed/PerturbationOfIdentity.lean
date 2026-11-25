/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation
import TauCeti.Topology.Frontier

/-!
# Lipschitz perturbations of the identity

Let `u : E → E` be `K`-Lipschitz with `K < 1` on a real Banach space. Then `x ↦ x + u x` is a
homeomorphism, `LipschitzWith.idAddHomeomorph` of Tau Ceti. If `u` vanishes on the frontier of a
set `s`, then
`x ↦ x + u x` maps `s` into `s`, and onto `s`. Indeed, a point of `s` sent outside `s` would cross
the frontier of `s` along the segment `τ ↦ x + τ • u x`, at a point fixed by `y ↦ y + τ • u y`,
which contradicts injectivity.

## Main statements

* `LipschitzWith.add_mem_of_forall_frontier_eq_zero`: `x + u x ∈ s` for every `x ∈ s`.
* `LipschitzWith.image_add_eq_of_forall_frontier_eq_zero`: `x ↦ x + u x` maps `s` onto `s`.
* `LipschitzWith.exists_homeomorph_id_add_smul`,
  `LipschitzWith.image_add_smul_eq_of_forall_frontier_eq_zero`: `x ↦ x + ε • v x` is a
  homeomorphism, which maps `s` onto `s`.
-/

@[expose] public section

open Set

open scoped NNReal

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : E → E} {K : ℝ≥0} {s : Set E}
  {x : E} {ε : ℝ}

/-- **Invariance of a set under a perturbation of the identity.** Let `u` be `K`-Lipschitz with
`K < 1` and vanish on the frontier of `s`. Then `x + u x ∈ s` for every `x ∈ s`. -/
theorem add_mem_of_forall_frontier_eq_zero (hu : LipschitzWith K u) (hK : K < 1)
    (h₀ : ∀ y ∈ frontier s, u y = 0) (hx : x ∈ s) : x + u x ∈ s := by
  by_contra hout
  -- The segment `τ ↦ x + τ • u x`, `τ ∈ [0, 1]`, joins a point of `s` to a point outside `s`, so
  -- it meets the frontier of `s`.
  let γ : ℝ → E := fun τ ↦ x + τ • u x
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  obtain ⟨_, ⟨τ, hτ, rfl⟩, hfr⟩ :=
    (isPreconnected_uIcc.image γ hγ.continuousOn).inter_frontier_nonempty
      ⟨γ 0, ⟨0, left_mem_uIcc, rfl⟩, by simpa [γ] using hx⟩
      ⟨γ 1, ⟨1, right_mem_uIcc, rfl⟩, by simpa [γ] using hout⟩
  -- The point `γ τ` is fixed by `y ↦ y + τ • u y`, as is its preimage `x`, so `x = γ τ`.
  rw [uIcc_of_le zero_le_one] at hτ
  have hτK : ‖τ‖₊ * K < 1 := (mul_le_of_le_one_left bot_le (by
    rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_of_nonneg hτ.1]
    exact hτ.2)).trans_lt hK
  have hinj := (((lipschitzWith_smul τ).comp hu).antilipschitzWith_id_add hτK).injective
  have hxγ : x = γ τ := hinj (by simp only [γ, Function.comp_apply, h₀ _ hfr, smul_zero, add_zero])
  have hux : u x = 0 := hxγ ▸ h₀ _ hfr
  exact hout (by simpa [hux] using hx)

/-- **A perturbation of the identity maps `s` onto `s`.** Let `u` be `K`-Lipschitz with `K < 1`
and vanish on the frontier of `s`. Then `x ↦ x + u x` maps `s` onto `s`. -/
theorem image_add_eq_of_forall_frontier_eq_zero [CompleteSpace E]
    (hu : LipschitzWith K u) (hK : K < 1) (h₀ : ∀ y ∈ frontier s, u y = 0) :
    (fun x ↦ x + u x) '' s = s := by
  refine (image_subset_iff.2 fun x hx ↦ hu.add_mem_of_forall_frontier_eq_zero hK h₀ hx).antisymm
    fun y hy ↦ ?_
  obtain ⟨x, hxy⟩ := (hu.idAddHomeomorph ℝ hK).surjective y
  rw [coe_idAddHomeomorph] at hxy
  subst hxy
  -- The complement of `s` has the same frontier, so it is invariant too.
  refine ⟨x, by_contra fun hx ↦ ?_, by simp⟩
  exact hu.add_mem_of_forall_frontier_eq_zero hK (s := sᶜ)
    (fun z hz ↦ h₀ z (frontier_compl s ▸ hz)) hx hy

/-- The case `u = ε • v` of `LipschitzWith.add_mem_of_forall_frontier_eq_zero`. -/
theorem add_smul_mem_of_forall_frontier_eq_zero (hv : LipschitzWith K v) (hε : ‖ε‖₊ * K < 1)
    (h₀ : ∀ y ∈ frontier s, v y = 0) (hx : x ∈ s) : x + ε • v x ∈ s :=
  ((lipschitzWith_smul ε).comp hv).add_mem_of_forall_frontier_eq_zero hε
    (fun y hy ↦ by simp [h₀ y hy]) hx

/-- The case `u = ε • v` of `LipschitzWith.idAddHomeomorph`. -/
theorem exists_homeomorph_id_add_smul [CompleteSpace E] (hv : LipschitzWith K v)
    (hε : ‖ε‖₊ * K < 1) : ∃ e : E ≃ₜ E, ⇑e = fun x ↦ x + ε • v x :=
  have hu : LipschitzWith (‖ε‖₊ * K) fun x ↦ ε • v x := (lipschitzWith_smul ε).comp hv
  ⟨hu.idAddHomeomorph ℝ hε, hu.coe_idAddHomeomorph ℝ hε⟩

/-- The case `u = ε • v` of `LipschitzWith.image_add_eq_of_forall_frontier_eq_zero`. -/
theorem image_add_smul_eq_of_forall_frontier_eq_zero [CompleteSpace E] (hv : LipschitzWith K v)
    (hε : ‖ε‖₊ * K < 1) (h₀ : ∀ y ∈ frontier s, v y = 0) : (fun x ↦ x + ε • v x) '' s = s :=
  have hu : LipschitzWith (‖ε‖₊ * K) fun x ↦ ε • v x := (lipschitzWith_smul ε).comp hv
  hu.image_add_eq_of_forall_frontier_eq_zero hε fun y hy ↦ by simp [h₀ y hy]

end LipschitzWith
