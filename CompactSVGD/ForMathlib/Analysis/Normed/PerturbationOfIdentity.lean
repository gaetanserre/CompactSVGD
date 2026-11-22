/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

import CompactSVGD.ForMathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Lipschitz perturbations of the identity

Let `u : E → E` be `K`-Lipschitz with `K < 1` on a complete normed group. Then `x ↦ x + u x` is
antilipschitz, and onto by Banach's fixed-point theorem, so it is a homeomorphism
(`LipschitzWith.exists_homeomorph_id_add`). If `u` vanishes on the frontier of a set `s`, then
`x ↦ x + u x` maps `s` into `s`, and onto `s`. Indeed, a point of `s` sent outside `s` would cross
the frontier of `s` along the segment `τ ↦ x + τ • u x`, at a point fixed by `y ↦ y + τ • u y`,
which contradicts injectivity.

## Main statements

* `LipschitzWith.add_mem_of_forall_frontier_eq_zero`: `x + u x ∈ s` for every `x ∈ s`.
* `LipschitzWith.exists_homeomorph_id_add`: `x ↦ x + u x` is a homeomorphism.
* `LipschitzWith.image_add_eq_of_forall_frontier_eq_zero`: `x ↦ x + u x` maps `s` onto `s`.

## Implementation notes

Mathlib's `ApproximatesLinearOn.toHomeomorph` gives the same homeomorphism, but needs a normed
space structure over a field. The construction by Banach's fixed-point theorem does not.
-/

@[expose] public section

open Set

open scoped NNReal

namespace LipschitzWith

section Homeomorph

theorem antilipschitzWith_id_add {E : Type*} [SeminormedAddCommGroup E] {u : E → E} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hK : K < 1) : AntilipschitzWith (1 - K)⁻¹ fun x ↦ x + u x := by
  simpa using AntilipschitzWith.id.add_lipschitzWith hu (by simpa using hK)

variable {E : Type*} [NormedAddCommGroup E] {u : E → E} {K : ℝ≥0}

theorem surjective_id_add [CompleteSpace E] (hu : LipschitzWith K u) (hK : K < 1) :
    Function.Surjective fun x ↦ x + u x := fun y ↦ by
  -- A solution of `x + u x = y` is a fixed point of the contraction `x ↦ y - u x`.
  have hc : ContractingWith K fun x ↦ y - u x :=
    ⟨hK, ((LipschitzWith.const y).sub hu).weaken (by simp)⟩
  exact ⟨_, eq_sub_iff_add_eq.1 hc.fixedPoint_isFixedPt.symm⟩

/-- **A Lipschitz-small perturbation of the identity is a homeomorphism.** If `u` is `K`-Lipschitz
with `K < 1` on a complete normed group, then `x ↦ x + u x` is a homeomorphism. -/
theorem exists_homeomorph_id_add [CompleteSpace E] (hu : LipschitzWith K u) (hK : K < 1) :
    ∃ e : E ≃ₜ E, ⇑e = fun x ↦ x + u x :=
  ⟨(Equiv.ofBijective _ ⟨(hu.antilipschitzWith_id_add hK).injective,
    hu.surjective_id_add hK⟩).toHomeomorphOfIsInducing
    ((hu.antilipschitzWith_id_add hK).isUniformInducing
      (uniformContinuous_id.add hu.uniformContinuous)).isInducing, rfl⟩

end Homeomorph

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
  obtain ⟨x, rfl⟩ := hu.surjective_id_add hK y
  -- The complement of `s` has the same frontier, so it is invariant too.
  refine ⟨x, by_contra fun hx ↦ ?_, by simp⟩
  exact hu.add_mem_of_forall_frontier_eq_zero hK (s := sᶜ)
    (fun z hz ↦ h₀ z (frontier_compl s ▸ hz)) hx hy

/-- The case `u = ε • v` of `LipschitzWith.add_mem_of_forall_frontier_eq_zero`. -/
theorem add_smul_mem_of_forall_frontier_eq_zero (hv : LipschitzWith K v) (hε : ‖ε‖₊ * K < 1)
    (h₀ : ∀ y ∈ frontier s, v y = 0) (hx : x ∈ s) : x + ε • v x ∈ s :=
  ((lipschitzWith_smul ε).comp hv).add_mem_of_forall_frontier_eq_zero hε
    (fun y hy ↦ by simp [h₀ y hy]) hx

end LipschitzWith
