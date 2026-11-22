/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Lipschitz perturbations of the identity

Let `v : E → E` be a `K`-Lipschitz map on a Banach space and let `ε` be a scalar with
`|ε| K < 1`. Then `x ↦ x + ε • v x` is a homeomorphism of `E` (`LipschitzWith.addSMulHomeomorph`):
it approximates the identity with constant `|ε| K < 1`.

If moreover `v` vanishes on the frontier of a closed set `s`, this homeomorphism maps `s` onto
`s` (`LipschitzWith.addSMulHomeomorph_image`). Indeed, a point of `s` sent outside `s` would
cross the frontier of `s` along the segment `τ ↦ x + τ • v x`, at a point fixed by the
perturbation, which contradicts injectivity.

These perturbations `I + ε v` are the transport maps along which the first variation of the
Kullback–Leibler divergence is computed in Stein Variational Gradient Descent.

## Main definitions

* `LipschitzWith.addSMulHomeomorph`: the homeomorphism `x ↦ x + ε • v x`.

## Main statements

* `hasFDerivAt_add_smul`: the derivative of `x ↦ x + ε • v x` is `id + ε • Dv`.
* `LipschitzWith.add_smul_mem`: if `v` vanishes on the frontier of the closed set `s`, then
  `x + ε • v x ∈ s` for `x ∈ s`.
* `LipschitzWith.addSMulHomeomorph_image`: the homeomorphism maps `s` onto `s`.
-/

@[expose] public section

open Set Metric

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E → E} {K : ℝ≥0} {ε : ℝ}

/-- The derivative of the perturbation `y ↦ y + ε • v y` of the identity is `id + ε • Dv`. -/
theorem hasFDerivAt_add_smul {x : E} (hv : DifferentiableAt ℝ v x) :
    HasFDerivAt (fun y ↦ y + ε • v y) (ContinuousLinearMap.id ℝ E + ε • fderiv ℝ v x) x :=
  (hasFDerivAt_id x).add (hv.hasFDerivAt.const_smul ε)

namespace LipschitzWith

/-- `x ↦ x + ε • v x` approximates the identity with constant `|ε| K`. -/
theorem approximatesLinearOn_add_smul (hv : LipschitzWith K v) (ε : ℝ) :
    ApproximatesLinearOn (fun x ↦ x + ε • v x) (ContinuousLinearMap.id ℝ E) univ (‖ε‖₊ * K) :=
  fun x _ y _ ↦ by
    have : x + ε • v x - (y + ε • v y) - ContinuousLinearMap.id ℝ E (x - y) =
        ε • (v x - v y) := by
      simp only [ContinuousLinearMap.id_apply, smul_sub]
      abel
    rw [this, norm_smul, NNReal.coe_mul, coe_nnNorm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hv.norm_sub_le x y) (norm_nonneg ε)

variable [CompleteSpace E]

/-- For `|ε| K < 1`, the perturbation `x ↦ x + ε • v x` of the identity is a homeomorphism. -/
noncomputable def addSMulHomeomorph (hv : LipschitzWith K v) (hε : ‖ε‖₊ * K < 1) : E ≃ₜ E :=
  (hv.approximatesLinearOn_add_smul ε).toHomeomorph (f' := ContinuousLinearEquiv.refl ℝ E) _ <| by
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    · right
      simpa using hε

@[simp]
theorem coe_addSMulHomeomorph (hv : LipschitzWith K v) (hε : ‖ε‖₊ * K < 1) :
    ⇑(hv.addSMulHomeomorph hε) = fun x ↦ x + ε • v x :=
  rfl

theorem injective_add_smul (hv : LipschitzWith K v) (hε : ‖ε‖₊ * K < 1) :
    Function.Injective fun x ↦ x + ε • v x :=
  (hv.addSMulHomeomorph hε).injective

/-- **Invariance of a closed set under a perturbation of the identity.** Let `s` be closed and let
`v` vanish on the frontier of `s`. If `|ε| K < 1`, then `x + ε • v x ∈ s` for every `x ∈ s`. -/
theorem add_smul_mem (hv : LipschitzWith K v) (hε : ‖ε‖₊ * K < 1) {s : Set E} (hs : IsClosed s)
    (h₀ : ∀ y ∈ frontier s, v y = 0) {x : E} (hx : x ∈ s) : x + ε • v x ∈ s := by
  by_contra hout
  -- The segment `τ ↦ x + τ • v x`, `τ ∈ [0, ε]`, joins a point of `s` to a point outside `s`.
  let γ : ℝ → E := fun τ ↦ x + τ • v x
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  -- It meets the frontier of `s`.
  obtain ⟨τ, hτ, hfr⟩ : ∃ τ ∈ uIcc 0 ε, γ τ ∈ frontier s := by
    by_contra hne
    push Not at hne
    obtain ⟨_, ⟨τ, hτ, rfl⟩, hτ₁, hτ₂⟩ := (isPreconnected_uIcc.image γ hγ.continuousOn)
      (interior s) (closure s)ᶜ isOpen_interior isClosed_closure.isOpen_compl
      (by
        rintro _ ⟨τ, hτ, rfl⟩
        by_cases hcl : γ τ ∈ closure s
        · exact Or.inl (by_contra fun hi ↦ hne τ hτ ⟨hcl, hi⟩)
        · exact Or.inr hcl)
      ⟨γ 0, ⟨0, left_mem_uIcc, rfl⟩, by_contra fun hi ↦ hne 0 left_mem_uIcc
        ⟨subset_closure (by simpa [γ] using hx), hi⟩⟩
      ⟨γ ε, ⟨ε, right_mem_uIcc, rfl⟩, by rwa [hs.closure_eq]⟩
    exact hτ₂ (interior_subset_closure hτ₁)
  -- The point `γ τ` is fixed by `x ↦ x + τ • v x`, as is its preimage `x`, so `x = γ τ`.
  have hτε : ‖τ‖₊ * K < 1 := lt_of_le_of_lt (by
    gcongr
    rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm, Real.norm_eq_abs, Real.norm_eq_abs]
    simpa using abs_sub_left_of_mem_uIcc hτ) hε
  have hxγ : x = γ τ := hv.injective_add_smul hτε (by
    simp only [γ, h₀ _ hfr, smul_zero, add_zero])
  have hvx : v x = 0 := hxγ ▸ h₀ _ hfr
  exact hout (by simpa [hvx] using hx)

/-- **A perturbation of the identity maps `s` onto `s`.** Let `s` be closed and let `v` vanish on
the frontier of `s`. If `|ε| K < 1`, then `x ↦ x + ε • v x` maps `s` onto `s`. -/
theorem addSMulHomeomorph_image (hv : LipschitzWith K v) (hε : ‖ε‖₊ * K < 1) {s : Set E}
    (hs : IsClosed s) (h₀ : ∀ y ∈ frontier s, v y = 0) : hv.addSMulHomeomorph hε '' s = s := by
  refine (image_subset_iff.2 fun x hx ↦ hv.add_smul_mem hε hs h₀ hx).antisymm fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := (hv.addSMulHomeomorph hε).surjective y
  refine ⟨x, ?_, rfl⟩
  by_contra hx
  -- `x` lies in the closure of the complement of `s`, which is also invariant.
  have hcl : (hv.addSMulHomeomorph hε) x ∈ closure sᶜ :=
    hv.add_smul_mem hε isClosed_closure
      (fun z hz ↦ h₀ z (frontier_compl s ▸ frontier_closure_subset hz)) (subset_closure hx)
  have hfr : (hv.addSMulHomeomorph hε) x ∈ frontier s := by
    rw [frontier_eq_closure_inter_closure, hs.closure_eq]
    exact ⟨hy, hcl⟩
  have hfix : (hv.addSMulHomeomorph hε) ((hv.addSMulHomeomorph hε) x) =
      (hv.addSMulHomeomorph hε) x := by
    have h := h₀ _ hfr
    simp only [coe_addSMulHomeomorph] at h ⊢
    simp [h]
  exact hx (by simpa using (hv.addSMulHomeomorph hε).injective hfix ▸ hy)

end LipschitzWith
