/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Regularity of the vector fields of a feature map

Let `Φ : ℝᵈ → H₀` be a map into a real inner product space. An element `h` of the Hilbert sum
`𝓗[d, H₀] = H₀ᵈ` defines the vector field `toVectorField Φ h : y ↦ (⟪hᵢ, Φ y⟫)ᵢ` on `ℝᵈ`
(`CompactSVGD/Definitions.lean`). This file proves its regularity: it is `1`-Lipschitz, hence
continuous, in `h`, differentiable when `Φ` is, Lipschitz and bounded when `Φ` is, and it vanishes
where `Φ` does.
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-! ### The vector field of an element of `𝓗` -/

@[simp]
theorem pairing_apply (h : 𝓗[d, H₀]) (u : H₀) (i : Fin d) : pairing h u i = inner ℝ (h i) u :=
  rfl

theorem pairing_sub (h h' : 𝓗[d, H₀]) : pairing (h - h') = pairing h - pairing h' :=
  ContinuousLinearMap.ext fun u ↦ by
    ext i
    simp [inner_sub_left]

variable {Φ : EuclideanSpace ℝ (Fin d) → H₀} {h h' : 𝓗[d, H₀]} {y y' : EuclideanSpace ℝ (Fin d)}

@[simp]
theorem toVectorField_apply (i : Fin d) : toVectorField Φ h y i = inner ℝ (h i) (Φ y) :=
  rfl

theorem toVectorField_eq_zero_of_eq_zero (hy : Φ y = 0) : toVectorField Φ h y = 0 := by
  simp [toVectorField, hy]

theorem hasFDerivAt_toVectorField {Φ' : EuclideanSpace ℝ (Fin d) →L[ℝ] H₀}
    (hΦ : HasFDerivAt Φ Φ' y) :
    HasFDerivAt (toVectorField Φ h) ((pairing h).comp Φ') y :=
  (pairing h).hasFDerivAt.comp y hΦ

/-- The Cauchy–Schwarz inequality for the pairing: `‖(⟪hᵢ, u⟫)ᵢ‖ ≤ ‖h‖ ‖u‖`. -/
theorem norm_pairing_apply_le (h : 𝓗[d, H₀]) (u : H₀) : ‖pairing h u‖ ≤ ‖h‖ * ‖u‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using abs_real_inner_le_norm (h i) u) 2

/-- The operator norm of the pairing is at most `‖h‖`. -/
theorem norm_pairing_le (h : 𝓗[d, H₀]) : ‖pairing h‖ ≤ ‖h‖ :=
  (pairing h).opNorm_le_bound (norm_nonneg _) (norm_pairing_apply_le h)

/-- The pairing is `1`-Lipschitz in `h`, for the operator norm. -/
theorem lipschitzWith_pairing :
    LipschitzWith 1 (pairing : 𝓗[d, H₀] → H₀ →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
  LipschitzWith.of_dist_le_mul fun h h' ↦ by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← pairing_sub]
    exact norm_pairing_le _

/-- The pairing is continuous in `h`, for the operator norm. -/
theorem continuous_pairing :
    Continuous (pairing : 𝓗[d, H₀] → H₀ →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
  lipschitzWith_pairing.continuous

theorem norm_toVectorField_le : ‖toVectorField Φ h y‖ ≤ ‖h‖ * ‖Φ y‖ :=
  norm_pairing_apply_le h (Φ y)

theorem norm_toVectorField_sub_le :
    ‖toVectorField Φ h y - toVectorField Φ h y'‖ ≤ ‖h‖ * ‖Φ y - Φ y'‖ := by
  rw [toVectorField, toVectorField, ← map_sub]
  exact norm_pairing_apply_le h _

theorem norm_toVectorField_sub_toVectorField_le :
    ‖toVectorField Φ h y - toVectorField Φ h' y‖ ≤ ‖h - h'‖ * ‖Φ y‖ := by
  rw [toVectorField, toVectorField, ← sub_apply, ← pairing_sub]
  exact norm_pairing_apply_le _ _

variable {m : ℝ → 𝓗[d, H₀]} {B C K : ℝ≥0}

/-! ### Regularity of the vector field of a curve -/

theorem lipschitzWith_toVectorField (hΦ : LipschitzWith K Φ) (h : 𝓗[d, H₀]) :
    LipschitzWith (‖h‖₊ * K) (toVectorField Φ h) :=
  LipschitzWith.of_dist_le_mul fun y y' ↦ by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, coe_nnNorm, mul_assoc]
    exact norm_toVectorField_sub_le.trans (by gcongr; exact hΦ.norm_sub_le y y')

theorem lipschitzWith_toVectorField_of_norm_le (hΦ : LipschitzWith K Φ) {h : 𝓗[d, H₀]}
    (hh : ‖h‖ ≤ B) : LipschitzWith (B * K) (toVectorField Φ h) :=
  (lipschitzWith_toVectorField hΦ h).weaken (by gcongr; exact_mod_cast hh)

/-- The vector fields of a curve bounded by `B` are `B K`-Lipschitz. -/
theorem lipschitzWith_toVectorField_apply (hΦ : LipschitzWith K Φ) (hm : ∀ t, ‖m t‖ ≤ B)
    (t : ℝ) : LipschitzWith (B * K) (toVectorField Φ (m t)) :=
  lipschitzWith_toVectorField_of_norm_le hΦ (hm t)

theorem norm_toVectorField_le_of_le (hΦ : ∀ y, ‖Φ y‖ ≤ C) {h : 𝓗[d, H₀]} (hh : ‖h‖ ≤ B)
    (y : EuclideanSpace ℝ (Fin d)) :
    ‖toVectorField Φ h y‖ ≤ B * C :=
  norm_toVectorField_le.trans (by gcongr; exact hΦ y)

theorem continuous_toVectorField_apply (hm : Continuous m) (y : EuclideanSpace ℝ (Fin d)) :
    Continuous fun t ↦ toVectorField Φ (m t) y :=
  (continuous_pairing.comp hm).clm_apply continuous_const

/-- The derivative of the vector field of `m t` at `y`, for a differentiable feature map. -/
theorem hasFDerivAt_toVectorField_apply (hΦ : Differentiable ℝ Φ) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (toVectorField Φ (m t)) ((pairing (m t)).comp (fderiv ℝ Φ y)) y :=
  hasFDerivAt_toVectorField (hΦ y).hasFDerivAt

/-- The derivative `(t, y) ↦ (pairing (m t)).comp (fderiv ℝ Φ y)` of the vector field of `m t` at
`y` is jointly continuous. -/
theorem continuous_uncurry_pairing_comp_fderiv (hΦ : ContDiff ℝ 1 Φ) (hm : Continuous m) :
    Continuous (Function.uncurry fun t y ↦ (pairing (m t)).comp (fderiv ℝ Φ y)) :=
  (continuous_pairing.comp (hm.comp continuous_fst)).clm_comp
    ((hΦ.continuous_fderiv one_ne_zero).comp continuous_snd)

end SVGD
