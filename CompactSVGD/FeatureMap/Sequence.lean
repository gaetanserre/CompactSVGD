/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.l2Space

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The feature map of a sequence of functions

Let `gₙ : E → ℝ` be `C¹` functions such that `‖gₙ‖ + ‖Dgₙ‖` is bounded for every `n`. The feature
map `SVGD.seqFeatureMap g : x ↦ (wₙ gₙ(x))ₙ ∈ ℓ²(ℕ, ℝ)` (`CompactSVGD/Definitions.lean`) has
positive weights `wₙ = SVGD.seqWeight g n` with `wₙ (‖gₙ‖ + ‖Dgₙ‖) ≤ 2⁻ⁿ`, so that the series
`∑ₙ wₙ gₙ(x) eₙ` converges in `C¹`. Thus it is `C¹`, bounded by `2` and `2`-Lipschitz, and every
finite linear combination of the `gₙ` is `x ↦ ⟪h, Φ x⟫` for some `h ∈ ℓ²(ℕ, ℝ)`.

## Main statements

* `SVGD.inner_seqFeatureMap`: the kernel of the feature map is `∑ₙ wₙ² gₙ(x) gₙ(y)`.
* `SVGD.contDiff_seqFeatureMap`, `SVGD.norm_seqFeatureMap_le`, `SVGD.lipschitzWith_seqFeatureMap`:
  the regularity of the feature map.
* `SVGD.exists_inner_seqFeatureMap_eq`: the finite linear combinations of the `gₙ` are of the form
  `x ↦ ⟪h, Φ x⟫`.
-/

@[expose] public section

open Set
open scoped lp NNReal RealInnerProductSpace

noncomputable section

namespace SVGD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ → E → ℝ}

private theorem iSup_norm_add_norm_fderiv_nonneg (g : ℕ → E → ℝ) (n : ℕ) :
    0 ≤ ⨆ x, (‖g n x‖ + ‖fderiv ℝ (g n) x‖) :=
  Real.iSup_nonneg fun _ ↦ by positivity

theorem seqWeight_pos (g : ℕ → E → ℝ) (n : ℕ) : 0 < seqWeight g n := by
  have := iSup_norm_add_norm_fderiv_nonneg g n
  rw [seqWeight]
  positivity

/-- `wₙ a ≤ 2⁻ⁿ` for every `a ≤ ‖gₙ x‖ + ‖Dgₙ x‖`. -/
private theorem seqWeight_mul_le {n : ℕ}
    (hb : BddAbove (range fun x ↦ ‖g n x‖ + ‖fderiv ℝ (g n) x‖)) {a : ℝ} {x : E}
    (ha : a ≤ ‖g n x‖ + ‖fderiv ℝ (g n) x‖) : seqWeight g n * a ≤ 2⁻¹ ^ n := by
  have hM₀ := iSup_norm_add_norm_fderiv_nonneg g n
  rw [seqWeight]
  set M := ⨆ x, (‖g n x‖ + ‖fderiv ℝ (g n) x‖)
  calc 2⁻¹ ^ n / (1 + M) * a ≤ 2⁻¹ ^ n / (1 + M) * (1 + M) := by
        gcongr
        linarith [le_ciSup hb x]
    _ = 2⁻¹ ^ n := div_mul_cancel₀ _ (by positivity)

private theorem hasSum_geometric_inv_two : HasSum (fun n : ℕ ↦ (2⁻¹ : ℝ) ^ n) 2 := by
  simpa [one_div] using hasSum_geometric_two

/-- The `n`-th term `wₙ gₙ(x) eₙ` of the series of `SVGD.seqFeatureMap g`. -/
private def seqTerm (g : ℕ → E → ℝ) (n : ℕ) (x : E) : ℓ²(ℕ, ℝ) :=
  (seqWeight g n * g n x) • lp.single 2 n 1

private theorem seqFeatureMap_eq_tsum : seqFeatureMap g = fun x ↦ ∑' n, seqTerm g n x :=
  rfl

private theorem seqTerm_eq (n : ℕ) (x : E) :
    seqTerm g n x = lp.single 2 n (seqWeight g n * g n x) := by
  rw [seqTerm, ← lp.single_smul, smul_eq_mul, mul_one]

private theorem norm_seqTerm (n : ℕ) (x : E) :
    ‖seqTerm g n x‖ = seqWeight g n * ‖g n x‖ := by
  rw [seqTerm_eq, lp.norm_single (by norm_num), norm_mul,
    Real.norm_of_nonneg (seqWeight_pos g n).le]

private theorem norm_seqTerm_le {n : ℕ}
    (hb : BddAbove (range fun x ↦ ‖g n x‖ + ‖fderiv ℝ (g n) x‖)) (x : E) :
    ‖seqTerm g n x‖ ≤ 2⁻¹ ^ n := by
  rw [norm_seqTerm]
  exact seqWeight_mul_le hb (le_add_of_nonneg_right (norm_nonneg _))

private theorem contDiff_seqTerm {n : ℕ} (hg : ContDiff ℝ 1 (g n)) :
    ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞) (seqTerm g n) :=
  (contDiff_const.mul hg).smul contDiff_const

/-- The terms of the series of `SVGD.seqFeatureMap g` and their derivatives are bounded by `2⁻ⁿ`. -/
private theorem norm_iteratedFDeriv_seqTerm_le (hg : ∀ n, ContDiff ℝ 1 (g n))
    (hb : ∀ n, BddAbove (range fun x ↦ ‖g n x‖ + ‖fderiv ℝ (g n) x‖)) (k n : ℕ) (x : E)
    (hk : (k : ℕ∞) ≤ 1) : ‖iteratedFDeriv ℝ k (seqTerm g n) x‖ ≤ 2⁻¹ ^ n := by
  obtain rfl | rfl : k = 0 ∨ k = 1 := by
    have : k ≤ 1 := by exact_mod_cast hk
    omega
  · rw [norm_iteratedFDeriv_zero]
    exact norm_seqTerm_le (hb n) x
  · have hd := (hg n).differentiable one_ne_zero x
    have hw := (seqWeight_pos g n).le
    rw [norm_iteratedFDeriv_one]
    change ‖fderiv ℝ (fun x ↦ (seqWeight g n * g n x) • (lp.single 2 n 1 : ℓ²(ℕ, ℝ))) x‖ ≤ _
    rw [fderiv_smul_const (hd.const_mul _),
      ContinuousLinearMap.norm_smulRight_apply, lp.norm_single (by norm_num), norm_one, mul_one,
      fderiv_const_mul hd, norm_smul, Real.norm_of_nonneg hw]
    exact seqWeight_mul_le (hb n) (le_add_of_nonneg_left (norm_nonneg _))

variable (hg : ∀ n, ContDiff ℝ 1 (g n))
  (hb : ∀ n, BddAbove (range fun x ↦ ‖g n x‖ + ‖fderiv ℝ (g n) x‖))
include hb

theorem seqFeatureMap_apply (x : E) (n : ℕ) : seqFeatureMap g x n = seqWeight g n * g n x := by
  have hmem : Memℓp (fun n ↦ seqWeight g n * g n x) 2 := by
    refine memℓp_gen (hasSum_geometric_inv_two.summable.of_nonneg_of_le (fun _ ↦ by positivity)
      fun n ↦ ?_)
    have h := norm_seqTerm_le (hb n) x
    rw [norm_seqTerm, ← Real.norm_of_nonneg (seqWeight_pos g n).le, ← norm_mul] at h
    have h₁ : (2⁻¹ : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
    nlinarith [norm_nonneg (seqWeight g n * g n x)]
  have hsum : HasSum (seqTerm g · x) (⟨_, hmem⟩ : ℓ²(ℕ, ℝ)) := by
    simpa only [seqTerm_eq] using lp.hasSum_single ENNReal.ofNat_ne_top (⟨_, hmem⟩ : ℓ²(ℕ, ℝ))
  have h : seqFeatureMap g x = ⟨_, hmem⟩ := hsum.tsum_eq
  rw [h]

theorem inner_single_seqFeatureMap (n : ℕ) (x : E) :
    ⟪(lp.single 2 n 1 : ℓ²(ℕ, ℝ)), seqFeatureMap g x⟫ = seqWeight g n * g n x := by
  rw [lp.inner_single_left, seqFeatureMap_apply hb]
  simp

/-- **The kernel of `SVGD.seqFeatureMap g`** is `k(x, y) = ∑ₙ wₙ² gₙ(x) gₙ(y)`. -/
theorem inner_seqFeatureMap (x y : E) :
    ⟪seqFeatureMap g x, seqFeatureMap g y⟫ = ∑' n, seqWeight g n ^ 2 * g n x * g n y := by
  simp_rw [lp.inner_eq_tsum, seqFeatureMap_apply hb]
  congr with n
  simp
  ring

/-- Every finite linear combination of the `gₙ` is of the form `x ↦ ⟪h, Φ x⟫`, where
`Φ = SVGD.seqFeatureMap g`. -/
theorem exists_inner_seqFeatureMap_eq (b : ℕ → ℝ) (s : Finset ℕ) :
    ∃ h : ℓ²(ℕ, ℝ), ∀ x, ⟪h, seqFeatureMap g x⟫ = ∑ n ∈ s, b n * g n x := by
  refine ⟨∑ n ∈ s, (b n / seqWeight g n) • lp.single 2 n 1, fun x ↦ ?_⟩
  simp_rw [sum_inner, real_inner_smul_left, inner_single_seqFeatureMap hb]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  field_simp [(seqWeight_pos g n).ne']

/-- `SVGD.seqFeatureMap g` is bounded by `2`. -/
theorem norm_seqFeatureMap_le (x : E) : ‖seqFeatureMap g x‖ ≤ 2 :=
  tsum_of_norm_bounded hasSum_geometric_inv_two fun n ↦ norm_seqTerm_le (hb n) x

include hg

/-- `SVGD.seqFeatureMap g` is `C¹`. -/
theorem contDiff_seqFeatureMap : ContDiff ℝ 1 (seqFeatureMap g) := by
  rw [seqFeatureMap_eq_tsum]
  exact_mod_cast contDiff_tsum (N := 1) (fun n ↦ contDiff_seqTerm (hg n))
    (fun _ _ ↦ hasSum_geometric_inv_two.summable) (norm_iteratedFDeriv_seqTerm_le hg hb)

theorem norm_fderiv_seqFeatureMap_le (x : E) : ‖fderiv ℝ (seqFeatureMap g) x‖ ≤ 2 := by
  rw [← norm_iteratedFDeriv_one, seqFeatureMap_eq_tsum,
    iteratedFDeriv_tsum_apply (N := 1) (fun n ↦ contDiff_seqTerm (hg n))
      (fun _ _ ↦ hasSum_geometric_inv_two.summable) (norm_iteratedFDeriv_seqTerm_le hg hb) le_rfl]
  exact tsum_of_norm_bounded hasSum_geometric_inv_two fun n ↦
    norm_iteratedFDeriv_seqTerm_le hg hb 1 n x le_rfl

/-- `SVGD.seqFeatureMap g` is `2`-Lipschitz. -/
theorem lipschitzWith_seqFeatureMap : LipschitzWith 2 (seqFeatureMap g) :=
  lipschitzWith_of_nnNorm_fderiv_le ((contDiff_seqFeatureMap hg hb).differentiable one_ne_zero)
    fun x ↦ by exact_mod_cast norm_fderiv_seqFeatureMap_le hg hb x

omit hg hb in
theorem seqFeatureMap_eq_zero {x : E} (hx : ∀ n, g n x = 0) : seqFeatureMap g x = 0 := by
  simp [seqFeatureMap, hx]

end SVGD
