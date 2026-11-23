/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A two-point problem for a scalar linear ODE

Let `σ` and `φ` be continuous on `ℝ` and let `a, b ∈ ℝ`. The equation `u' + σ u = φ - c` has a
solution with `u a = 0` and `u b = 0` for a suitable constant `c`, the mean of `φ` on `[a, b]` with
respect to the integrating factor `exp (∫ σ)`. This is the one-dimensional Stein equation.

## Main statements

* `exists_hasDerivAt_sub_sub_mul`: the solution of the two-point problem.
-/

@[expose] public section

open intervalIntegral

/-- **The scalar two-point problem.** Let `σ` and `φ` be continuous and let `a, b ∈ ℝ`. There are a
constant `c` and a function `u` such that `u a = 0`, `u b = 0` and `u' = φ - c - σ u` on `ℝ`. -/
theorem exists_hasDerivAt_sub_sub_mul {σ φ : ℝ → ℝ} (hσ : Continuous σ) (hφ : Continuous φ)
    (a b : ℝ) :
    ∃ c : ℝ, ∃ u : ℝ → ℝ, u a = 0 ∧ u b = 0 ∧ ∀ t, HasDerivAt u (φ t - c - σ t * u t) t := by
  -- The integrating factor `w t = exp (∫₀ᵗ σ)`, with `w' = w σ`.
  set w : ℝ → ℝ := fun t ↦ Real.exp (∫ τ in (0 : ℝ)..t, σ τ)
  have hw (t : ℝ) : HasDerivAt w (w t * σ t) t :=
    (hσ.integral_hasStrictDerivAt 0 t).hasDerivAt.exp
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun t ↦ (hw t).continuousAt
  -- `c` is the mean of `φ` on `[a, b]` with respect to `w`, and `u = w⁻¹ ∫ₐ w (φ - c)`.
  set c := (∫ t in a..b, w t * φ t) / ∫ t in a..b, w t with hc
  set A : ℝ → ℝ := fun t ↦ ∫ τ in a..t, w τ * (φ τ - c)
  have hA (t : ℝ) : HasDerivAt A (w t * (φ t - c)) t :=
    ((hwc.mul (hφ.sub continuous_const)).integral_hasStrictDerivAt a t).hasDerivAt
  refine ⟨c, fun t ↦ A t / w t, by simp [A], ?_, fun t ↦ ?_⟩
  · have hAb : A b = 0 := by
      rcases eq_or_ne a b with rfl | hab
      · simp [A]
      -- As `w > 0`, `∫ₐᵇ w ≠ 0`, so that `∫ₐᵇ w (φ - c) = ∫ₐᵇ w φ - c ∫ₐᵇ w = 0`.
      have hwI : ∫ t in a..b, w t ≠ 0 := by
        rcases hab.lt_or_gt with hab | hab
        · exact (intervalIntegral_pos_of_pos_on (hwc.intervalIntegrable a b)
            (fun t _ ↦ Real.exp_pos _) hab).ne'
        · rw [integral_symm]
          exact neg_ne_zero.2 (intervalIntegral_pos_of_pos_on (hwc.intervalIntegrable b a)
            (fun t _ ↦ Real.exp_pos _) hab).ne'
      simp only [A, mul_sub]
      rw [integral_sub (f := fun τ ↦ w τ * φ τ) (g := fun τ ↦ w τ * c)
        ((hwc.mul hφ).intervalIntegrable a b) ((hwc.mul continuous_const).intervalIntegrable a b),
        integral_mul_const, hc, mul_div_cancel₀ _ hwI, sub_self]
    simp [hAb]
  · have hwt : w t ≠ 0 := (Real.exp_pos _).ne'
    convert (hA t).div (hw t) hwt using 1
    field_simp
