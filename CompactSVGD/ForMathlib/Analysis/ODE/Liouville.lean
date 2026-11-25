/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Trace

import CompactSVGD.ForMathlib.Analysis.Calculus.FDeriv.DetIdAddSMul
import CompactSVGD.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.ODE.ExistUnique
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

/-!
# Liouville's formula

If `J : 𝕜 → E →L[𝕜] E` solves `J' t = A t ∘ J t` on a finite-dimensional normed space over a
complete nontrivially normed field `𝕜`, then
`(det J)' t = trace (A t) * det J t`, without assuming that `J t` is invertible. A solution of the
scalar equation `f' = c f` with bounded `c` and `f s > 0` stays positive, and its logarithm is
Lipschitz. So the Jacobian determinant of a flow stays positive and its logarithm grows at most
linearly.

## Main statements

* `hasDerivAt_det_of_hasDerivAt_comp`: **Liouville's formula**.
* `pos_of_hasDerivAt_mul`: positivity of solutions of `f' = c f` with `f s > 0`.
* `abs_log_sub_log_le_of_hasDerivAt_mul`: the logarithm of such a solution is Lipschitz.
-/

@[expose] public section

open Set Module

open scoped NNReal

/-- **Liouville's formula.** If `J' t = A ∘ J t`, then `(det J)' t = trace A * det (J t)`. -/
theorem hasDerivAt_det_of_hasDerivAt_comp {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {J : 𝕜 → E →L[𝕜] E} {A : E →L[𝕜] E} {t : 𝕜} (hJ : HasDerivAt J (A.comp (J t)) t) :
    HasDerivAt (fun t ↦ (J t).det) (LinearMap.trace 𝕜 E A * (J t).det) t := by
  have hdet : Differentiable 𝕜 fun B : E →L[𝕜] E ↦ LinearMap.det (B : E →ₗ[𝕜] E) :=
    (ContinuousLinearMap.contDiff_det (𝕜 := 𝕜) (E := E) (r := 1)).differentiable one_ne_zero
  -- Along the curve `P τ = (id + (τ - t) • A) ∘ J t`, which has the same derivative as `J` at `t`,
  -- the determinant is `det (id + (τ - t) • A) * det (J t)`.
  set P : 𝕜 → E →L[𝕜] E := fun τ ↦ (ContinuousLinearMap.id 𝕜 E + (τ - t) • A).comp (J t)
  have hP : HasDerivAt P (A.comp (J t)) t := by
    have : HasDerivAt (fun τ : 𝕜 ↦ J t + (τ - t) • A.comp (J t)) (A.comp (J t)) t := by
      simpa using (((hasDerivAt_id t).sub_const t).smul_const (A.comp (J t))).const_add (J t)
    convert this using 1
    funext τ
    simp [P, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp]
  have hPt : P t = J t := by simp [P]
  have h₁ := (hdet (P t)).hasFDerivAt.comp_hasDerivAt t hP
  have h₂ : HasDerivAt (fun τ ↦ LinearMap.det (P τ : E →ₗ[𝕜] E))
      (LinearMap.trace 𝕜 E A * LinearMap.det (J t : E →ₗ[𝕜] E)) t := by
    have h := ((hasDerivAt_det_id_add_smul_zero A).comp_of_eq t ((hasDerivAt_id t).sub_const t)
      (by simp)).mul_const (LinearMap.det (J t : E →ₗ[𝕜] E))
    simp only [Function.comp_def, id, mul_one] at h
    convert h using 1
    funext τ
    simp only [P, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  have hD := h₁.unique h₂
  rw [hPt] at hD
  rw [← hD]
  exact (hdet (J t)).hasFDerivAt.comp_hasDerivAt t hJ

/-- A solution of the scalar linear equation `f' = c f` with `c` bounded and `f s > 0` is
positive. Indeed, by uniqueness, a solution vanishing at one time vanishes identically. -/
theorem pos_of_hasDerivAt_mul {f c : ℝ → ℝ} {C : ℝ≥0} (hf : ∀ t, HasDerivAt f (c t * f t) t)
    (hc : ∀ t, |c t| ≤ C) {s : ℝ} (hs : 0 < f s) (t : ℝ) : 0 < f t := by
  by_contra ht
  push Not at ht
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t ↦ (hf t).continuousAt
  obtain ⟨τ, -, hτ⟩ := intermediate_value_uIcc (a := s) (b := t) hfc.continuousOn
    (show (0 : ℝ) ∈ uIcc (f s) (f t) from mem_uIcc.2 (Or.inr ⟨ht, hs.le⟩))
  have hlip (τ : ℝ) : LipschitzWith C fun y : ℝ ↦ c τ * y :=
    LipschitzWith.of_dist_le_mul fun y y' ↦ by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      gcongr
      exact hc τ
  have h0 : f = fun _ ↦ 0 := ODE_solution_unique_univ (s := fun _ ↦ univ) (t₀ := τ)
    (fun τ ↦ (hlip τ).lipschitzOnWith) (fun t ↦ ⟨hf t, trivial⟩)
    (fun t ↦ ⟨by simpa using hasDerivAt_const t (0 : ℝ), trivial⟩) hτ
  exact hs.ne' (congrFun h0 s)

/-- The logarithm of a solution of the scalar linear equation `f' = c f` with `|c| ≤ C` and
`f s > 0` is `C`-Lipschitz: `|log f t - log f s| ≤ C |t - s|`. -/
theorem abs_log_sub_log_le_of_hasDerivAt_mul {f c : ℝ → ℝ} {C : ℝ≥0}
    (hf : ∀ t, HasDerivAt f (c t * f t) t) (hc : ∀ t, |c t| ≤ C) {s : ℝ} (hs : 0 < f s)
    (t : ℝ) : |Real.log (f t) - Real.log (f s)| ≤ C * |t - s| := by
  have hpos := pos_of_hasDerivAt_mul hf hc hs
  have hlog (τ : ℝ) : HasDerivAt (fun τ ↦ Real.log (f τ)) (c τ) τ :=
    hasDerivAt_log_of_hasDerivAt_mul (hf τ) (hpos τ).ne'
  have := (lipschitzWith_of_nnNorm_deriv_le (C := C) (fun τ ↦ (hlog τ).differentiableAt)
    fun τ ↦ by
      rw [(hlog τ).deriv, ← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs]
      exact hc τ).dist_le_mul t s
  rwa [Real.dist_eq, Real.dist_eq] at this
