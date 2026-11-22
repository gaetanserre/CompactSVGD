/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.IntermediateValue
public import SBS.Analysis.Calculus.FDeriv.DetIdAddSMul
public import SBS.Analysis.Normed.Module.Trace

/-!
# Liouville's formula

Let `E` be a finite-dimensional real normed space and let `J : ℝ → E →L[ℝ] E` solve a linear
equation `J' t = A t ∘ J t`. Then `det J` solves the scalar linear equation

  `(det J)' t = trace (A t) * det J t`

(`hasDerivAt_det_of_hasDerivAt_comp`). This is Liouville's formula. It holds without assuming that
`J t` is invertible: the curve `τ ↦ (id + (τ - t) • A) ∘ J t` has the same derivative as `J` at `t`,
and along it the determinant is `det (id + (τ - t) • A) * det (J t)`, whose derivative at `t` is
`trace A * det (J t)` by Jacobi's formula at the identity.

A solution of a scalar linear equation `f' = c f` with bounded `c` never vanishes unless it vanishes
identically (`pos_of_hasDerivAt_mul`), and its logarithm is `C`-Lipschitz if `|c| ≤ C`
(`abs_log_sub_log_le_of_hasDerivAt_mul`). In particular, the Jacobian determinant of a flow, which
equals `1` at the initial time, stays positive, and its logarithm grows at most linearly.

## Main statements

* `hasDerivAt_det_of_hasDerivAt_comp`: Liouville's formula.
* `pos_of_hasDerivAt_mul`: positivity of solutions of `f' = c f` with `f s > 0`.
* `abs_log_sub_log_le_of_hasDerivAt_mul`: the logarithm of such a solution is Lipschitz.
-/

@[expose] public section

open Set Module

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Liouville's formula.** If `J' t = A ∘ J t`, then `(det J)' t = trace A * det (J t)`. -/
theorem hasDerivAt_det_of_hasDerivAt_comp {J : ℝ → E →L[ℝ] E} {A : E →L[ℝ] E} {t : ℝ}
    (hJ : HasDerivAt J (A.comp (J t)) t) :
    HasDerivAt (fun t ↦ (J t).det) (LinearMap.trace ℝ E A * (J t).det) t := by
  have hdet : Differentiable ℝ fun B : E →L[ℝ] E ↦ LinearMap.det (B : E →ₗ[ℝ] E) :=
    (ContinuousLinearMap.contDiff_det (𝕜 := ℝ) (E := E) (r := 1)).differentiable one_ne_zero
  -- Along the curve `P τ = (id + (τ - t) • A) ∘ J t`, which has the same derivative as `J` at `t`,
  -- the determinant is `det (id + (τ - t) • A) * det (J t)`.
  set P : ℝ → E →L[ℝ] E := fun τ ↦ (ContinuousLinearMap.id ℝ E + (τ - t) • A).comp (J t)
  have hP : HasDerivAt P (A.comp (J t)) t := by
    have : HasDerivAt (fun τ : ℝ ↦ J t + (τ - t) • A.comp (J t)) (A.comp (J t)) t := by
      simpa using (((hasDerivAt_id t).sub_const t).smul_const (A.comp (J t))).const_add (J t)
    convert this using 1
    funext τ
    simp [P, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp]
  have hPt : P t = J t := by simp [P]
  have h₁ := (hdet (P t)).hasFDerivAt.comp_hasDerivAt t hP
  have h₂ : HasDerivAt (fun τ ↦ LinearMap.det (P τ : E →ₗ[ℝ] E))
      (LinearMap.trace ℝ E A * LinearMap.det (J t : E →ₗ[ℝ] E)) t := by
    have h := ((hasDerivAt_det_id_add_smul_zero A).comp_of_eq t ((hasDerivAt_id t).sub_const t)
      (by simp)).mul_const (LinearMap.det (J t : E →ₗ[ℝ] E))
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
  have hlog (τ : ℝ) : HasDerivAt (fun τ ↦ Real.log (f τ)) (c τ) τ := by
    have := (hf τ).log (hpos τ).ne'
    rwa [mul_div_cancel_right₀ _ (hpos τ).ne'] at this
  have := (lipschitzWith_of_nnNorm_deriv_le (C := C) (fun τ ↦ (hlog τ).differentiableAt)
    fun τ ↦ by
      rw [(hlog τ).deriv, ← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs]
      exact hc τ).dist_le_mul t s
  rwa [Real.dist_eq, Real.dist_eq] at this
