/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Analysis.Calculus.Divergence
public import SBS.Analysis.ODE.InitialCondition
public import SBS.Analysis.ODE.Liouville
public import TauCeti.Analysis.ODE.Nonautonomous

/-!
# The Jacobian of a flow

Let `E` be a finite-dimensional real normed space and let `v : ℝ → E → E` be a time-dependent
vector field, `K`-Lipschitz in space uniformly in time, and differentiable in space with a jointly
continuous derivative `Dv`. Let `α x` be the solution of `α' t = v t (α t)` with `α x s = x`.

For every time `t`, the flow map `α · t` is differentiable (`ODE.differentiable_flow`), and its
derivative `D(α · t) x` solves the variational equation `∂ₜ D(α · t) x = Dv t (α x t) ∘ D(α · t) x`
(`ODE.hasDerivAt_fderiv_flow`). Hence, by Liouville's formula, the Jacobian determinant
`Jₜ x = det D(α · t) x`

* solves `∂ₜ Jₜ x = div (v t) (α x t) * Jₜ x` (`ODE.hasDerivAt_det_fderiv_flow`);
* is positive (`ODE.det_fderiv_flow_pos`), with `∂ₜ log Jₜ x = div (v t) (α x t)`
  (`ODE.hasDerivAt_log_det_fderiv_flow`);
* satisfies `|log Jₜ x| ≤ ‖trace‖ K |t - s|` (`ODE.abs_log_det_fderiv_flow_le`).

The derivative of the flow is the global solution of the variational equation, a linear equation
whose coefficients `Dv t (α x t)` are continuous in time and bounded by `K`
(`ODE.nonautonomousSolution`).

## Main statements

* `ODE.differentiable_flow`: the flow maps are differentiable.
* `ODE.hasDerivAt_fderiv_flow`: the variational equation.
* `ODE.hasDerivAt_det_fderiv_flow`, `ODE.hasDerivAt_log_det_fderiv_flow`: Liouville's formula for
  flows.
* `ODE.det_fderiv_flow_pos`, `ODE.abs_log_det_fderiv_flow_le`: bounds on the Jacobian determinant.
-/

@[expose] public section

open Set Function

open scoped NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {K : ℝ≥0} {α : E → ℝ → E} {s : ℝ}

variable (hv : ∀ t y, HasFDerivAt (v t) (Dv t y) y) (hDv : Continuous (uncurry Dv))
  (hvK : ∀ t, LipschitzWith K (v t)) (hα : ∀ x t, HasDerivAt (α x) (v t (α x t)) t)
  (hα₀ : ∀ x, α x s = x)
include hv hDv hvK hα hα₀

/-- The derivative of the flow at `x` is the solution of the variational equation along the
trajectory of `x`. -/
private theorem exists_hasFDerivAt_flow (x : E) :
    ∃ J : ℝ → E →L[ℝ] E, (∀ t, HasDerivAt J ((Dv t (α x t)).comp (J t)) t) ∧
      J s = ContinuousLinearMap.id ℝ E ∧ ∀ t, HasFDerivAt (α · t) (J t) x := by
  have hαc : Continuous (α x) := continuous_iff_continuousAt.2 fun t ↦ (hα x t).continuousAt
  have hc (A : E →L[ℝ] E) : Continuous fun t ↦ (Dv t (α x t)).comp A :=
    (hDv.comp (continuous_id.prodMk hαc)).clm_comp continuous_const
  have hL (t : ℝ) : LipschitzWith K fun A : E →L[ℝ] E ↦ (Dv t (α x t)).comp A :=
    LipschitzWith.of_dist_le_mul fun A B ↦ by
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by gcongr; exact (hv t _).le_of_lipschitz (hvK t))
  set J := ODE.nonautonomousSolution (fun t A ↦ (Dv t (α x t)).comp A) hc hL s
    (ContinuousLinearMap.id ℝ E)
  have hJ (t : ℝ) : HasDerivAt J ((Dv t (α x t)).comp (J t)) t :=
    ODE.hasDerivAt_nonautonomousSolution _ hc hL s _ t
  have hJ₀ : J s = ContinuousLinearMap.id ℝ E := ODE.nonautonomousSolution_self _ hc hL s _
  exact ⟨J, hJ, hJ₀, hasFDerivAt_apply_of_hasDerivAt_variational hv hDv hvK hα hα₀ hJ hJ₀⟩

/-- The flow maps are differentiable. -/
theorem differentiable_flow (t : ℝ) : Differentiable ℝ (α · t) := fun x ↦
  have ⟨_, _, _, hJ⟩ := exists_hasFDerivAt_flow hv hDv hvK hα hα₀ x
  (hJ t).differentiableAt

/-- The flow maps are continuous. -/
theorem continuous_flow (t : ℝ) : Continuous (α · t) :=
  (differentiable_flow hv hDv hvK hα hα₀ t).continuous

/-- **The variational equation.** The derivative of the flow solves
`∂ₜ D(α · t) x = Dv t (α x t) ∘ D(α · t) x`. -/
theorem hasDerivAt_fderiv_flow (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ fderiv ℝ (α · t) x) ((Dv t (α x t)).comp (fderiv ℝ (α · t) x)) t := by
  obtain ⟨J, hJ, -, hJα⟩ := exists_hasFDerivAt_flow hv hDv hvK hα hα₀ x
  have : (fun t ↦ fderiv ℝ (α · t) x) = J := funext fun t ↦ (hJα t).fderiv
  rw [this, (hJα t).fderiv]
  exact hJ t

/-- **Liouville's formula for flows.** The Jacobian determinant of the flow solves
`∂ₜ det D(α · t) x = div (v t) (α x t) * det D(α · t) x`. -/
theorem hasDerivAt_det_fderiv_flow (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ (fderiv ℝ (α · t) x).det)
      (divergence ℝ (v t) (α x t) * (fderiv ℝ (α · t) x).det) t := by
  rw [(hv t _).divergence_eq]
  exact hasDerivAt_det_of_hasDerivAt_comp (hasDerivAt_fderiv_flow hv hDv hvK hα hα₀ x t)

omit hv hDv hα hα₀ in
/-- The bound `|div (v t)| ≤ ‖trace‖ K`, with an `ℝ≥0` constant. -/
private theorem abs_divergence_le (t : ℝ) (y : E) :
    |divergence ℝ (v t) y| ≤ (‖ContinuousLinearMap.trace ℝ E‖₊ * K : ℝ≥0) := by
  rw [← Real.norm_eq_abs, NNReal.coe_mul, coe_nnNorm]
  exact norm_divergence_le_of_lipschitz (hvK t) y

omit [FiniteDimensional ℝ E] hv hDv hvK hα in
/-- At the initial time, the Jacobian determinant of the flow is `1`. -/
theorem det_fderiv_flow_self (x : E) : (fderiv ℝ (α · s) x).det = 1 := by
  have : (α · s) = id := funext hα₀
  rw [this, fderiv_id]
  exact LinearMap.det_id

/-- The Jacobian determinant of the flow is positive. -/
theorem det_fderiv_flow_pos (x : E) (t : ℝ) : 0 < (fderiv ℝ (α · t) x).det :=
  pos_of_hasDerivAt_mul (hasDerivAt_det_fderiv_flow hv hDv hvK hα hα₀ x)
    (fun t ↦ abs_divergence_le hvK t _) (s := s)
    (by rw [det_fderiv_flow_self hα₀]; exact one_pos) t

/-- **Liouville's formula for flows**, in logarithmic form:
`∂ₜ log det D(α · t) x = div (v t) (α x t)`. -/
theorem hasDerivAt_log_det_fderiv_flow (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ Real.log (fderiv ℝ (α · t) x).det) (divergence ℝ (v t) (α x t)) t := by
  have hpos := det_fderiv_flow_pos hv hDv hvK hα hα₀ x t
  have := (hasDerivAt_det_fderiv_flow hv hDv hvK hα hα₀ x t).log hpos.ne'
  rwa [mul_div_cancel_right₀ _ hpos.ne'] at this

/-- The logarithm of the Jacobian determinant of the flow grows at most linearly:
`|log det D(α · t) x| ≤ ‖trace‖ K |t - s|`. -/
theorem abs_log_det_fderiv_flow_le (x : E) (t : ℝ) :
    |Real.log (fderiv ℝ (α · t) x).det| ≤ ‖ContinuousLinearMap.trace ℝ E‖ * K * |t - s| := by
  have := abs_log_sub_log_le_of_hasDerivAt_mul (hasDerivAt_det_fderiv_flow hv hDv hvK hα hα₀ x)
    (fun t ↦ abs_divergence_le hvK t _) (s := s)
    (by rw [det_fderiv_flow_self hα₀]; exact one_pos) t
  rwa [det_fderiv_flow_self hα₀, Real.log_one, sub_zero, NNReal.coe_mul, coe_nnNorm] at this

end ODE
