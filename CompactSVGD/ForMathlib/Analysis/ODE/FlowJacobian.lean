/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import TauCeti.Topology.Algebra.Module.Trace

import CompactSVGD.ForMathlib.Analysis.Calculus.Divergence
import CompactSVGD.ForMathlib.Analysis.ODE.Global
import CompactSVGD.ForMathlib.Analysis.ODE.InitialCondition
import CompactSVGD.ForMathlib.Analysis.ODE.Liouville
import CompactSVGD.ForMathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Jacobian of a flow

Let `v : ℝ → E → E` be a time-dependent vector field on a finite-dimensional real normed space,
Lipschitz in space uniformly in time, with a jointly continuous spatial derivative `Dv`, and let
`α x` be the solution of `α' t = v t (α t)` with `α x s = x`. The flow maps are differentiable,
their derivative solves the variational equation, and their Jacobian determinant `Jₜ x` solves
`∂ₜ Jₜ x = div (v t) (α x t) * Jₜ x`. Hence `Jₜ x > 0` and `|log Jₜ x| ≤ ‖trace‖ K |t - s|`.

## Main statements

* `ODE.hasDerivAt_fderiv_flow`: the variational equation.
* `ODE.hasDerivAt_det_fderiv_flow`: **Liouville's formula** for flows.
* `ODE.det_fderiv_flow_pos`, `ODE.abs_log_det_fderiv_flow_le`: bounds on the Jacobian determinant.
-/

@[expose] public section

open Set Function

open scoped NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {K : ℝ≥0} {α : E → ℝ → E} {s : ℝ}

/-- At the initial time, the Jacobian determinant of the flow is `1`. -/
theorem det_fderiv_flow_self (hα₀ : ∀ x, α x s = x) (x : E) : (fderiv ℝ (α · s) x).det = 1 := by
  have : (α · s) = id := funext hα₀
  rw [this, fderiv_id]
  exact LinearMap.det_id

variable [FiniteDimensional ℝ E]

/-- The bound `|div (v t)| ≤ ‖trace‖ K`, with an `ℝ≥0` constant. -/
private theorem abs_divergence_le (hvK : ∀ t, LipschitzWith K (v t)) (t : ℝ) (y : E) :
    |divergence ℝ (v t) y| ≤ (‖TauCeti.traceCLM ℝ E‖₊ * K : ℝ≥0) := by
  rw [← Real.norm_eq_abs, NNReal.coe_mul, coe_nnNorm]
  exact norm_divergence_le_of_lipschitz (hvK t) y

variable (hv : ∀ t y, HasFDerivAt (v t) (Dv t y) y) (hDv : Continuous (uncurry Dv))
  (hvK : ∀ t, LipschitzWith K (v t)) (hα : ∀ x, IsIntegralCurve (α x) v)
  (hα₀ : ∀ x, α x s = x)
include hv hDv hvK hα hα₀

/-- The derivative of the flow at `x` is the solution of the variational equation along the
trajectory of `x`. -/
private theorem exists_hasFDerivAt_flow (x : E) :
    ∃ J : ℝ → E →L[ℝ] E, (∀ t, HasDerivAt J ((Dv t (α x t)).comp (J t)) t) ∧
      ∀ t, HasFDerivAt (α · t) (J t) x := by
  have hαc : Continuous (α x) := continuous_iff_continuousAt.2 fun t ↦ (hα x t).continuousAt
  have hc (A : E →L[ℝ] E) : Continuous fun t ↦ (Dv t (α x t)).comp A :=
    (hDv.comp (continuous_id.prodMk hαc)).clm_comp continuous_const
  have hL (t : ℝ) : LipschitzWith K fun A : E →L[ℝ] E ↦ (Dv t (α x t)).comp A :=
    LipschitzWith.of_dist_le_mul fun A B ↦ by
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by gcongr; exact (hv t _).le_of_lipschitz (hvK t))
  set J := integralCurveThrough (fun t A ↦ (Dv t (α x t)).comp A) s (ContinuousLinearMap.id ℝ E)
  have hJ (t : ℝ) : HasDerivAt J ((Dv t (α x t)).comp (J t)) t :=
    isIntegralCurve_integralCurveThrough hc hL s _ t
  have hJ₀ : J s = ContinuousLinearMap.id ℝ E := integralCurveThrough_self hc hL s _
  exact ⟨J, hJ, hasFDerivAt_apply_of_hasDerivAt_variational hv hDv hvK hα hα₀ hJ hJ₀⟩

/-- The flow maps are differentiable. -/
theorem differentiable_flow (t : ℝ) : Differentiable ℝ (α · t) := fun x ↦
  have ⟨_, _, hJ⟩ := exists_hasFDerivAt_flow hv hDv hvK hα hα₀ x
  (hJ t).differentiableAt

/-- The flow maps are continuous. -/
theorem continuous_flow (t : ℝ) : Continuous (α · t) :=
  (differentiable_flow hv hDv hvK hα hα₀ t).continuous

/-- **The variational equation.** The derivative of the flow solves
`∂ₜ D(α · t) x = Dv t (α x t) ∘ D(α · t) x`. -/
theorem hasDerivAt_fderiv_flow (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ fderiv ℝ (α · t) x) ((Dv t (α x t)).comp (fderiv ℝ (α · t) x)) t := by
  obtain ⟨J, hJ, hJα⟩ := exists_hasFDerivAt_flow hv hDv hvK hα hα₀ x
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

/-- The Jacobian determinant of the flow is positive. -/
theorem det_fderiv_flow_pos (x : E) (t : ℝ) : 0 < (fderiv ℝ (α · t) x).det :=
  pos_of_hasDerivAt_mul (hasDerivAt_det_fderiv_flow hv hDv hvK hα hα₀ x)
    (fun t ↦ abs_divergence_le hvK t _) (s := s)
    (by rw [det_fderiv_flow_self hα₀]; exact one_pos) t

/-- **Liouville's formula for flows**, in logarithmic form:
`∂ₜ log det D(α · t) x = div (v t) (α x t)`. -/
theorem hasDerivAt_log_det_fderiv_flow (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ Real.log (fderiv ℝ (α · t) x).det) (divergence ℝ (v t) (α x t)) t :=
  hasDerivAt_log_of_hasDerivAt_mul (hasDerivAt_det_fderiv_flow hv hDv hvK hα hα₀ x t)
    (det_fderiv_flow_pos hv hDv hvK hα hα₀ x t).ne'

/-- The logarithm of the Jacobian determinant of the flow grows at most linearly:
`|log det D(α · t) x| ≤ ‖trace‖ K |t - s|`. -/
theorem abs_log_det_fderiv_flow_le (x : E) (t : ℝ) :
    |Real.log (fderiv ℝ (α · t) x).det| ≤ ‖TauCeti.traceCLM ℝ E‖ * K * |t - s| := by
  have := abs_log_sub_log_le_of_hasDerivAt_mul (hasDerivAt_det_fderiv_flow hv hDv hvK hα hα₀ x)
    (fun t ↦ abs_divergence_le hvK t _) (s := s)
    (by rw [det_fderiv_flow_self hα₀]; exact one_pos) t
  rwa [det_fderiv_flow_self hα₀, Real.log_one, sub_zero, NNReal.coe_mul, coe_nnNorm] at this

end ODE
