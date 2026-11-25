/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import TauCeti.Analysis.ODE.Nonautonomous

/-!
# Global solutions of Lipschitz ODEs

Let `v : ℝ → E → E` be a time-dependent vector field on a Banach space `E`, continuous in time and
`K`-Lipschitz in space uniformly in time. For every initial condition `(t₀, x)`, the ODE
`α' t = v t (α t)` has a unique solution on `ℝ` (an integral curve of `v`),
`ODE.integralCurveThrough v t₀ x`.

This file is the API of `ODE.integralCurveThrough`, defined in `CompactSVGD/Definitions.lean`. It
is the global solution `ODE.nonautonomousSolution` of Tau Ceti
(`ODE.integralCurveThrough_eq_nonautonomousSolution`), whose API gives the results below.

## Main statements

* `ODE.integralCurveThrough_eq_nonautonomousSolution`: the link with Tau Ceti.
* `IsIntegralCurve.eq_integralCurveThrough`: uniqueness.
* `ODE.dist_integralCurveThrough_le`: Lipschitz dependence on the initial condition.
* `ODE.integralCurveThrough_eq_of_eqOn`: the solution at time `t` only depends on the field between
  `t₀` and `t`.
-/

@[expose] public section

open Set

open scoped NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {v : ℝ → E → E}
  {K : ℝ≥0}

section Lipschitz

variable (hvc : ∀ x, Continuous (v · x)) (hv : ∀ t, LipschitzWith K (v t))
include hvc hv

/-- Global existence for a Lipschitz vector field, by Tau Ceti's `ODE.nonautonomousSolution`. -/
private theorem exists_isIntegralCurve_of_lipschitzWith (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurve α v :=
  ⟨nonautonomousSolution v hvc hv t₀ x₀, nonautonomousSolution_self v hvc hv t₀ x₀,
    isIntegralCurve_nonautonomousSolution v hvc hv t₀ x₀⟩

private theorem integralCurveThrough_spec (t₀ : ℝ) (x : E) :
    integralCurveThrough v t₀ x t₀ = x ∧ IsIntegralCurve (integralCurveThrough v t₀ x) v := by
  have h := exists_isIntegralCurve_of_lipschitzWith hvc hv t₀ x
  rw [integralCurveThrough, dite_eq_left h]
  exact h.choose_spec

/-- `ODE.integralCurveThrough` is the global solution `ODE.nonautonomousSolution` of Tau Ceti. -/
theorem integralCurveThrough_eq_nonautonomousSolution (t₀ : ℝ) (x : E) :
    integralCurveThrough v t₀ x = nonautonomousSolution v hvc hv t₀ x := by
  obtain ⟨h₀, h⟩ := integralCurveThrough_spec hvc hv t₀ x
  have := eq_nonautonomousSolution v hvc hv h t₀
  rwa [h₀] at this

theorem integralCurveThrough_self (t₀ : ℝ) (x : E) : integralCurveThrough v t₀ x t₀ = x :=
  (integralCurveThrough_spec hvc hv t₀ x).1

theorem isIntegralCurve_integralCurveThrough (t₀ : ℝ) (x : E) :
    IsIntegralCurve (integralCurveThrough v t₀ x) v :=
  (integralCurveThrough_spec hvc hv t₀ x).2

theorem continuous_integralCurveThrough (t₀ : ℝ) (x : E) :
    Continuous (integralCurveThrough v t₀ x) :=
  (isIntegralCurve_integralCurveThrough hvc hv t₀ x).continuous

/-- **Uniqueness.** An integral curve of `v` on `ℝ` is the global solution through its value at any
time `t₀`. -/
theorem _root_.IsIntegralCurve.eq_integralCurveThrough {α : ℝ → E} (hα : IsIntegralCurve α v)
    (t₀ : ℝ) : α = integralCurveThrough v t₀ (α t₀) := by
  rw [integralCurveThrough_eq_nonautonomousSolution hvc hv]
  exact eq_nonautonomousSolution v hvc hv hα t₀

/-- **The evolution law.** Following the solution from `r` to `s`, then from `s` to `t`, is
following it from `r` to `t`. -/
theorem integralCurveThrough_integralCurveThrough (r s t : ℝ) (x : E) :
    integralCurveThrough v s (integralCurveThrough v r x s) t = integralCurveThrough v r x t := by
  simp only [integralCurveThrough_eq_nonautonomousSolution hvc hv, nonautonomousSolution_trans]

/-- **Lipschitz dependence on the initial condition.** Solutions through `x` and `y` at time `t₀`
are at distance at most `e^{K |t - t₀|} ‖x - y‖` at time `t`. -/
theorem dist_integralCurveThrough_le (t₀ : ℝ) (x y : E) (t : ℝ) :
    dist (integralCurveThrough v t₀ x t) (integralCurveThrough v t₀ y t) ≤
      dist x y * Real.exp (K * |t - t₀|) := by
  simp only [integralCurveThrough_eq_nonautonomousSolution hvc hv]
  exact dist_nonautonomousSolution_le v hvc hv t₀ x y t

theorem continuous_integralCurveThrough_apply (t₀ t : ℝ) :
    Continuous fun x ↦ integralCurveThrough v t₀ x t :=
  (LipschitzWith.of_dist_le' fun x y ↦ (dist_integralCurveThrough_le hvc hv t₀ x y t).trans_eq
    (mul_comm _ _)).continuous

end Lipschitz

/-- Two fields that agree between times `t₀` and `t` have the same solutions from `t₀` to `t`. -/
theorem integralCurveThrough_eq_of_eqOn {v₁ v₂ : ℝ → E → E} {K₁ K₂ : ℝ≥0}
    (hvc₁ : ∀ x, Continuous (v₁ · x)) (hv₁ : ∀ t, LipschitzWith K₁ (v₁ t))
    (hvc₂ : ∀ x, Continuous (v₂ · x)) (hv₂ : ∀ t, LipschitzWith K₂ (v₂ t)) {t₀ t : ℝ}
    (heq : EqOn v₁ v₂ (uIcc t₀ t)) (x : E) :
    integralCurveThrough v₁ t₀ x t = integralCurveThrough v₂ t₀ x t := by
  rw [integralCurveThrough_eq_nonautonomousSolution hvc₁ hv₁,
    integralCurveThrough_eq_nonautonomousSolution hvc₂ hv₂]
  exact nonautonomousSolution_eq_of_eqOn hvc₁ hvc₂ hv₁ hv₂ heq x

end ODE
