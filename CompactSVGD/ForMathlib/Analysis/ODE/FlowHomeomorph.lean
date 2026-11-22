/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions

import CompactSVGD.ForMathlib.Analysis.ODE.Global
import CompactSVGD.ForMathlib.Analysis.ODE.Invariance

/-!
# The flow maps of a Lipschitz vector field

Let `v : ℝ → E → E` be continuous in time and Lipschitz in space uniformly in time, and let `α x`
be the solution of `α' t = v t (α t)` with `α x s = x`. Every flow map `α · t` is a homeomorphism
of `E`, whose inverse follows the global solutions `ODE.globalSolution` back to time `s`.
If `v` vanishes on the frontier of `Ω`, the flow maps map `Ω` onto `Ω`.

## Main statements

* `ODE.isHomeomorph_flow`: the flow maps are homeomorphisms.
* `ODE.image_flow_eq_of_forall_frontier_eq_zero`: invariance of a set whose frontier consists of
  equilibria.
-/

@[expose] public section

open Set

open scoped NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : ℝ → E → E} {K : ℝ≥0} {α : E → ℝ → E} {s : ℝ}

variable (hvc : ∀ y, Continuous (v · y)) (hvK : ∀ t, LipschitzWith K (v t))
  (hα : ∀ x, IsIntegralCurve (α x) v) (hα₀ : ∀ x, α x s = x)
include hvc hvK hα hα₀

/-- The trajectories of the flow are the global solutions `ODE.globalSolution`. -/
theorem flow_eq_globalSolution (x : E) : α x = globalSolution v s x := by
  have := (hα x).eq_globalSolution hvc hvK s
  rwa [hα₀] at this

/-- The flow map at time `t` maps the value at time `s` of the solution through `y` at time `t`
to `y`. -/
theorem flow_globalSolution (t : ℝ) (y : E) : α (globalSolution v t y s) t = y := by
  rw [flow_eq_globalSolution hvc hvK hα hα₀, globalSolution_globalSolution hvc hvK,
    globalSolution_self hvc hvK]

/-- Following the flow from `s` to `t` and then back from `t` to `s` is the identity. -/
theorem globalSolution_flow (x : E) (t : ℝ) : globalSolution v t (α x t) s = x := by
  rw [flow_eq_globalSolution hvc hvK hα hα₀, globalSolution_globalSolution hvc hvK,
    globalSolution_self hvc hvK]

/-- **The flow maps are homeomorphisms.** The inverse of `α · t` maps `y` to the value at time `s`
of the solution through `y` at time `t` (`ODE.globalSolution_flow`, `ODE.flow_globalSolution`). -/
theorem isHomeomorph_flow (t : ℝ) : IsHomeomorph (α · t) := by
  have hαc : Continuous (α · t) := by
    have : (α · t) = (globalSolution v s · t) :=
      funext fun x ↦ by rw [flow_eq_globalSolution hvc hvK hα hα₀]
    rw [this]
    exact continuous_globalSolution_apply hvc hvK s t
  exact Homeomorph.isHomeomorph
    { toFun := (α · t)
      invFun := (globalSolution v t · s)
      left_inv := fun x ↦ globalSolution_flow hvc hvK hα hα₀ x t
      right_inv := fun y ↦ flow_globalSolution hvc hvK hα hα₀ t y
      continuous_toFun := hαc
      continuous_invFun := continuous_globalSolution_apply hvc hvK t s }

/-- **Invariance.** If `v` vanishes on the frontier of `Ω`, the flow maps map `Ω` onto `Ω`. -/
theorem image_flow_eq_of_forall_frontier_eq_zero {Ω : Set E}
    (hv₀ : ∀ t, ∀ y ∈ frontier Ω, v t y = 0) (t : ℝ) : (α · t) '' Ω = Ω :=
  Subset.antisymm (image_subset_iff.2 fun x hx ↦
      mem_of_forall_frontier_eq_zero hvK hv₀ (hα x) (t₀ := s) (by rwa [hα₀]) t)
    fun y hy ↦ ⟨_, mem_of_forall_frontier_eq_zero hvK hv₀
      (isIntegralCurve_globalSolution hvc hvK t y) (t₀ := t)
      (by rwa [globalSolution_self hvc hvK]) s, flow_globalSolution hvc hvK hα hα₀ t y⟩

end ODE
