/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Analysis.ODE.Global
public import TauCeti.Analysis.ODE.Nonautonomous

/-!
# The flow maps of a globally Lipschitz vector field

Let `E` be a real Banach space and let `v : ℝ → E → E` be a time-dependent vector field,
continuous in time and `K`-Lipschitz in space uniformly in time. Let `α x` be the solution of
`α' t = v t (α t)` with `α x s = x`. For every time `t`:

* the flow map `α · t` is a homeomorphism of `E` (`ODE.isHomeomorph_flow`), whose inverse maps
  `y` to the value at time `s` of the solution through `y` at time `t`
  (`ODE.flow_nonautonomousSolution`, `ODE.nonautonomousSolution_flow`);
* if `v` vanishes on the frontier of a closed set `Ω`, the flow map maps `Ω` onto `Ω`
  (`ODE.image_flow_eq`).

The solutions through arbitrary initial conditions are the global solutions
`ODE.nonautonomousSolution`.
-/

@[expose] public section

open Set

open scoped NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : ℝ → E → E} {K : ℝ≥0} {α : E → ℝ → E} {s : ℝ}

variable (hvc : ∀ y, Continuous (v · y)) (hvK : ∀ t, LipschitzWith K (v t))
  (hα : ∀ x t, HasDerivAt (α x) (v t (α x t)) t) (hα₀ : ∀ x, α x s = x)
include hvc hvK hα hα₀

/-- The trajectories of the flow are the global solutions `ODE.nonautonomousSolution`. -/
theorem flow_eq_nonautonomousSolution (x : E) :
    α x = ODE.nonautonomousSolution v hvc hvK s x := by
  have := ODE.eq_nonautonomousSolution v hvc hvK (hα x) s
  rwa [hα₀] at this

/-- The flow map at time `t` maps the value at time `s` of the solution through `y` at time `t`
to `y`. -/
theorem flow_nonautonomousSolution (t : ℝ) (y : E) :
    α (ODE.nonautonomousSolution v hvc hvK t y s) t = y := by
  rw [flow_eq_nonautonomousSolution hvc hvK hα hα₀, ODE.nonautonomousSolution_trans,
    ODE.nonautonomousSolution_self]

/-- Following the flow from `s` to `t` and then back from `t` to `s` is the identity. -/
theorem nonautonomousSolution_flow (x : E) (t : ℝ) :
    ODE.nonautonomousSolution v hvc hvK t (α x t) s = x := by
  rw [flow_eq_nonautonomousSolution hvc hvK hα hα₀, ODE.nonautonomousSolution_trans,
    ODE.nonautonomousSolution_self]

/-- **The flow maps are homeomorphisms.** The inverse of `α · t` maps `y` to the value at time `s`
of the solution through `y` at time `t` (`ODE.nonautonomousSolution_flow`,
`ODE.flow_nonautonomousSolution`). -/
theorem isHomeomorph_flow (t : ℝ) : IsHomeomorph (α · t) := by
  have hc (a b : ℝ) : Continuous fun y ↦ ODE.nonautonomousSolution v hvc hvK a y b :=
    (ODE.continuous_nonautonomousSolution v hvc hvK).comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  have hαc : Continuous (α · t) := by
    have : (α · t) = (ODE.nonautonomousSolution v hvc hvK s · t) :=
      funext fun x ↦ by rw [flow_eq_nonautonomousSolution hvc hvK hα hα₀]
    rw [this]
    exact hc s t
  exact Homeomorph.isHomeomorph
    { toFun := (α · t)
      invFun := (ODE.nonautonomousSolution v hvc hvK t · s)
      left_inv := fun x ↦ nonautonomousSolution_flow hvc hvK hα hα₀ x t
      right_inv := fun y ↦ flow_nonautonomousSolution hvc hvK hα hα₀ t y
      continuous_toFun := hαc
      continuous_invFun := hc t s }

/-- **Invariance.** If `v` vanishes on the frontier of the closed set `Ω`, the flow maps map `Ω`
onto `Ω`. -/
theorem image_flow_eq {Ω : Set E} (hΩ : IsClosed Ω) (hv₀ : ∀ t, ∀ y ∈ frontier Ω, v t y = 0)
    (t : ℝ) : (α · t) '' Ω = Ω :=
  Subset.antisymm (image_subset_iff.2 fun x hx ↦
      mem_of_forall_frontier_eq_zero hΩ hvK hv₀ (hα x) (t₀ := s) (by rwa [hα₀]) t)
    fun y hy ↦ ⟨_, mem_of_forall_frontier_eq_zero hΩ hvK hv₀
      (ODE.hasDerivAt_nonautonomousSolution v hvc hvK t y) (t₀ := t)
      (by rwa [ODE.nonautonomousSolution_self]) s, flow_nonautonomousSolution hvc hvK hα hα₀ t y⟩

end ODE
