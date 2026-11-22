/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.ODE.Basic

import CompactSVGD.ForMathlib.Topology.Connected.Basic
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Invariance of a set whose frontier consists of equilibria

Let `v : ℝ → E → E` be a time-dependent vector field, Lipschitz in space. If every point of the
frontier of a set `s` is an equilibrium of `v`, then a solution of `α' t = v t (α t)` that
meets `s` stays in `s` forever, in both time directions. Indeed a solution leaving `s` must cross
its frontier, and the solution through an equilibrium is constant.

## Main statements

* `ODE.eq_const_of_forall_eq_zero`: the solution through an equilibrium is constant.
* `ODE.mem_of_forall_frontier_eq_zero`: invariance of a set whose frontier consists of
  equilibria.
* `ODE.mem_interior_of_forall_frontier_eq_zero`: invariance of its interior.
-/

@[expose] public section

open Set Metric

open scoped NNReal Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ℝ → E → E} {K : ℝ≥0}
  {α : ℝ → E} {t₀ : ℝ}

/-- **Equilibria.** A solution of `α' = v t α` through a common zero of the fields `v t` is
constant. -/
theorem eq_const_of_forall_eq_zero (hv : ∀ t, LipschitzWith K (v t))
    (hα : IsIntegralCurve α v) (h₀ : ∀ t, v t (α t₀) = 0) :
    α = fun _ ↦ α t₀ :=
  ODE_solution_unique_univ (s := fun _ ↦ univ) (t₀ := t₀) (fun t ↦ (hv t).lipschitzOnWith)
    (fun t ↦ ⟨hα t, trivial⟩)
    (fun t ↦ ⟨by simpa [h₀ t] using hasDerivAt_const t (α t₀), trivial⟩) rfl

/-- **Invariance of a set whose frontier consists of equilibria.** Let `v` be Lipschitz in space,
and let `s` be a set such that `v t y = 0` for every `y ∈ frontier s`. Then a solution of
`α' = v t α` that meets `s` at some time stays in `s` at all times. -/
theorem mem_of_forall_frontier_eq_zero {s : Set E} (hv : ∀ t, LipschitzWith K (v t))
    (h₀ : ∀ t, ∀ y ∈ frontier s, v t y = 0) (hα : IsIntegralCurve α v)
    (ht₀ : α t₀ ∈ s) (t : ℝ) : α t ∈ s := by
  have hαc : Continuous α := hα.continuous
  by_contra ht
  -- The connected set `α '' [t₀, t]` meets `s` and its complement, hence the frontier of `s`.
  obtain ⟨_, ⟨τ, -, rfl⟩, hτ⟩ :=
    (isPreconnected_uIcc.image α hαc.continuousOn).inter_frontier_nonempty
      ⟨α t₀, ⟨t₀, left_mem_uIcc, rfl⟩, ht₀⟩ ⟨α t, ⟨t, right_mem_uIcc, rfl⟩, ht⟩
  -- There, `α` passes through an equilibrium, so it is constant.
  have hconst := eq_const_of_forall_eq_zero hv hα fun t ↦ h₀ t _ hτ
  exact ht (by rwa [congrFun hconst t, ← congrFun hconst t₀])

/-- **Invariance of the interior.** Under the assumptions of `mem_of_forall_frontier_eq_zero`, a
solution that meets the interior of `s` at some time stays in the interior of `s` at all times. -/
theorem mem_interior_of_forall_frontier_eq_zero {s : Set E} (hv : ∀ t, LipschitzWith K (v t))
    (h₀ : ∀ t, ∀ y ∈ frontier s, v t y = 0) (hα : IsIntegralCurve α v)
    (ht₀ : α t₀ ∈ interior s) (t : ℝ) : α t ∈ interior s :=
  mem_of_forall_frontier_eq_zero hv (fun t y hy ↦ h₀ t y (frontier_interior_subset hy)) hα ht₀ t

end ODE
