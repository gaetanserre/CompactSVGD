/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import SBS.Analysis.ODE.FlowHomeomorph
public import SBS.Probability.SVGD.Basic

/-!
# Trajectories of the vector field of a curve in `𝓗`

Let `m : ℝ → 𝓗` be a continuous curve, bounded by `B`. Each `m t` defines a vector field
`y ↦ toVectorField Φ (m t) y` on `ℝᵈ`. If the feature map `Φ` is `K`-Lipschitz and bounded by
`C`, this time-dependent vector field is `B K`-Lipschitz in space and bounded by `B C`. Its
trajectories `SVGD.trajectory Φ m s x` (the solution equal to `x` at time `s`) are then defined on
all of `ℝ` and unique.

In SVGD, `m t` is the update direction `φ*_{μₜ}`, and the measures `μₜ` are transported along these
trajectories. The mean-field flow is a fixed point of `m ↦ (t ↦ φ*_{μₜ})`. This file studies the
trajectories for a fixed curve `m`. The estimates below are the ones needed for the fixed point.

* **Flow maps.** For all times `s` and `t`, the map `x ↦ trajectory Φ m s x t` is a homeomorphism
  of `ℝᵈ` (`SVGD.isHomeomorph_trajectory`), with inverse `y ↦ trajectory Φ m t y s`
  (`SVGD.trajectory_trajectory_apply`).
* **Invariance.** If `Φ` vanishes on the frontier of a closed set `Ω`, every vector field of `𝓗`
  vanishes there, and trajectories starting in `Ω` stay in `Ω` (`SVGD.trajectory_mem`). This is
  the condition that keeps the particles of SVGD in the domain.
* **Speed.** Trajectories are `B C`-Lipschitz in time (`SVGD.dist_trajectory_le`).
* **Stability.** Trajectories depend Lipschitz-continuously on the initial point
  (`SVGD.dist_trajectory_trajectory_le`) and continuously on the curve `m`
  (`SVGD.dist_trajectory_trajectory_le_of_dist_le`), by Grönwall's inequality.

## Main definitions

* `SVGD.trajectory Φ m s x`: the trajectory of the vector field of `m` through `x` at time `s`.

## Main statements

* `SVGD.hasDerivAt_trajectory`, `SVGD.trajectory_self`: `SVGD.trajectory Φ m s x` is a
  solution with initial condition `x` at time `s`.
* `SVGD.trajectory_eq`: it is the only one.
* `SVGD.trajectory_trajectory`: the flow property.
* `SVGD.isHomeomorph_trajectory`: the flow maps are homeomorphisms.
* `SVGD.trajectory_mem`: invariance of `Ω`.
-/

@[expose] public section

open Set Metric Filter

open scoped NNReal Topology

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

variable {Φ : EuclideanSpace ℝ (Fin d) → H₀} {m m' : ℝ → 𝓗[d, H₀]} {B C K : ℝ≥0}

/-! ### Regularity of the vector field of a curve -/

theorem lipschitzWith_toVectorField (hΦ : LipschitzWith K Φ) {h : 𝓗[d, H₀]} (hh : ‖h‖ ≤ B) :
    LipschitzWith (B * K) (toVectorField Φ h) :=
  LipschitzWith.of_dist_le_mul fun y y' ↦ by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, mul_assoc]
    exact norm_toVectorField_sub_le.trans (mul_le_mul hh (hΦ.norm_sub_le y y') (norm_nonneg _)
      B.coe_nonneg)

theorem norm_toVectorField_le_of_le (hΦ : ∀ y, ‖Φ y‖ ≤ C) {h : 𝓗[d, H₀]} (hh : ‖h‖ ≤ B)
    (y : EuclideanSpace ℝ (Fin d)) :
    ‖toVectorField Φ h y‖ ≤ B * C :=
  norm_toVectorField_le.trans (mul_le_mul hh (hΦ y) (norm_nonneg _) B.coe_nonneg)

theorem continuous_toVectorField_apply (hm : Continuous m) (y : EuclideanSpace ℝ (Fin d)) :
    Continuous fun t ↦ toVectorField Φ (m t) y := by
  have : LipschitzWith ‖Φ y‖₊ fun h : 𝓗[d, H₀] ↦ toVectorField Φ h y :=
    LipschitzWith.of_dist_le_mul fun h h' ↦ by
      rw [dist_eq_norm, dist_eq_norm, coe_nnNorm, mul_comm]
      exact norm_toVectorField_sub_toVectorField_le
  exact this.continuous.comp hm

/-- The derivative `(t, y) ↦ (pairing (m t)).comp (fderiv ℝ Φ y)` of the vector field of `m t` at
`y` is jointly continuous. -/
theorem continuous_uncurry_pairing_comp_fderiv (hΦ : ContDiff ℝ 1 Φ) (hm : Continuous m) :
    Continuous (Function.uncurry fun t y ↦ (pairing (m t)).comp (fderiv ℝ Φ y)) :=
  (continuous_pairing.comp (hm.comp continuous_fst)).clm_comp
    ((hΦ.continuous_fderiv one_ne_zero).comp continuous_snd)

/-! ### Trajectories -/

/-- The trajectory through `x` at time `s` of the time-dependent vector field
`y ↦ toVectorField Φ (m t) y`, i.e. the solution `α` of `α' t = toVectorField Φ (m t) (α t)` with
`α s = x`. It is well-defined when `m` is continuous and bounded and `Φ` is bounded and Lipschitz
(see `SVGD.hasDerivAt_trajectory`). -/
def trajectory (Φ : EuclideanSpace ℝ (Fin d) → H₀) (m : ℝ → 𝓗[d, H₀]) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ → EuclideanSpace ℝ (Fin d) :=
  @Classical.epsilon _ ⟨fun _ ↦ x⟩ fun α ↦
    α s = x ∧ ∀ t, HasDerivAt α (toVectorField Φ (m t) (α t)) t

variable (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B) (hΦK : LipschitzWith K Φ)
  (hΦC : ∀ y, ‖Φ y‖ ≤ C)

include hm hmB hΦK hΦC in
theorem trajectory_spec (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m s x s = x ∧
      ∀ t, HasDerivAt (trajectory Φ m s x) (toVectorField Φ (m t) (trajectory Φ m s x t)) t :=
  Classical.epsilon_spec (ODE.exists_forall_hasDerivAt_of_lipschitzWith (L := B * C)
    (fun t ↦ lipschitzWith_toVectorField hΦK (hmB t)) (continuous_toVectorField_apply hm)
    (fun t y ↦ (norm_toVectorField_le_of_le hΦC (hmB t) y).trans_eq (NNReal.coe_mul _ _).symm) s x)

include hm hmB hΦK hΦC

theorem trajectory_self (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) : trajectory Φ m s x s = x :=
  (trajectory_spec hm hmB hΦK hΦC s x).1

theorem hasDerivAt_trajectory (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (trajectory Φ m s x) (toVectorField Φ (m t) (trajectory Φ m s x t)) t :=
  (trajectory_spec hm hmB hΦK hΦC s x).2 t

theorem continuous_trajectory (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (trajectory Φ m s x) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_trajectory hm hmB hΦK hΦC s x t).continuousAt

/-- **Uniqueness of trajectories.** -/
theorem trajectory_eq {α : ℝ → EuclideanSpace ℝ (Fin d)} {s : ℝ}
    (hα : ∀ t, HasDerivAt α (toVectorField Φ (m t) (α t)) t) :
    trajectory Φ m s (α s) = α :=
  ODE_solution_unique_univ (s := fun _ ↦ univ) (t₀ := s)
    (fun t ↦ (lipschitzWith_toVectorField hΦK (hmB t)).lipschitzOnWith)
    (fun t ↦ ⟨hasDerivAt_trajectory hm hmB hΦK hΦC s (α s) t, trivial⟩)
    (fun t ↦ ⟨hα t, trivial⟩) (trajectory_self hm hmB hΦK hΦC s (α s))

/-- **The flow property.** -/
theorem trajectory_trajectory (s t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m t (trajectory Φ m s x t) = trajectory Φ m s x :=
  trajectory_eq hm hmB hΦK hΦC (hasDerivAt_trajectory hm hmB hΦK hΦC s x)

/-- Moving along a trajectory and back is the identity. -/
theorem trajectory_trajectory_apply (s t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m t (trajectory Φ m s x t) s = x := by
  rw [trajectory_trajectory hm hmB hΦK hΦC, trajectory_self hm hmB hΦK hΦC]

/-- **Speed of trajectories.** Trajectories are `B C`-Lipschitz in time. -/
theorem dist_trajectory_le (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) (t t' : ℝ) :
    dist (trajectory Φ m s x t) (trajectory Φ m s x t') ≤ B * C * dist t t' := by
  have := (lipschitzWith_of_nnNorm_deriv_le (C := B * C)
    (fun t ↦ (hasDerivAt_trajectory hm hmB hΦK hΦC s x t).differentiableAt) fun t ↦ by
      rw [(hasDerivAt_trajectory hm hmB hΦK hΦC s x t).deriv, ← NNReal.coe_le_coe, coe_nnNorm]
      exact norm_toVectorField_le_of_le hΦC (hmB t) _).dist_le_mul t t'
  simpa using this

/-- **Lipschitz dependence on the initial point.** For `t ≥ s`, trajectories through `x` and `x'`
at time `s` are at distance at most `e^{B K (t - s)} ‖x - x'‖` at time `t`. -/
theorem dist_trajectory_trajectory_le {s t : ℝ} (hst : s ≤ t) (x x' : EuclideanSpace ℝ (Fin d)) :
    dist (trajectory Φ m s x t) (trajectory Φ m s x' t) ≤
      dist x x' * Real.exp (B * K * (t - s)) := by
  have := dist_le_of_trajectories_ODE (v := fun t ↦ toVectorField Φ (m t)) (a := s) (b := t)
    (fun t ↦ lipschitzWith_toVectorField hΦK (hmB t))
    (continuous_trajectory hm hmB hΦK hΦC s x).continuousOn
    (fun t _ ↦ (hasDerivAt_trajectory hm hmB hΦK hΦC s x t).hasDerivWithinAt)
    (continuous_trajectory hm hmB hΦK hΦC s x').continuousOn
    (fun t _ ↦ (hasDerivAt_trajectory hm hmB hΦK hΦC s x' t).hasDerivWithinAt)
    (le_of_eq (by rw [trajectory_self hm hmB hΦK hΦC, trajectory_self hm hmB hΦK hΦC]))
    t ⟨hst, le_rfl⟩
  simpa using this

/-- **The flow maps are homeomorphisms.** For all times `s` and `t`, the map
`x ↦ trajectory Φ m s x t` is a homeomorphism of `ℝᵈ`. -/
theorem isHomeomorph_trajectory (s t : ℝ) : IsHomeomorph (trajectory Φ m s · t) :=
  ODE.isHomeomorph_flow (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField hΦK (hmB t)) (hasDerivAt_trajectory hm hmB hΦK hΦC s)
    (trajectory_self hm hmB hΦK hΦC s) t

/-- The time-`t` map of the flow is continuous. -/
theorem continuous_trajectory_apply (s t : ℝ) : Continuous fun x ↦ trajectory Φ m s x t :=
  (isHomeomorph_trajectory hm hmB hΦK hΦC s t).continuous

/-- **Invariance of `Ω`.** If `Φ` vanishes on the frontier of the closed set `Ω`, trajectories
that meet `Ω` stay in `Ω` at all times. -/
theorem trajectory_mem {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsClosed Ω)
    (hΦΩ : ∀ y ∈ frontier Ω, Φ y = 0)
    {s : ℝ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) (t : ℝ) : trajectory Φ m s x t ∈ Ω :=
  ODE.mem_of_forall_frontier_eq_zero hΩ (fun t ↦ lipschitzWith_toVectorField hΦK (hmB t))
    (fun _ y hy ↦ toVectorField_eq_zero_of_eq_zero (hΦΩ y hy))
    (hasDerivAt_trajectory hm hmB hΦK hΦC s x) (t₀ := s)
    (by rwa [trajectory_self hm hmB hΦK hΦC]) t

/-- **Continuous dependence on the curve.** Let `m'` be another continuous curve bounded by `B`.
If `‖m τ - m' τ‖ ≤ δ` for `τ ∈ [s, t]`, the trajectories of `m` and `m'` through `x` at time `s`
are at distance at most `gronwallBound 0 (B K) (C δ) (t - s)` at time `t`. -/
theorem dist_trajectory_trajectory_le_of_dist_le (hm' : Continuous m') (hmB' : ∀ t, ‖m' t‖ ≤ B)
    {s t δ : ℝ} (hst : s ≤ t) (hδ : ∀ τ ∈ Icc s t, ‖m τ - m' τ‖ ≤ δ)
    (x : EuclideanSpace ℝ (Fin d)) :
    dist (trajectory Φ m s x t) (trajectory Φ m' s x t) ≤
      gronwallBound 0 (B * K) (C * δ) (t - s) := by
  have := dist_le_of_approx_trajectories_ODE (v := fun t ↦ toVectorField Φ (m t)) (a := s)
    (b := t) (εf := 0) (εg := C * δ) (δ := 0)
    (fun t ↦ lipschitzWith_toVectorField hΦK (hmB t))
    (continuous_trajectory hm hmB hΦK hΦC s x).continuousOn
    (fun t _ ↦ (hasDerivAt_trajectory hm hmB hΦK hΦC s x t).hasDerivWithinAt)
    (fun t _ ↦ by simp)
    (continuous_trajectory hm' hmB' hΦK hΦC s x).continuousOn
    (fun t _ ↦ (hasDerivAt_trajectory hm' hmB' hΦK hΦC s x t).hasDerivWithinAt)
    (fun τ hτ ↦ by
      rw [dist_eq_norm, ← norm_neg, neg_sub, mul_comm]
      exact norm_toVectorField_sub_toVectorField_le.trans
        (mul_le_mul (hδ τ (Ico_subset_Icc_self hτ)) (hΦC _) (norm_nonneg _)
          ((norm_nonneg _).trans (hδ τ (Ico_subset_Icc_self hτ)))))
    (by simp [trajectory_self hm hmB hΦK hΦC, trajectory_self hm' hmB' hΦK hΦC])
    t ⟨hst, le_rfl⟩
  simpa using this

end SVGD
