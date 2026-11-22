/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import CompactSVGD.FeatureMap.VectorField
import CompactSVGD.ForMathlib.Analysis.ODE.FlowHomeomorph
import CompactSVGD.ForMathlib.Analysis.ODE.Global
import CompactSVGD.ForMathlib.Analysis.ODE.Invariance
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Flow
import CompactSVGD.ForMathlib.MeasureTheory.Integral.Map

/-!
# Trajectories of the vector field of a curve

Let `m : ℝ → 𝓗[d, H₀]` be a continuous curve bounded by `B`, and let `Φ : ℝᵈ → H₀` be `K`-Lipschitz.
Each `m t` defines the vector field `toVectorField Φ (m t)`, which is `B K`-Lipschitz in space, and
`trajectory Φ m s x` is its global solution through `x` at time `s`
(`CompactSVGD/Definitions.lean`). This file proves the properties of these trajectories: they
form a flow of homeomorphisms, they depend continuously on the initial point and on the curve, they
stay in a set `Ω` when `Φ` vanishes on its frontier, and the integrals of a uniformly continuous
function along them are equicontinuous in time. It also gives the derivative of the
Kullback–Leibler divergence along the flow.

## Main statements

* `SVGD.hasDerivAt_trajectory`, `SVGD.trajectory_self`: the trajectory is a solution with value
  `x` at time `s`.
* `SVGD.isHomeomorph_trajectory`, `SVGD.exists_homeomorph_trajectory`: the flow maps are
  homeomorphisms of `ℝᵈ`, and of `Ω` when `Φ` vanishes on the frontier of `Ω`.
* `SVGD.trajectory_mem`: if `Φ` vanishes on the frontier of `Ω`, trajectories stay in `Ω`.
* `SVGD.dist_trajectory_trajectory_le_of_dist_le`: trajectories depend continuously on `m`.
* `SVGD.exists_dist_integral_map_trajectory_lt`: equicontinuity of `t ↦ ∫ F d(Tₜ)#ν`, uniformly in
  the curve.
* `SVGD.hasDerivAt_toReal_klDiv_map_trajectory`: the derivative of the Kullback–Leibler divergence
  along the flow.
-/

@[expose] public section

open Set MeasureTheory InformationTheory

open scoped NNReal ENNReal

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

variable {Φ : EuclideanSpace ℝ (Fin d) → H₀} {m m' : ℝ → 𝓗[d, H₀]} {B C K : ℝ≥0}

/-! ### Trajectories -/

section Trajectories

variable (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B) (hΦK : LipschitzWith K Φ)
include hm hmB hΦK

theorem trajectory_self (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) : trajectory Φ m s x s = x :=
  ODE.globalSolution_self (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t)) s x

theorem hasDerivAt_trajectory (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (trajectory Φ m s x) (toVectorField Φ (m t) (trajectory Φ m s x t)) t :=
  ODE.isIntegralCurve_globalSolution (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t)) s x t

theorem continuous_trajectory (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (trajectory Φ m s x) :=
  ODE.continuous_globalSolution (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t)) s x

/-- **The flow property.** -/
theorem trajectory_trajectory (s t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m t (trajectory Φ m s x t) = trajectory Φ m s x :=
  funext fun τ ↦ ODE.globalSolution_globalSolution (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t)) s t τ x

/-- Moving along a trajectory and back is the identity. -/
theorem trajectory_trajectory_apply (s t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m t (trajectory Φ m s x t) s = x := by
  rw [trajectory_trajectory hm hmB hΦK, trajectory_self hm hmB hΦK]

/-- **Speed of trajectories.** If `Φ` is bounded by `C`, trajectories are `B C`-Lipschitz in
time. -/
theorem lipschitzWith_trajectory (hΦC : ∀ y, ‖Φ y‖ ≤ C) (s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    LipschitzWith (B * C) (trajectory Φ m s x) :=
  lipschitzWith_of_nnNorm_deriv_le
    (fun t ↦ (hasDerivAt_trajectory hm hmB hΦK s x t).differentiableAt) fun t ↦ by
      rw [(hasDerivAt_trajectory hm hmB hΦK s x t).deriv, ← NNReal.coe_le_coe, coe_nnNorm]
      exact norm_toVectorField_le_of_le hΦC (hmB t) _

/-- **The flow maps are homeomorphisms.** For all times `s` and `t`, the map
`x ↦ trajectory Φ m s x t` is a homeomorphism of `ℝᵈ`. -/
theorem isHomeomorph_trajectory (s t : ℝ) : IsHomeomorph (trajectory Φ m s · t) :=
  ODE.isHomeomorph_flow (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t))
    (hasDerivAt_trajectory hm hmB hΦK s) (trajectory_self hm hmB hΦK s) t

/-- The time-`t` map of the flow is continuous. -/
theorem continuous_trajectory_apply (s t : ℝ) : Continuous fun x ↦ trajectory Φ m s x t :=
  ODE.continuous_globalSolution_apply (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t)) s t

/-- **Invariance of `Ω`.** If `Φ` vanishes on the frontier of `Ω`, trajectories that meet `Ω`
stay in `Ω` at all times. -/
theorem trajectory_mem {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΦΩ : ∀ y ∈ frontier Ω, Φ y = 0)
    {s : ℝ} {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) (t : ℝ) : trajectory Φ m s x t ∈ Ω :=
  ODE.mem_of_forall_frontier_eq_zero (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t))
    (fun _ y hy ↦ toVectorField_eq_zero_of_eq_zero (hΦΩ y hy))
    (hasDerivAt_trajectory hm hmB hΦK s x) (t₀ := s) (by rwa [trajectory_self hm hmB hΦK]) t

/-- If `Φ` vanishes on the frontier of `Ω`, the flow maps send a measure carried by `Ω` to a
measure carried by `Ω`. -/
theorem ae_map_trajectory_mem {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : MeasurableSet Ω)
    (hΦΩ : ∀ y ∈ frontier Ω, Φ y = 0) {μ : Measure (EuclideanSpace ℝ (Fin d))}
    (hμ : ∀ᵐ x ∂μ, x ∈ Ω) (s t : ℝ) : ∀ᵐ y ∂μ.map (trajectory Φ m s · t), y ∈ Ω :=
  (ae_map_iff (continuous_trajectory_apply hm hmB hΦK s t).aemeasurable hΩ).2
    (hμ.mono fun _ hx ↦ trajectory_mem hm hmB hΦK hΦΩ hx t)

/-- Two curves that agree between times `s` and `t` have the same trajectories from time `s` to
time `t`. -/
theorem trajectory_eq_of_eqOn (hm' : Continuous m') (hmB' : ∀ t, ‖m' t‖ ≤ B) {s t : ℝ}
    (hmm' : EqOn m m' (uIcc s t)) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m s x t = trajectory Φ m' s x t :=
  ODE.globalSolution_eq_of_eqOn (continuous_toVectorField_apply hm)
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t))
    (continuous_toVectorField_apply hm')
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB' t))
    (fun _ hτ ↦ congrArg (toVectorField Φ) (hmm' hτ)) x

/-- **Continuous dependence on the curve.** Let `Φ` be bounded by `C` and let `m'` be another
continuous curve bounded by `B`. If `dist (m τ) (m' τ) ≤ δ` for `τ ∈ [s, t)`, the trajectories of
`m` and `m'` through `x` at time `s` are at distance at most `gronwallBound 0 (B K) (C δ) (t - s)`
at time `t`. -/
theorem dist_trajectory_trajectory_le_of_dist_le (hΦC : ∀ y, ‖Φ y‖ ≤ C) (hm' : Continuous m')
    (hmB' : ∀ t, ‖m' t‖ ≤ B) {s t δ : ℝ} (hst : s ≤ t)
    (hδ : ∀ τ ∈ Ico s t, dist (m τ) (m' τ) ≤ δ)
    (x : EuclideanSpace ℝ (Fin d)) :
    dist (trajectory Φ m s x t) (trajectory Φ m' s x t) ≤
      gronwallBound 0 (B * K) (C * δ) (t - s) := by
  have := dist_le_of_approx_trajectories_ODE (v := fun t ↦ toVectorField Φ (m t)) (a := s)
    (b := t) (εf := 0) (εg := C * δ) (δ := 0)
    (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t))
    (continuous_trajectory hm hmB hΦK s x).continuousOn
    (fun t _ ↦ (hasDerivAt_trajectory hm hmB hΦK s x t).hasDerivWithinAt)
    (fun t _ ↦ by simp)
    (continuous_trajectory hm' hmB' hΦK s x).continuousOn
    (fun t _ ↦ (hasDerivAt_trajectory hm' hmB' hΦK s x t).hasDerivWithinAt)
    (fun τ hτ ↦ by
      have hδτ : ‖m τ - m' τ‖ ≤ δ := by
        rw [← dist_eq_norm]
        exact hδ τ hτ
      rw [dist_comm, dist_eq_norm, mul_comm]
      exact norm_toVectorField_sub_toVectorField_le.trans
        (mul_le_mul hδτ (hΦC _) (norm_nonneg _) ((norm_nonneg _).trans hδτ)))
    (by simp [trajectory_self hm hmB hΦK, trajectory_self hm' hmB' hΦK])
    t ⟨hst, le_rfl⟩
  simpa using this

/-! ### The flow maps are homeomorphisms of `Ω` -/

/-- **The flow maps are homeomorphisms of `Ω`.** If `Φ` vanishes on the frontier of `Ω`, the map
`x ↦ trajectory Φ m s x t` restricts to a homeomorphism of `Ω`, with inverse
`y ↦ trajectory Φ m t y s`. -/
theorem exists_homeomorph_trajectory {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΦΩ : ∀ y ∈ frontier Ω, Φ y = 0) (s t : ℝ) :
    ∃ T : Ω ≃ₜ Ω, ∀ x : Ω, (T x : EuclideanSpace ℝ (Fin d)) = trajectory Φ m s x t :=
  ⟨((isHomeomorph_trajectory hm hmB hΦK s t).homeomorph _).subtype fun x ↦
    ⟨fun hx ↦ trajectory_mem hm hmB hΦK hΦΩ hx t, fun hx ↦
      trajectory_trajectory_apply hm hmB hΦK s t x ▸ trajectory_mem hm hmB hΦK hΦΩ hx s⟩,
    fun _ ↦ rfl⟩

end Trajectories

/-! ### Integrals along the trajectories -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Set (EuclideanSpace ℝ (Fin d))} {ν : Measure (EuclideanSpace ℝ (Fin d))}
  [IsProbabilityMeasure ν] {F : EuclideanSpace ℝ (Fin d) → E}

/-- **Equicontinuity of integrals along trajectories.** Let `Φ` be `K`-Lipschitz, bounded by `C` and
zero on the frontier of the compact set `Ω`, and let `F` be uniformly continuous on `Ω`. For
`ε > 0`, there is `δ > 0` such that, for every continuous curve `m` bounded by `B`, the integrals of
`F` against `(Tₜ)#ν` and `(Tᵣ)#ν` are at distance less than `ε` when `|t - r| < δ`, where `Tₜ` is
the flow of `m`. -/
theorem exists_dist_integral_map_trajectory_lt (hΩ : IsCompact Ω) (hΦK : LipschitzWith K Φ)
    (hΦC : ∀ y, ‖Φ y‖ ≤ C) (hΦΩ : ∀ y ∈ frontier Ω, Φ y = 0) (hF : UniformContinuousOn F Ω)
    (hν : ∀ᵐ x ∂ν, x ∈ Ω) (B : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ m : ℝ → 𝓗[d, H₀], Continuous m → (∀ t, ‖m t‖ ≤ B) → ∀ a t r : ℝ, dist t r < δ →
      dist (∫ x, F x ∂ν.map (trajectory Φ m a · t)) (∫ x, F x ∂ν.map (trajectory Φ m a · r)) <
        ε := by
  obtain ⟨η, hη, hηF⟩ := Metric.uniformContinuousOn_iff.1 hF (ε / 2) (half_pos hε)
  refine ⟨η / (B * C + 1), by positivity, fun m hm hmB a t r htr ↦ ?_⟩
  refine (MeasureTheory.dist_integral_map_le hΩ hF.continuousOn hν
    (continuous_trajectory_apply hm hmB hΦK a t) (continuous_trajectory_apply hm hmB hΦK a r)
    (fun x hx ↦ trajectory_mem hm hmB hΦK hΦΩ hx t) (fun x hx ↦ trajectory_mem hm hmB hΦK hΦΩ hx r)
    (fun x hx y hy hxy ↦ (hηF x hx y hy hxy).le) fun x _ ↦ ?_).trans_lt (half_lt_self hε)
  -- The trajectories are `B C`-Lipschitz in time.
  calc dist (trajectory Φ m a x t) (trajectory Φ m a x r)
    _ ≤ B * C * dist t r := (lipschitzWith_trajectory hm hmB hΦK hΦC a x).dist_le_mul t r
    _ ≤ B * C * (η / (B * C + 1)) := by gcongr
    _ < η := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [mul_nonneg B.coe_nonneg C.coe_nonneg]

end Integral

/-! ### The Kullback–Leibler divergence along the trajectories -/

section KullbackLeibler

variable {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {Ω : Set (EuclideanSpace ℝ (Fin d))} {p : EuclideanSpace ℝ (Fin d) → ℝ}
  {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ] (hΩ : IsCompact Ω)
  (hp : Measurable p) (hpc : ContinuousOn p Ω) (hp₀ : ∀ x ∈ Ω, 0 < p x) (hΦ : ContDiff ℝ 1 Φ)
  (hΦK : LipschitzWith K Φ) (hΦΩ : ∀ y ∈ frontier Ω, Φ y = 0) (hm : Continuous m)
  (hmB : ∀ t, ‖m t‖ ≤ B)
  (hKL : klDiv μ ((volume.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)) ≠ ∞)
include hΩ hp hpc hp₀ hΦ hΦK hΦΩ hm hmB hKL

/-- **The dissipation of the Kullback–Leibler divergence along the flow of `m`.** Let
`π = p · λ|_Ω`, where `log p` has a continuous derivative `s` on `Ω`. The map `t ↦ KL(μₜ ‖ π)`,
where `μₜ = (Tₜ)#μ`, has derivative `-E_{μₜ}[s(vₜ) + div vₜ]` at every time, where `vₜ` is the
vector field of `m t`. -/
theorem hasDerivAt_toReal_klDiv_map_trajectory
    (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ Real.log (p y)) (s x) x) (hsc : ContinuousOn s Ω)
    (t : ℝ) :
    HasDerivAt (fun t ↦ (klDiv (μ.map (trajectory Φ m 0 · t))
        ((volume.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x))).toReal)
      (-∫ y, (s y (toVectorField Φ (m t) y) + divergence ℝ (toVectorField Φ (m t)) y)
        ∂(μ.map (trajectory Φ m 0 · t))) t :=
  InformationTheory.hasDerivAt_toReal_klDiv_map_flow hΩ hp hpc hp₀
    (continuous_toVectorField_apply hm) (fun t ↦ lipschitzWith_toVectorField_of_norm_le hΦK (hmB t))
    (fun _ y ↦ hasFDerivAt_toVectorField ((hΦ.differentiable one_ne_zero) y).hasFDerivAt)
    (continuous_uncurry_pairing_comp_fderiv hΦ hm)
    (fun _ y hy ↦ toVectorField_eq_zero_of_eq_zero (hΦΩ y hy))
    (hasDerivAt_trajectory hm hmB hΦK 0) (trajectory_self hm hmB hΦK 0) hKL hs hsc t

end KullbackLeibler

end SVGD
