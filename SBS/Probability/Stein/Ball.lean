/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.MeasureTheory.Integral.DivergenceTheorem.Ball
public import SBS.Probability.Stein.Class

/-!
# The Stein class on a ball

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`. On a
ball `Ω = ball c R` or `Ω = closedBall c R`, the divergence theorem identifies the condition
defining the Stein class with the vanishing of the flux through the sphere. If `p • φ` is `C¹` at
every point of `closedBall c R`, then `φ` is in the Stein class of `p` on the ball if and only if

  `∮_{sphere c R} p φ · n dS = 0`

(`ProbabilityTheory.mem_steinClass_ball_iff`, `ProbabilityTheory.mem_steinClass_closedBall_iff`).
This is the definition of the Stein class in [Liu2016] and [Serre2025].

## Main statements

* `ProbabilityTheory.mem_steinClass_ball_iff`: on an open ball, the Stein class is the set of
  fields with zero flux through the sphere.
* `ProbabilityTheory.mem_steinClass_closedBall_iff`: the same on a closed ball.

## References

* [Q. Liu, J. Lee, M. Jordan, *A Kernelized Stein Discrepancy for Goodness-of-fit Tests*][Liu2016]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Definition A.2
-/

@[expose] public section

open MeasureTheory Metric Set

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {c : E} {R : ℝ}
  {p : E → ℝ} {φ : E → E}

/-- On an open ball, a field `φ` such that `p • φ` is `C¹` at every point of the closed ball is in
the Stein class of `p` if and only if the flux of `p • φ` through the sphere vanishes. -/
theorem mem_steinClass_ball_iff (hR : 0 ≤ R)
    (hf : ∀ x ∈ closedBall c R, ContDiffAt ℝ 1 (p • φ) x) :
    φ ∈ steinClass (μ.restrict (ball c R)) p ↔ ballFlux μ c R (p • φ) = 0 := by
  have hi : IntegrableOn (divergence ℝ (p • φ)) (closedBall c R) μ :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall c R) fun x hx ↦
      ((hf x hx).continuousAt_divergence one_ne_zero).continuousWithinAt
  rw [mem_steinClass_iff, integral_divergence_eq_ballFlux μ hR hf]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦
    (hf x (ball_subset_closedBall hx)).differentiableAt one_ne_zero,
    hi.mono_set ball_subset_closedBall, h⟩⟩

/-- On a closed ball, a field `φ` such that `p • φ` is `C¹` at every point of the closed ball is
in the Stein class of `p` if and only if the flux of `p • φ` through the sphere vanishes. -/
theorem mem_steinClass_closedBall_iff [Nontrivial E] (hR : 0 ≤ R)
    (hf : ∀ x ∈ closedBall c R, ContDiffAt ℝ 1 (p • φ) x) :
    φ ∈ steinClass (μ.restrict (closedBall c R)) p ↔ ballFlux μ c R (p • φ) = 0 := by
  rw [← Measure.restrict_ball_eq_restrict_closedBall]
  exact mem_steinClass_ball_iff hR hf

end ProbabilityTheory
