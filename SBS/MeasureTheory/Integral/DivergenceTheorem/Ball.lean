/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Analysis.Calculus.Divergence
public import SBS.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Ball

/-!
# The divergence theorem on a ball, in terms of `divergence`

Let `E` be a finite-dimensional real inner product space of dimension `n`, with an additive Haar
measure `μ`. This file restates the divergence theorem on a ball of Tau Ceti,
`TauCeti.setIntegral_ball_trace_fderiv`, with the divergence `divergence ℝ f` and with the outward
flux `ballFlux μ c R f` of `f` through the sphere of radius `R` about `c`.

The sphere `sphere c R` is parametrized by the unit sphere `S` through `θ ↦ c + R • θ`. Its
outward unit normal at `c + R • θ` is `θ`, and its surface measure is the image of
`R ^ (n - 1) • μ.toSphere`, where `μ.toSphere` is the surface measure on `S` given by polar
coordinates. So
`ballFlux μ c R f = R ^ (n - 1) * ∫ θ ∈ S, ⟪f (c + R • θ), θ⟫ ∂μ.toSphere` is the surface integral
`∮_{sphere c R} f · n dS`.

## Main definitions

* `MeasureTheory.ballFlux μ c R f`: the outward flux of `f` through `sphere c R`.

## Main statements

* `MeasureTheory.integral_divergence_eq_ballFlux`: the divergence theorem on `ball c R`.
* `MeasureTheory.integral_divergence_closedBall_eq_ballFlux`: the same on `closedBall c R`.
-/

@[expose] public section

open Metric Module

open scoped RealInnerProductSpace

noncomputable section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  (μ : Measure E)

/-- The outward flux of the vector field `f : E → E` through the sphere of radius `R` about `c`,
i.e. the surface integral `∮_{sphere c R} f · n dS`, computed in polar coordinates. -/
def ballFlux (c : E) (R : ℝ) (f : E → E) : ℝ :=
  R ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪f (c + R • (θ : E)), θ⟫ ∂μ.toSphere

variable [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] {c : E} {R : ℝ} {f : E → E}

/-- **Divergence theorem on a ball.** If `f` is `C¹` at every point of `closedBall c R`, the
integral of its divergence over `ball c R` is its outward flux through `sphere c R`. -/
theorem integral_divergence_eq_ballFlux (hR : 0 ≤ R)
    (hf : ∀ x ∈ closedBall c R, ContDiffAt ℝ 1 f x) :
    ∫ x in ball c R, divergence ℝ f x ∂μ = ballFlux μ c R f :=
  TauCeti.setIntegral_ball_trace_fderiv c hR hf

/-- **Divergence theorem on a closed ball.** If `f` is `C¹` at every point of `closedBall c R`,
the integral of its divergence over `closedBall c R` is its outward flux through `sphere c R`. -/
theorem integral_divergence_closedBall_eq_ballFlux [Nontrivial E] (hR : 0 ≤ R)
    (hf : ∀ x ∈ closedBall c R, ContDiffAt ℝ 1 f x) :
    ∫ x in closedBall c R, divergence ℝ f x ∂μ = ballFlux μ c R f := by
  rw [← Measure.restrict_ball_eq_restrict_closedBall, integral_divergence_eq_ballFlux μ hR hf]

end MeasureTheory
