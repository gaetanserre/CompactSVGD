/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Open and closed balls are almost everywhere equal for an additive Haar measure

In a nontrivial finite-dimensional real normed space, spheres are null sets for an additive Haar
measure (`MeasureTheory.Measure.addHaar_sphere`). Hence open and closed balls are almost everywhere
equal, and restricting the measure to either of them gives the same measure.

## Main statements

* `MeasureTheory.Measure.ball_ae_eq_closedBall`: `ball x r =ᵐ[μ] closedBall x r`.
* `MeasureTheory.Measure.restrict_ball_eq_restrict_closedBall`:
  `μ.restrict (ball x r) = μ.restrict (closedBall x r)`.
-/

@[expose] public section

open Metric Set

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem ball_ae_eq_closedBall (x : E) (r : ℝ) : ball x r =ᵐ[μ] closedBall x r :=
  ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 ball_subset_closedBall, measure_empty],
    by rw [closedBall_sdiff_ball, addHaar_sphere]⟩

theorem restrict_ball_eq_restrict_closedBall (x : E) (r : ℝ) :
    μ.restrict (ball x r) = μ.restrict (closedBall x r) :=
  restrict_congr_set (ball_ae_eq_closedBall μ x r)

end MeasureTheory.Measure
