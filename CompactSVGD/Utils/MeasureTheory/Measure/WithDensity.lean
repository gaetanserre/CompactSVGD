/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measures with a density on a set

A measure with a density with respect to the restriction of a measure to a measurable set is
carried by this set.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- A measure with a density with respect to `μ.restrict s` is carried by `s`. -/
theorem ae_withDensity_restrict_mem (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∀ᵐ x ∂(μ.restrict s).withDensity f, x ∈ s :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hs)

end MeasureTheory
