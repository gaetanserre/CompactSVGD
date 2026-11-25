/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Functions continuous on a compact set carrying the measure

A function continuous on a compact set `K` is integrable for every measure carried by `K` that is
finite on compact sets.
-/

@[expose] public section

open MeasureTheory

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T2Space X] [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X}
  {f : X → E}

theorem ContinuousOn.integrable_of_ae_mem (hK : IsCompact K) (hf : ContinuousOn f K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) : Integrable f μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem hμ]
  exact hf.integrableOn_compact hK
