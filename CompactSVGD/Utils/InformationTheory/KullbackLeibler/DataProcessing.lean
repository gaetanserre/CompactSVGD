/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

import TauCeti.InformationTheory.KullbackLeibler.Basic

/-!
# Transport of the Kullback–Leibler divergence by a measurable equivalence

A measurable equivalence preserves the Kullback–Leibler divergence
(`MeasureTheory.Measure.klDiv_map_measurableEquiv` of Tau Ceti). Thus, transporting the first
argument by `e` amounts to transporting the second one backwards.

## Main statements

* `MeasurableEquiv.klDiv_map_left`: `KL(e#μ ‖ ν) = KL(μ ‖ e⁻¹#ν)` for a measurable equivalence `e`.
-/

@[expose] public section

open MeasureTheory InformationTheory

/-- Transporting the first argument of the Kullback–Leibler divergence by a measurable equivalence
amounts to transporting the second one backwards. -/
theorem MeasurableEquiv.klDiv_map_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure β} [IsFiniteMeasure ν] :
    klDiv (μ.map e) ν = klDiv μ (ν.map e.symm) := by
  rw [← Measure.klDiv_map_measurableEquiv μ (ν.map e.symm) e, MeasurableEquiv.map_map_symm]
