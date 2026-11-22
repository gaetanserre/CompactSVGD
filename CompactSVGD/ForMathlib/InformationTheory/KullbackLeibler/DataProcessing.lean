/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Invariance of the Kullback–Leibler divergence under measurable embeddings

By the data processing inequality `klDiv_map_le`, a measurable map does not increase the
Kullback–Leibler divergence between finite measures. A measurable embedding has a measurable left
inverse, so it preserves the divergence.

## Main statements

* `MeasurableEmbedding.klDiv_map`: `KL(f#μ ‖ f#ν) = KL(μ ‖ ν)` for a measurable embedding `f`.
* `MeasurableEquiv.klDiv_map_left`: `KL(e#μ ‖ ν) = KL(μ ‖ e⁻¹#ν)` for a measurable equivalence `e`.
-/

@[expose] public section

open MeasureTheory InformationTheory

theorem MeasurableEmbedding.klDiv_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν hf.measurable) ?_
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [Measure.eq_zero_of_isEmpty μ, Measure.eq_zero_of_isEmpty ν]
  -- A measurable left inverse `g` of `f` maps `f#μ` back to `μ`.
  obtain ⟨g, hg, hgf⟩ := hf.exists_measurable_extend measurable_id fun _ ↦ hα
  have hmap (ρ : Measure α) : (ρ.map f).map g = ρ := by
    rw [Measure.map_map hg hf.measurable, hgf, Measure.map_id]
  calc klDiv μ ν = klDiv ((μ.map f).map g) ((ν.map f).map g) := by rw [hmap, hmap]
    _ ≤ klDiv (μ.map f) (ν.map f) := klDiv_map_le _ _ hg

/-- Transporting the first argument of the Kullback–Leibler divergence by a measurable equivalence
amounts to transporting the second one backwards. -/
theorem MeasurableEquiv.klDiv_map_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure β} [IsFiniteMeasure ν] :
    klDiv (μ.map e) ν = klDiv μ (ν.map e.symm) := by
  rw [← e.measurableEmbedding.klDiv_map μ (ν.map e.symm), MeasurableEquiv.map_map_symm]
