/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Measure.Map

/-!
# Image of a measure on a subtype

The image by `Subtype.val` of a measure on a measurable set `s` is carried by `s`.
-/

@[expose] public section

namespace MeasureTheory

theorem ae_map_subtypeVal_mem {α : Type*} [MeasurableSpace α] {s : Set α} (hs : MeasurableSet s)
    {μ : Measure s} : ∀ᵐ x ∂μ.map Subtype.val, x ∈ s :=
  (ae_map_iff measurable_subtypeVal.aemeasurable hs).2 (ae_of_all _ fun x ↦ x.property)

end MeasureTheory
