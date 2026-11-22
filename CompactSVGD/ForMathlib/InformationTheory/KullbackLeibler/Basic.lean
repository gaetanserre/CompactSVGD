/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

import CompactSVGD.ForMathlib.MeasureTheory.Measure.WithDensity

/-!
# Measures at finite Kullback–Leibler divergence

A property that holds almost everywhere for `ν` holds almost everywhere for every measure at
finite Kullback–Leibler divergence from `ν`. In particular, such a measure is carried by any set
that carries `ν`.
-/

@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- A property that holds almost everywhere for `ν` holds almost everywhere for every measure at
finite Kullback–Leibler divergence from `ν`. -/
theorem ae_of_klDiv_ne_top (hμ : klDiv μ ν ≠ ∞) {P : α → Prop} (h : ∀ᵐ x ∂ν, P x) :
    ∀ᵐ x ∂μ, P x :=
  (klDiv_ne_top_iff.1 hμ).1.ae_le h

/-- A measure at finite Kullback–Leibler divergence from a measure carried by `Ω` is carried by
`Ω`. -/
theorem ae_mem_of_klDiv_ne_top {Ω : Set α} {f : α → ℝ≥0∞} (hΩ : MeasurableSet Ω)
    (hμ : klDiv μ ((ν.restrict Ω).withDensity f) ≠ ∞) : ∀ᵐ x ∂μ, x ∈ Ω :=
  ae_of_klDiv_ne_top hμ (ae_withDensity_restrict_mem hΩ f)

end InformationTheory
