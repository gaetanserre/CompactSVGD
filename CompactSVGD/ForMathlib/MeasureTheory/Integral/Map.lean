/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import CompactSVGD.ForMathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrals against push-forward measures

The integral of a function against the push-forward of a probability measure depends continuously
on the transport map, uniformly on a compact set.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {Ω : Set X} {ν : Measure X} [IsProbabilityMeasure ν] {F : X → E}

/-- **Integrals depend continuously on the transport map.** Let `f` and `g` be continuous maps
preserving the compact set `Ω`, and let `F` be continuous on `Ω`. If `F` varies by at most `ε` on
pairs of points of `Ω` at distance less than `η`, and `f` and `g` are at distance less than `η` on
`Ω`, then the integrals of `F` against `f#ν` and `g#ν` are at distance at most `ε`. -/
theorem dist_integral_map_le (hΩ : IsCompact Ω) (hF : ContinuousOn F Ω) (hν : ∀ᵐ x ∂ν, x ∈ Ω)
    {f g : X → X} (hf : Continuous f) (hg : Continuous g) (hfΩ : MapsTo f Ω Ω)
    (hgΩ : MapsTo g Ω Ω) {ε η : ℝ} (hη : ∀ x ∈ Ω, ∀ y ∈ Ω, dist x y < η → dist (F x) (F y) ≤ ε)
    (hfg : ∀ x ∈ Ω, dist (f x) (g x) < η) :
    dist (∫ x, F x ∂ν.map f) (∫ x, F x ∂ν.map g) ≤ ε := by
  have hFf := hF.integrable_of_ae_mem hΩ
    ((ae_map_iff hf.aemeasurable hΩ.measurableSet).2 (hν.mono hfΩ))
  have hFg := hF.integrable_of_ae_mem hΩ
    ((ae_map_iff hg.aemeasurable hΩ.measurableSet).2 (hν.mono hgΩ))
  have hFf' : Integrable (fun x ↦ F (f x)) ν := hFf.comp_aemeasurable hf.aemeasurable
  have hFg' : Integrable (fun x ↦ F (g x)) ν := hFg.comp_aemeasurable hg.aemeasurable
  rw [dist_eq_norm, integral_map hf.aemeasurable hFf.aestronglyMeasurable,
    integral_map hg.aemeasurable hFg.aestronglyMeasurable, ← integral_sub hFf' hFg']
  simpa using norm_integral_le_of_norm_le_const (hν.mono fun x hx ↦ by
    simpa [dist_eq_norm] using hη _ (hfΩ hx) _ (hgΩ hx) (hfg x hx))

end MeasureTheory
