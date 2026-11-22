/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Module.Determinant

import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Measurability of the Jacobian determinant

On a finite-dimensional space over a complete field, the Jacobian determinant `x ↦ det (Df x)` of
any map `f : E → E` is measurable, as the composition of the continuous determinant with the
measurable derivative. The proof is adapted from the
[Tau Ceti library](https://github.com/TauCetiProject/TauCeti).
-/

@[expose] public section

theorem measurable_det_fderiv (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [FiniteDimensional 𝕜 E] (f : E → E) :
    Measurable fun x ↦ (fderiv 𝕜 f x).det := by
  have := FiniteDimensional.completeSpace 𝕜 E
  borelize (E →L[𝕜] E)
  exact ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv 𝕜 f)
