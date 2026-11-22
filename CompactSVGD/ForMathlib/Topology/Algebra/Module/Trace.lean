/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions

/-!
# The trace as a continuous linear functional

On a finite-dimensional Hausdorff topological vector space `E` over a complete nontrivially normed
field `𝕜`, every linear map out of `E →L[𝕜] E` is continuous. In particular, the trace of continuous
endomorphisms is a continuous linear functional `ContinuousLinearMap.traceCLM 𝕜 E`.

This file is the API of `ContinuousLinearMap.traceCLM 𝕜 E`, defined in
`CompactSVGD/Definitions.lean`. The definition is adapted from `TauCeti.traceCLM` in the
[Tau Ceti library](https://github.com/TauCetiProject/TauCeti).
-/

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E]

@[simp]
theorem traceCLM_apply (f : E →L[𝕜] E) : traceCLM 𝕜 E f = LinearMap.trace 𝕜 E (f : E →ₗ[𝕜] E) :=
  rfl

end ContinuousLinearMap
