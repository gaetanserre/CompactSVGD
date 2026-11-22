/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The trace of a continuous linear map

On a finite-dimensional normed space `E` over a complete nontrivially normed field `𝕜`, the trace of
endomorphisms is a continuous linear form on `E →L[𝕜] E`. This file bundles it as
`ContinuousLinearMap.trace 𝕜 E : (E →L[𝕜] E) →L[𝕜] 𝕜`.

## Main definitions

* `ContinuousLinearMap.trace 𝕜 E`: the trace of continuous linear endomorphisms of `E`, as a
  continuous linear form.
-/

@[expose] public section

noncomputable section

namespace ContinuousLinearMap

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The trace of continuous linear endomorphisms of a finite-dimensional space, as a continuous
linear form. -/
def trace : (E →L[𝕜] E) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace 𝕜 E).comp (coeLM 𝕜))

variable {𝕜 E}

@[simp]
theorem trace_apply (f : E →L[𝕜] E) : trace 𝕜 E f = LinearMap.trace 𝕜 E f :=
  rfl

end ContinuousLinearMap
