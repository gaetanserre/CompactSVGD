/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Analysis.InnerProductSpace.Trace

import CompactSVGD.ForMathlib.Topology.Algebra.Module.Trace

/-!
# The norm of the trace on an inner product space

On a finite-dimensional real inner product space `E`, the trace of a continuous endomorphism `L`
is the sum of the `⟪bᵢ, L bᵢ⟫` over an orthonormal basis `b`. Each term is at most `‖L‖`, so that
`|tr L| ≤ dim E ‖L‖`.

## Main statements

* `ContinuousLinearMap.norm_traceCLM_le`: `‖trace‖ ≤ dim E`.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The trace is bounded by the dimension: `|tr L| ≤ dim E ‖L‖`. -/
theorem norm_traceCLM_le : ‖traceCLM ℝ E‖ ≤ Module.finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ E
  refine opNorm_le_bound _ (Nat.cast_nonneg _) fun L ↦ ?_
  rw [traceCLM_apply, LinearMap.trace_eq_sum_inner _ b]
  calc ‖∑ i, ⟪b i, (L : E →ₗ[ℝ] E) (b i)⟫‖ ≤ ∑ i, ‖⟪b i, L (b i)⟫‖ := norm_sum_le _ _
    _ ≤ ∑ _i, ‖L‖ := Finset.sum_le_sum fun i _ ↦ (norm_inner_le_norm _ _).trans (by
        simpa [b.orthonormal.1 i] using L.le_opNorm (b i))
    _ = Module.finrank ℝ E * ‖L‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end ContinuousLinearMap
