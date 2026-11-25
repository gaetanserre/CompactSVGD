/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Topology.Algebra.Module.Trace

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Divergence of a vector field

The divergence of a vector field `f : E → E` at `x` is the trace of its Fréchet derivative. It does
not depend on a choice of coordinates, and is `0` where `f` is not differentiable, as `fderiv` is.

This file is the API of `divergence 𝕜 f x`, defined in `CompactSVGD/Definitions.lean`.

## Main statements

* `divergence_eq_sum_basis`, `divergence_euclideanSpace`: in a basis `b`, the divergence is
  `∑ i, ∂ᵢ fᵢ`.
* `divergence_smul`: the product rule `div (c • f) = c * div f + Dc (f)`.
* `norm_divergence_le_of_lipschitz`: the divergence of a `K`-Lipschitz field is bounded by
  `‖trace‖ K`.
-/

@[expose] public section

open Module

open scoped NNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : E → E} {x : E}

theorem divergence_eq_traceCLM [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] :
    divergence 𝕜 f x = TauCeti.traceCLM 𝕜 E (fderiv 𝕜 f x) := by
  rw [TauCeti.traceCLM_apply, divergence]

theorem divergence_eq_traceCLM_comp [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] :
    divergence 𝕜 f = TauCeti.traceCLM 𝕜 E ∘ fderiv 𝕜 f :=
  funext fun _ ↦ divergence_eq_traceCLM

theorem HasFDerivAt.divergence_eq {f' : E →L[𝕜] E} (h : HasFDerivAt f f' x) :
    divergence 𝕜 f x = LinearMap.trace 𝕜 E f' := by
  rw [divergence, h.fderiv]

/-! ### Divergence in coordinates -/

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- The divergence in a basis `b`: `div f x = ∑ i, b.coord i (fderiv 𝕜 f x (b i))`. -/
theorem divergence_eq_sum_basis (b : Basis ι 𝕜 E) :
    divergence 𝕜 f x = ∑ i, b.coord i (fderiv 𝕜 f x (b i)) := by
  classical
  simp [divergence, LinearMap.trace_eq_matrix_trace 𝕜 b, Matrix.trace, LinearMap.toMatrix_apply]

/-- The divergence on `EuclideanSpace 𝕜 ι`, the usual `∑ i, ∂ᵢ fᵢ`. -/
theorem divergence_euclideanSpace {𝕜 : Type*} [RCLike 𝕜] [DecidableEq ι]
    {f : EuclideanSpace 𝕜 ι → EuclideanSpace 𝕜 ι} {x : EuclideanSpace 𝕜 ι} :
    divergence 𝕜 f x = ∑ i, fderiv 𝕜 f x (EuclideanSpace.single i 1) i := by
  simp [divergence_eq_sum_basis (EuclideanSpace.basisFun ι 𝕜).toBasis]

end Coordinates

/-! ### Algebraic operations -/

section Algebra

/-- The product rule for the divergence: `div (c • f) = c * div f + Dc (f)`. -/
theorem divergence_smul [FiniteDimensional 𝕜 E] {c : E → 𝕜} (hc : DifferentiableAt 𝕜 c x)
    (hf : DifferentiableAt 𝕜 f x) :
    divergence 𝕜 (c • f) x = c x * divergence 𝕜 f x + fderiv 𝕜 c x (f x) := by
  rw [divergence, fderiv_smul hc hf, ContinuousLinearMap.toLinearMap_add, map_add,
    ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, divergence]
  congr 1
  exact LinearMap.trace_smulRight (fderiv 𝕜 c x : E →ₗ[𝕜] 𝕜) (f x)

/-- The product rule for the divergence when `Dc = c • L` at `x`, e.g. when `L` is the logarithmic
derivative of `c`: `div (c • f) x = c x * (L (f x) + div f x)`. -/
theorem divergence_smul_of_hasFDerivAt_self_smul [FiniteDimensional 𝕜 E] {c : E → 𝕜}
    {L : StrongDual 𝕜 E} (hc : HasFDerivAt c (c x • L) x) (hf : DifferentiableAt 𝕜 f x) :
    divergence 𝕜 (c • f) x = c x * (L (f x) + divergence 𝕜 f x) := by
  rw [divergence_smul hc.differentiableAt hf, hc.fderiv, smul_apply, smul_eq_mul]
  ring

end Algebra

/-! ### Regularity -/

section Regularity

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

theorem ContDiffAt.continuousAt_divergence {n : WithTop ℕ∞} (hf : ContDiffAt 𝕜 n f x)
    (hn : n ≠ 0) : ContinuousAt (divergence 𝕜 f) x := by
  rw [divergence_eq_traceCLM_comp]
  exact (TauCeti.traceCLM 𝕜 E).continuous.continuousAt.comp (hf.continuousAt_fderiv hn)

theorem ContDiff.continuous_divergence (hf : ContDiff 𝕜 1 f) : Continuous (divergence 𝕜 f) :=
  continuous_iff_continuousAt.2 fun x ↦ (hf.contDiffAt (x := x)).continuousAt_divergence one_ne_zero

/-- The divergence of a `K`-Lipschitz vector field is bounded by `‖trace‖ * K`. -/
theorem norm_divergence_le_of_lipschitz {K : ℝ≥0} (hf : LipschitzWith K f) (x : E) :
    ‖divergence 𝕜 f x‖ ≤ ‖TauCeti.traceCLM 𝕜 E‖ * K := by
  rw [divergence_eq_traceCLM]
  exact (TauCeti.traceCLM 𝕜 E).le_opNorm_of_le (norm_fderiv_le_of_lipschitz 𝕜 hf)

end Regularity
