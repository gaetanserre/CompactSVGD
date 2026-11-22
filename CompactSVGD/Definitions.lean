/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# The definitions of the project

This file gathers every definition of the project outside `CompactSVGD/Paper.lean`, so that they
can be checked by hand in one place: all the other files only contain lemmas. To trust the results
of `CompactSVGD/Paper.lean`, one only needs to trust Mathlib, this file, and the definitions and
statements of `CompactSVGD/Paper.lean`.

The first definitions are general; their API is in `CompactSVGD/ForMathlib/`. The last ones are the
vector fields of a feature map `Φ : ℝᵈ → H₀`, for the kernel `k(x, y) = ⟪Φ x, Φ y⟫` of SVGD, and
their trajectories; their lemmas are in `CompactSVGD/FeatureMap/`.

## Main definitions

* `divergence 𝕜 f x`: the divergence of a vector field `f : E → E`, the trace of its derivative.
* `ContinuousLinearMap.traceCLM 𝕜 E`: the trace of continuous endomorphisms of a
  finite-dimensional space, as a continuous linear functional.
* `ODE.globalSolution v t₀ x`: a solution on `ℝ` of `α' t = v t (α t)` with `α t₀ = x`.
* `SVGD.pairing h`: the map `u ↦ (⟪hᵢ, u⟫)ᵢ` from `H₀` to `ℝᵈ`, for `h ∈ 𝓗[d, H₀]`.
* `SVGD.toVectorField Φ h`: the vector field `y ↦ (⟪hᵢ, Φ y⟫)ᵢ` of `h ∈ 𝓗[d, H₀]`.
* `SVGD.trajectory Φ m s x`: the trajectory through `x` at time `s` of the time-dependent vector
  field of a curve `m` in `𝓗[d, H₀]`.

## Notation

* `𝓗[d, H₀]`: the product space `PiLp 2 fun _ : Fin d ↦ H₀`, scoped in the `SVGD` namespace.
-/

@[expose] public section

noncomputable section

/-! ### The divergence of a vector field -/

section Divergence

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- The divergence of a vector field `f : E → E` at `x`, i.e. the trace of `fderiv 𝕜 f x`.

It is `0` when `f` is not differentiable at `x`, and when `E` is not finite-dimensional. -/
def divergence (f : E → E) (x : E) : 𝕜 :=
  LinearMap.trace 𝕜 E (fderiv 𝕜 f x)

end Divergence

/-! ### The trace as a continuous linear functional -/

namespace ContinuousLinearMap

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E]

/-- The trace of continuous endomorphisms of a finite-dimensional space, as a continuous linear
functional. Continuity is automatic, since `E →L[𝕜] E` is finite-dimensional. -/
def traceCLM : (E →L[𝕜] E) →L[𝕜] 𝕜 :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace 𝕜 E).comp (coeLM 𝕜))

end ContinuousLinearMap

/-! ### Global solutions of ordinary differential equations -/

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- An integral curve of `v` on `ℝ` with `α t₀ = x`, or the constant curve `x` if there is none.
For a field continuous in time and Lipschitz in space, it is the unique solution
(`ODE.exists_isIntegralCurve_of_lipschitzWith`, `IsIntegralCurve.eq_globalSolution`). -/
def globalSolution (v : ℝ → E → E) (t₀ : ℝ) (x : E) : ℝ → E :=
  if h : ∃ α : ℝ → E, α t₀ = x ∧ IsIntegralCurve α v then h.choose else fun _ ↦ x

end ODE

/-! ### The vector fields of a feature map -/

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- The product space `𝓗[d, H₀] = H₀ᵈ`, a Hilbert sum. -/
scoped notation "𝓗[" d ", " H₀ "]" => PiLp 2 fun _ : Fin d ↦ H₀

/-- The pairing `u ↦ (⟪hᵢ, u⟫)ᵢ` between `H₀` and `EuclideanSpace ℝ (Fin d)` defined by
`h ∈ 𝓗[d, H₀]`. -/
def pairing (h : 𝓗[d, H₀]) : H₀ →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (h i))

/-- The vector field `y ↦ (⟪hᵢ, Φ y⟫)ᵢ` of `h ∈ 𝓗[d, H₀]`, for a map `Φ : ℝᵈ → H₀`. When `H₀` is
the RKHS of the kernel `k(x, y) = ⟪Φ x, Φ y⟫`, this is the evaluation of `h` at `y`. -/
def toVectorField (Φ : EuclideanSpace ℝ (Fin d) → H₀) (h : 𝓗[d, H₀])
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  pairing h (Φ y)

/-- The trajectory through `x` at time `s` of the time-dependent vector field
`y ↦ toVectorField Φ (m t) y`, i.e. its global solution `ODE.globalSolution`. -/
def trajectory (Φ : EuclideanSpace ℝ (Fin d) → H₀) (m : ℝ → 𝓗[d, H₀]) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ → EuclideanSpace ℝ (Fin d) :=
  ODE.globalSolution (fun t ↦ toVectorField Φ (m t)) s x

end SVGD
