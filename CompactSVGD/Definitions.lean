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

The first definitions are general; their API is in `CompactSVGD/ForMathlib/`. The next ones are the
vector fields of a feature map `Φ : ℝᵈ → H₀`, for the kernel `k(x, y) = ⟪Φ x, Φ y⟫` of SVGD, and
their trajectories. Their lemmas are in `CompactSVGD/FeatureMap/`.

## Main definitions

* `divergence 𝕜 f x`: the divergence of a vector field `f : E → E`, the trace of its derivative.
* `modulusOfContinuityOn f s`: the modulus of continuity of `f` on `s`.
* `ODE.integralCurveThrough v t₀ x`: a solution on `ℝ` of `α' t = v t (α t)` with `α t₀ = x`.
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
def divergence (f : E → E) (x : E) : 𝕜 := LinearMap.trace 𝕜 E (fderiv 𝕜 f x)

end Divergence

/-! ### The modulus of continuity of a function on a set -/

section ModulusOfContinuity

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]

/-- The modulus of continuity of `f` on `s`: `ω(r)` is the supremum of `dist (f x) (f y)` over the
points `x, y ∈ s` with `dist x y ≤ r`. It is `0` when there is no such pair, and when these
distances are unbounded. -/
def modulusOfContinuityOn (f : α → β) (s : Set α) (r : ℝ) : ℝ :=
  sSup {e | ∃ x ∈ s, ∃ y ∈ s, dist x y ≤ r ∧ dist (f x) (f y) = e}

end ModulusOfContinuity

/-! ### Global solutions of ordinary differential equations -/

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- An integral curve of `v` on `ℝ` with `α t₀ = x`, or the constant curve `x` if there is none.
For a field continuous in time and Lipschitz in space, it is the unique solution
(`ODE.integralCurveThrough_eq_nonautonomousSolution`). -/
def integralCurveThrough (v : ℝ → E → E) (t₀ : ℝ) (x : E) : ℝ → E :=
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
`y ↦ toVectorField Φ (m t) y`, i.e. its global solution `ODE.integralCurveThrough`. -/
def trajectory (Φ : EuclideanSpace ℝ (Fin d) → H₀) (m : ℝ → 𝓗[d, H₀]) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ → EuclideanSpace ℝ (Fin d) :=
  ODE.integralCurveThrough (fun t ↦ toVectorField Φ (m t)) s x

end SVGD
