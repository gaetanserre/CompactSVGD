/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Trace

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

/-!
# The determinant along the line `t ↦ id + t • A`

Let `E` be a finite-dimensional normed space over a nontrivially normed field `𝕜` and let
`A : E →L[𝕜] E`. The function `t ↦ det (id + t • A)` has derivative `trace A` at `0`. This is
Jacobi's formula at the identity. For matrices, it is `Matrix.hasDerivAt_det_one_add_smul` of Tau
Ceti, and it transfers to endomorphisms through a basis. At a general time `t`, the derivative is
`D det (id + t • A) A`. These are the Jacobian determinants of the perturbations
`y ↦ y + t • v y` of the identity, whose derivative is `id + t • Dv`.

## Main statements

* `hasDerivAt_det_id_add_smul_zero`: **Jacobi's formula at the identity**.
* `fderiv_det_id_apply`: the derivative of the determinant at the identity is the trace.
-/

@[expose] public section

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- The derivative of the perturbation `y ↦ y + ε • v y` of the identity is `id + ε • Dv`. -/
theorem hasFDerivAt_add_smul {v : E → E} {ε : 𝕜} {x : E} (hv : DifferentiableAt 𝕜 v x) :
    HasFDerivAt (fun y ↦ y + ε • v y) (ContinuousLinearMap.id 𝕜 E + ε • fderiv 𝕜 v x) x :=
  (hasFDerivAt_id x).add (hv.hasFDerivAt.const_smul ε)

/-- The determinant of a continuous linear endomorphism, as a function on `E →L[𝕜] E`. -/
local notation "det" => fun B : E →L[𝕜] E ↦ LinearMap.det (B : E →ₗ[𝕜] E)

/-- The determinant is differentiable along `t ↦ id + t • A`, with derivative
`D det (id + t • A) A`. -/
theorem hasDerivAt_det_id_add_smul [CompleteSpace 𝕜] (A : E →L[𝕜] E) (t : 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ LinearMap.det ((ContinuousLinearMap.id 𝕜 E + t • A : E →L[𝕜] E) :
      E →ₗ[𝕜] E)) (fderiv 𝕜 det (ContinuousLinearMap.id 𝕜 E + t • A) A) t := by
  have hdet : Differentiable 𝕜 det :=
    (ContinuousLinearMap.contDiff_det (𝕜 := 𝕜) (E := E) (r := 1)).differentiable one_ne_zero
  have hline : HasDerivAt (fun t : 𝕜 ↦ ContinuousLinearMap.id 𝕜 E + t • A) A t := by
    simpa using ((hasDerivAt_id t).smul_const A).const_add (ContinuousLinearMap.id 𝕜 E)
  exact (hdet _).hasFDerivAt.comp_hasDerivAt t hline

variable [FiniteDimensional 𝕜 E]

/-- **Jacobi's formula at the identity.** `t ↦ det (id + t • A)` has derivative `trace A` at
`0`. -/
theorem hasDerivAt_det_id_add_smul_zero (A : E →L[𝕜] E) :
    HasDerivAt (fun t : 𝕜 ↦ LinearMap.det ((ContinuousLinearMap.id 𝕜 E + t • A : E →L[𝕜] E) :
      E →ₗ[𝕜] E)) (LinearMap.trace 𝕜 E A) 0 := by
  classical
  let b := Module.finBasis 𝕜 E
  let M := LinearMap.toMatrix b b (A : E →ₗ[𝕜] E)
  have h := Matrix.hasDerivAt_det_one_add_smul M
  have hfun : (fun t : 𝕜 ↦ LinearMap.det ((ContinuousLinearMap.id 𝕜 E + t • A : E →L[𝕜] E) :
      E →ₗ[𝕜] E)) = fun t ↦ (1 + t • M).det := by
    funext t
    rw [← LinearMap.det_toMatrix b]
    simp [M, map_add, map_smul]
  rw [hfun, LinearMap.trace_eq_matrix_trace 𝕜 b]
  exact h

/-- The derivative of the determinant at the identity is the trace. -/
theorem fderiv_det_id_apply [CompleteSpace 𝕜] (A : E →L[𝕜] E) :
    fderiv 𝕜 det (ContinuousLinearMap.id 𝕜 E) A = LinearMap.trace 𝕜 E A := by
  have h := hasDerivAt_det_id_add_smul A 0
  simp only [zero_smul, add_zero] at h
  exact h.unique (hasDerivAt_det_id_add_smul_zero A)
