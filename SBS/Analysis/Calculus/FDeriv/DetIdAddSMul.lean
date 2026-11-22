/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

/-!
# The determinant along the line `t ↦ id + t • A`

Let `E` be a finite-dimensional real normed space and let `A : E →L[ℝ] E`. The function
`t ↦ det (id + t • A)` is differentiable, with derivative `trace A` at `0`
(`hasDerivAt_det_id_add_smul_zero`). This is Jacobi's formula at the identity, transferred from
matrices (`Matrix.hasDerivAt_det_one_add_smul`) to endomorphisms through a basis. At a general
time `t`, the derivative is `D det (id + t • A) A` (`hasDerivAt_det_id_add_smul`), since the
determinant is smooth (`ContinuousLinearMap.contDiff_det`).

These are the derivatives of the Jacobian determinants of the perturbations `I + t v` of the
identity, along which the first variation of the Kullback–Leibler divergence is computed.
-/

@[expose] public section

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The determinant of a continuous linear endomorphism, as a function on `E →L[ℝ] E`. -/
local notation "det" => fun B : E →L[ℝ] E ↦ LinearMap.det (B : E →ₗ[ℝ] E)

/-- **Jacobi's formula at the identity.** `t ↦ det (id + t • A)` has derivative `trace A` at
`0`. -/
theorem hasDerivAt_det_id_add_smul_zero (A : E →L[ℝ] E) :
    HasDerivAt (fun t : ℝ ↦ LinearMap.det ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) :
      E →ₗ[ℝ] E)) (LinearMap.trace ℝ E A) 0 := by
  classical
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  have h := Matrix.hasDerivAt_det_one_add_smul M
  have hfun : (fun t : ℝ ↦ LinearMap.det ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) :
      E →ₗ[ℝ] E)) = fun t ↦ (1 + t • M).det := by
    funext t
    rw [← LinearMap.det_toMatrix b]
    simp [M, map_add, map_smul]
  rw [hfun, LinearMap.trace_eq_matrix_trace ℝ b]
  exact h

omit [FiniteDimensional ℝ E] in
/-- The determinant is differentiable along `t ↦ id + t • A`, with derivative
`D det (id + t • A) A`. -/
theorem hasDerivAt_det_id_add_smul (A : E →L[ℝ] E) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ LinearMap.det ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) :
      E →ₗ[ℝ] E)) (fderiv ℝ det (ContinuousLinearMap.id ℝ E + t • A) A) t := by
  have hdet : Differentiable ℝ det :=
    (ContinuousLinearMap.contDiff_det (𝕜 := ℝ) (E := E) (r := 1)).differentiable one_ne_zero
  have hline : HasDerivAt (fun t : ℝ ↦ ContinuousLinearMap.id ℝ E + t • A) A t := by
    simpa using ((hasDerivAt_id t).smul_const A).const_add (ContinuousLinearMap.id ℝ E)
  exact (hdet _).hasFDerivAt.comp_hasDerivAt t hline

/-- The derivative of the determinant at the identity is the trace. -/
theorem fderiv_det_id_apply (A : E →L[ℝ] E) :
    fderiv ℝ det (ContinuousLinearMap.id ℝ E) A = LinearMap.trace ℝ E A := by
  have h := hasDerivAt_det_id_add_smul A 0
  simp only [zero_smul, add_zero] at h
  exact h.unique (hasDerivAt_det_id_add_smul_zero A)
