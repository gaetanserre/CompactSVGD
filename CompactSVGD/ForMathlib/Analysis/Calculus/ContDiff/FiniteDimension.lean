/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Module.Determinant

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smoothness of the determinant

The determinant of continuous endomorphisms of a normed space over a complete field is smooth. In
finite dimension, it is a polynomial in the entries of the matrix in a basis, and these entries are
continuous linear functions of the endomorphism. In infinite dimension, it is the constant `1`.
-/

@[expose] public section

theorem ContinuousLinearMap.contDiff_det {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : WithTop ℕ∞} :
    ContDiff 𝕜 n fun f : E →L[𝕜] E ↦ f.det := by
  by_cases hE : FiniteDimensional 𝕜 E
  swap
  · simpa [LinearMap.det_eq_one_of_not_module_finite hE] using contDiff_const
  classical
  let b := Module.finBasis 𝕜 E
  -- The entries of the matrix of `f` are continuous linear functions of `f`.
  have hentry (i j) :
      ContDiff 𝕜 n fun f : E →L[𝕜] E ↦ LinearMap.toMatrix b b (f : E →ₗ[𝕜] E) i j := by
    simp only [LinearMap.toMatrix_apply]
    exact (LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp
      (ContinuousLinearMap.apply 𝕜 E (b j)).contDiff
  have hfun : (fun f : E →L[𝕜] E ↦ f.det) =
      fun f : E →L[𝕜] E ↦ ∑ σ : Equiv.Perm _,
        (Equiv.Perm.sign σ : 𝕜) * ∏ i, LinearMap.toMatrix b b (f : E →ₗ[𝕜] E) (σ i) i := by
    funext f
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    simp [Units.smul_def]
  rw [hfun]
  exact ContDiff.sum fun σ _ ↦ contDiff_const.mul (contDiff_prod fun i _ ↦ hentry _ _)
