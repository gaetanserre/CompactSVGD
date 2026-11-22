/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Analysis.Calculus.Divergence
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The divergence theorem on the whole space

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`. If a vector
field `f : E → E` is differentiable, integrable, and has an integrable derivative, then its
divergence is integrable and has integral `0` (`integral_divergence_eq_zero`). This is the
divergence theorem on a domain without boundary.

The proof writes the divergence in a basis `b` as `∑ i, b.coord i (fderiv ℝ f x (b i))`. Each
directional derivative `x ↦ fderiv ℝ f x v` has integral `0`
(`integral_fderiv_apply_eq_zero`), by integration by parts against the constant function `1`.

## Main statements

* `integrable_divergence`: the divergence of a field with integrable derivative is integrable.
* `integral_fderiv_apply_eq_zero`: `∫ x, fderiv ℝ f x v ∂μ = 0`.
* `integral_divergence_eq_zero`: `∫ x, divergence ℝ f x ∂μ = 0`.
* `HasCompactSupport.integral_divergence_eq_zero`: the same for a compactly supported `C¹` field.
* `setIntegral_divergence_eq_zero_of_tsupport_subset`: if moreover `tsupport f ⊆ s`, then
  `∫ x in s, divergence ℝ f x ∂μ = 0`.
-/

@[expose] public section

open MeasureTheory Module Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {μ : Measure E} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The divergence of a vector field with integrable derivative is integrable. -/
theorem integrable_divergence {f : E → E} (hf' : Integrable (fderiv ℝ f) μ) :
    Integrable (divergence ℝ f) μ :=
  (ContinuousLinearMap.trace ℝ E).integrable_comp hf'

variable [BorelSpace E] [μ.IsAddHaarMeasure]

/-- The integral of a directional derivative of an integrable function with integrable derivative
vanishes. -/
theorem integral_fderiv_apply_eq_zero {f : E → F} {v : E} (hf : Differentiable ℝ f)
    (hfi : Integrable f μ) (hf'i : Integrable (fun x ↦ fderiv ℝ f x v) μ) :
    ∫ x, fderiv ℝ f x v ∂μ = 0 := by
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := μ)
    (f := fun _ ↦ (1 : ℝ)) (f' := fun _ ↦ 0) (g := f) (g' := fderiv ℝ f) (v := v)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (by simp) (by simpa using hf'i) (by simpa using hfi)
    (fun x _ ↦ hasFDerivAt_const 1 x) (fun x _ ↦ (hf x).hasFDerivAt)
  simpa using h

/-- **Divergence theorem on the whole space.** The integral of the divergence of a differentiable
and integrable vector field with integrable derivative vanishes. -/
theorem integral_divergence_eq_zero {f : E → E} (hf : Differentiable ℝ f)
    (hfi : Integrable f μ) (hf'i : Integrable (fderiv ℝ f) μ) :
    ∫ x, divergence ℝ f x ∂μ = 0 := by
  let b := Module.finBasis ℝ E
  -- In the basis `b`, each term of the divergence is a coordinate of a directional derivative.
  have hint (i : Fin (finrank ℝ E)) : Integrable (fun x ↦ fderiv ℝ f x (b i)) μ :=
    hf'i.apply_continuousLinearMap (b i)
  have hint' (i : Fin (finrank ℝ E)) : Integrable (fun x ↦ b.coord i (fderiv ℝ f x (b i))) μ :=
    (LinearMap.toContinuousLinearMap (b.coord i)).integrable_comp (hint i)
  simp_rw [divergence_eq_sum_basis b]
  rw [integral_finsetSum _ fun i _ ↦ hint' i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have := (LinearMap.toContinuousLinearMap (b.coord i)).integral_comp_comm (hint i)
  simp only [LinearMap.coe_toContinuousLinearMap'] at this
  rw [this, integral_fderiv_apply_eq_zero hf hfi (hint i), map_zero]

/-- **Divergence theorem for compactly supported fields.** The integral of the divergence of a
compactly supported `C¹` vector field vanishes. -/
theorem HasCompactSupport.integral_divergence_eq_zero {f : E → E} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) : ∫ x, divergence ℝ f x ∂μ = 0 :=
  _root_.integral_divergence_eq_zero (hf.differentiable one_ne_zero)
    (hf.continuous.integrable_of_hasCompactSupport hc)
    ((hf.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hc.fderiv ℝ))

/-- **Divergence theorem on a set containing the support.** If `tsupport f ⊆ s`, the integral over
`s` of the divergence of a differentiable and integrable vector field with integrable derivative
vanishes. -/
theorem setIntegral_divergence_eq_zero_of_tsupport_subset {f : E → E} {s : Set E}
    (hs : tsupport f ⊆ s) (hf : Differentiable ℝ f) (hfi : Integrable f μ)
    (hf'i : Integrable (fderiv ℝ f) μ) : ∫ x in s, divergence ℝ f x ∂μ = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
    divergence_of_notMem_tsupport fun h ↦ hx (hs h)]
  exact integral_divergence_eq_zero hf hfi hf'i
