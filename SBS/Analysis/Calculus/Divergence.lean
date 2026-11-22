/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Analysis.Normed.Module.Trace
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Divergence of a vector field

Let `E` be a normed space over a nontrivially normed field `𝕜` and let `f : E → E` be a vector
field. The *divergence* of `f` at `x` is the trace of its Fréchet derivative,
`divergence 𝕜 f x = LinearMap.trace 𝕜 E (fderiv 𝕜 f x)`.

This definition does not depend on a choice of coordinates. In a basis `b`, it is the familiar
`∑ i, ∂ᵢ fᵢ` (`divergence_eq_sum_basis`). On `ι → 𝕜`, it is the expression
`∑ i, fderiv 𝕜 f x (Pi.single i 1) i` used in the divergence theorem on boxes
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` (`divergence_pi`).

As for `fderiv`, the divergence is `0` at points where `f` is not differentiable. It is also `0`
when `E` is not finite-dimensional, as `LinearMap.trace` is.

## Main definitions

* `divergence 𝕜 f x`: the divergence of `f : E → E` at `x`.

## Main statements

* `divergence_eq_sum_basis`, `divergence_pi`, `divergence_eq_sum_orthonormalBasis`,
  `divergence_euclideanSpace`: the divergence in coordinates.
* `divergence_conj`: the divergence is invariant under a linear change of variables.
* `divergence_add`, `divergence_sub`, `divergence_neg`, `divergence_const_smul`,
  `divergence_sum`: the divergence is linear on differentiable vector fields.
* `divergence_smul`: the product rule `div (c • f) = c * div f + Dc (f)`.
* `ContDiff.continuous_divergence`, `measurable_divergence`: regularity of the divergence.

## Tags

divergence, vector field, trace
-/

@[expose] public section

open Set Function Filter Module

open scoped Topology

noncomputable section

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The divergence of a vector field `f : E → E` at `x`, i.e. the trace of `fderiv 𝕜 f x`.

It is `0` when `f` is not differentiable at `x`, and when `E` is not finite-dimensional. -/
def divergence (f : E → E) (x : E) : 𝕜 :=
  LinearMap.trace 𝕜 E (fderiv 𝕜 f x)

variable {𝕜} {f g : E → E} {x : E}

theorem divergence_def : divergence 𝕜 f x = LinearMap.trace 𝕜 E (fderiv 𝕜 f x) :=
  rfl

theorem divergence_eq_trace [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] :
    divergence 𝕜 f x = ContinuousLinearMap.trace 𝕜 E (fderiv 𝕜 f x) :=
  rfl

theorem HasFDerivAt.divergence_eq {f' : E →L[𝕜] E} (h : HasFDerivAt f f' x) :
    divergence 𝕜 f x = LinearMap.trace 𝕜 E f' := by
  rw [divergence, h.fderiv]

theorem divergence_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) :
    divergence 𝕜 f x = 0 := by
  simp [divergence, fderiv_zero_of_not_differentiableAt h]

/-! ### Divergence in coordinates -/

section Coordinates

/-- The divergence in a basis `b`: `div f x = ∑ i, b.coord i (fderiv 𝕜 f x (b i))`. -/
theorem divergence_eq_sum_basis {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 E) :
    divergence 𝕜 f x = ∑ i, b.coord i (fderiv 𝕜 f x (b i)) := by
  classical
  simp [divergence, LinearMap.trace_eq_matrix_trace 𝕜 b, Matrix.trace, LinearMap.toMatrix_apply]

/-- The divergence on `ι → 𝕜`. This is the expression of the divergence in the divergence theorem
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. -/
theorem divergence_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → 𝕜) → ι → 𝕜}
    {x : ι → 𝕜} : divergence 𝕜 f x = ∑ i, fderiv 𝕜 f x (Pi.single i 1) i := by
  simp [divergence_eq_sum_basis (Pi.basisFun 𝕜 ι)]

/-- The divergence in an orthonormal basis `b`: `div f x = ∑ i, ⟪b i, fderiv 𝕜 f x (b i)⟫`. -/
theorem divergence_eq_sum_orthonormalBasis {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {f : E → E} {x : E} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) :
    divergence 𝕜 f x = ∑ i, inner 𝕜 (b i) (fderiv 𝕜 f x (b i)) := by
  simp [divergence_eq_sum_basis b.toBasis, b.repr_apply_apply]

/-- The divergence on `EuclideanSpace 𝕜 ι`, the usual `∑ i, ∂ᵢ fᵢ`. -/
theorem divergence_euclideanSpace {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : EuclideanSpace 𝕜 ι → EuclideanSpace 𝕜 ι} {x : EuclideanSpace 𝕜 ι} :
    divergence 𝕜 f x = ∑ i, fderiv 𝕜 f x (EuclideanSpace.single i 1) i := by
  simp [divergence_eq_sum_basis (EuclideanSpace.basisFun ι 𝕜).toBasis]

/-- The divergence is invariant under a linear change of variables: if `e : E ≃L[𝕜] F`, the
divergence of the field `e ∘ f ∘ e.symm` on `F` at `e x` is the divergence of `f` at `x`. -/
theorem divergence_conj {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : E ≃L[𝕜] F)
    (f : E → E) (x : E) : divergence 𝕜 (e ∘ f ∘ e.symm) (e x) = divergence 𝕜 f x := by
  rw [divergence, e.comp_fderiv, e.symm.comp_right_fderiv, e.symm_apply_apply, divergence,
    ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr 1

end Coordinates

/-! ### Algebraic operations -/

section Algebra

@[simp]
theorem divergence_const (c : E) : divergence 𝕜 (fun _ : E ↦ c) = 0 := by
  ext x
  simp [divergence, fderiv_fun_const]

@[simp]
theorem divergence_zero : divergence 𝕜 (0 : E → E) = 0 :=
  divergence_const 0

@[simp]
theorem divergence_id : divergence 𝕜 (id : E → E) x = finrank 𝕜 E := by
  by_cases hE : FiniteDimensional 𝕜 E
  · simp [divergence, fderiv_id, LinearMap.trace_id]
  · have h : ¬∃ s : Finset E, Nonempty (Basis s 𝕜 E) := fun ⟨_, ⟨b⟩⟩ ↦
      hE (Module.Finite.of_basis b)
    simp [divergence, LinearMap.trace, h, finrank_of_not_finite hE]

@[simp]
theorem divergence_id' : divergence 𝕜 (fun x : E ↦ x) x = finrank 𝕜 E :=
  divergence_id

theorem divergence_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (f + g) x = divergence 𝕜 f x + divergence 𝕜 g x := by
  simp [divergence, fderiv_add hf hg]

theorem divergence_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun y ↦ f y + g y) x = divergence 𝕜 f x + divergence 𝕜 g x :=
  divergence_add hf hg

@[simp]
theorem divergence_neg : divergence 𝕜 (-f) x = -divergence 𝕜 f x := by
  simp [divergence, fderiv_neg]

@[simp]
theorem divergence_fun_neg : divergence 𝕜 (fun y ↦ -f y) x = -divergence 𝕜 f x :=
  divergence_neg

theorem divergence_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (f - g) x = divergence 𝕜 f x - divergence 𝕜 g x := by
  simp [divergence, fderiv_sub hf hg]

theorem divergence_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    divergence 𝕜 (fun y ↦ f y - g y) x = divergence 𝕜 f x - divergence 𝕜 g x :=
  divergence_sub hf hg

theorem divergence_const_smul (hf : DifferentiableAt 𝕜 f x) (c : 𝕜) :
    divergence 𝕜 (c • f) x = c * divergence 𝕜 f x := by
  simp [divergence, fderiv_const_smul hf]

theorem divergence_fun_const_smul (hf : DifferentiableAt 𝕜 f x) (c : 𝕜) :
    divergence 𝕜 (fun y ↦ c • f y) x = c * divergence 𝕜 f x :=
  divergence_const_smul hf c

theorem divergence_sum {ι : Type*} {u : Finset ι} {A : ι → E → E}
    (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    divergence 𝕜 (∑ i ∈ u, A i) x = ∑ i ∈ u, divergence 𝕜 (A i) x := by
  simp [divergence, fderiv_sum h]

theorem divergence_fun_sum {ι : Type*} {u : Finset ι} {A : ι → E → E}
    (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    divergence 𝕜 (fun y ↦ ∑ i ∈ u, A i y) x = ∑ i ∈ u, divergence 𝕜 (A i) x := by
  simp [divergence, fderiv_fun_sum h]

/-- The product rule for the divergence: `div (c • f) = c * div f + Dc (f)`. -/
theorem divergence_smul [FiniteDimensional 𝕜 E] {c : E → 𝕜} (hc : DifferentiableAt 𝕜 c x)
    (hf : DifferentiableAt 𝕜 f x) :
    divergence 𝕜 (c • f) x = c x * divergence 𝕜 f x + fderiv 𝕜 c x (f x) := by
  rw [divergence, fderiv_smul hc hf, ContinuousLinearMap.toLinearMap_add, map_add,
    ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, divergence]
  congr 1
  exact LinearMap.trace_smulRight (fderiv 𝕜 c x : E →ₗ[𝕜] 𝕜) (f x)

/-- The product rule for the divergence: `div (c • f) = c * div f + Dc (f)`. -/
theorem divergence_fun_smul [FiniteDimensional 𝕜 E] {c : E → 𝕜} (hc : DifferentiableAt 𝕜 c x)
    (hf : DifferentiableAt 𝕜 f x) :
    divergence 𝕜 (fun y ↦ c y • f y) x = c x * divergence 𝕜 f x + fderiv 𝕜 c x (f x) :=
  divergence_smul hc hf

end Algebra

/-! ### Locality -/

section Locality

theorem Filter.EventuallyEq.divergence_eq (h : f =ᶠ[𝓝 x] g) :
    divergence 𝕜 f x = divergence 𝕜 g x := by
  rw [divergence, h.fderiv_eq, divergence]

theorem divergence_of_notMem_tsupport (h : x ∉ tsupport f) : divergence 𝕜 f x = 0 := by
  simp [divergence, fderiv_of_notMem_tsupport 𝕜 h]

theorem support_divergence_subset : support (divergence 𝕜 f) ⊆ tsupport f := fun _ hx ↦ by
  by_contra h
  exact hx (divergence_of_notMem_tsupport h)

theorem tsupport_divergence_subset : tsupport (divergence 𝕜 f) ⊆ tsupport f :=
  closure_minimal support_divergence_subset isClosed_closure

protected theorem HasCompactSupport.divergence (hf : HasCompactSupport f) :
    HasCompactSupport (divergence 𝕜 f) :=
  hf.mono' support_divergence_subset

end Locality

/-! ### Regularity -/

section Regularity

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

theorem ContDiffAt.continuousAt_divergence {n : WithTop ℕ∞} (hf : ContDiffAt 𝕜 n f x)
    (hn : n ≠ 0) : ContinuousAt (divergence 𝕜 f) x :=
  (ContinuousLinearMap.trace 𝕜 E).continuous.continuousAt.comp (hf.continuousAt_fderiv hn)

theorem ContDiff.continuous_divergence (hf : ContDiff 𝕜 1 f) : Continuous (divergence 𝕜 f) :=
  (ContinuousLinearMap.trace 𝕜 E).continuous.comp (hf.continuous_fderiv one_ne_zero)

theorem ContDiffOn.continuousOn_divergence {s : Set E} (hf : ContDiffOn 𝕜 1 f s)
    (hs : IsOpen s) : ContinuousOn (divergence 𝕜 f) s :=
  (ContinuousLinearMap.trace 𝕜 E).continuous.comp_continuousOn
    (hf.continuousOn_fderiv_of_isOpen hs le_rfl)

@[fun_prop]
theorem measurable_divergence [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace 𝕜]
    [BorelSpace 𝕜] (f : E → E) : Measurable (divergence 𝕜 f) :=
  have := FiniteDimensional.completeSpace 𝕜 E
  (ContinuousLinearMap.trace 𝕜 E).continuous.measurable.comp (measurable_fderiv 𝕜 f)

end Regularity
