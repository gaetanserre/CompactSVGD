/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Probability.Stein.Operator
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The objects of Stein Variational Gradient Descent

Let `E = ℝᵈ = EuclideanSpace ℝ (Fin d)` and let `H₀` be a real inner product space. The kernel of
SVGD is given by a *feature map* `Φ : E → H₀`, with `k(x, y) = ⟪Φ x, Φ y⟫`. When `H₀` is the RKHS
of `k`, `Φ x` is `k(·, x)`. The space of the update directions of SVGD is the product `𝓗 = H₀ᵈ`,
with the inner product `⟪f, g⟫_𝓗 = ∑ i, ⟪fᵢ, gᵢ⟫`.

* `SVGD.toVectorField Φ h` is the vector field `y ↦ (⟪hᵢ, Φ y⟫)ᵢ` of `h ∈ 𝓗`. When `H₀` is the RKHS
  of `k`, this is `h` itself, by the reproducing property.
* `SVGD.steinFeature Φ s x ∈ 𝓗` is `ξₓ = s(x) k(·, x) + ∇ₓ k(·, x)`, i.e.
  `(ξₓ)ᵢ = s x eᵢ • Φ x + ∂ᵢ Φ x`, for a score `s : E → StrongDual ℝ E`.
* `SVGD.direction Φ s ν = ∫ ξₓ dν(x) ∈ 𝓗` is the update direction `φ*_ν` of SVGD.

The update direction is defined for any measure `ν`, with or without a density. The SVGD dynamics
moves particles along the vector field `toVectorField Φ (direction Φ s νₜ)`.

The pairing `⟪h, ξₓ⟫_𝓗` is the Stein operator `𝒜_s` applied to the vector field of `h`
(`SVGD.inner_steinFeature`). This is the bridge between SVGD and Stein's identity.

## Main definitions

* `SVGD.pairing h`: the continuous linear map `u ↦ (⟪hᵢ, u⟫)ᵢ` from `H₀` to `E`.
* `SVGD.toVectorField Φ h`: the vector field of `h ∈ 𝓗`.
* `SVGD.steinFeature Φ s x`: the element `ξₓ` of `𝓗`.
* `SVGD.direction Φ s ν`: the update direction `φ*_ν` of SVGD.

## Main statements

* `SVGD.norm_pairing_apply_le`: `‖(⟪hᵢ, u⟫)ᵢ‖ ≤ ‖h‖ ‖u‖`, by the Cauchy–Schwarz inequality.
* `SVGD.inner_steinFeature`: `⟪h, ξₓ⟫ = 𝒜_s (toVectorField Φ h) x`.

## References

* [Q. Liu, D. Wang, *Stein Variational Gradient Descent*][Liu2016SVGD]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025]
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- The product space `𝓗[d, H₀] = H₀ᵈ` of the update directions of SVGD. -/
local notation "𝓗[" d ", " H₀ "]" => PiLp 2 fun _ : Fin d ↦ H₀

/-! ### The vector field of an element of `𝓗` -/

/-- The pairing `u ↦ (⟪hᵢ, u⟫)ᵢ` between `H₀` and `E` defined by `h ∈ 𝓗`. -/
def pairing (h : 𝓗[d, H₀]) : H₀ →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (h i))

@[simp]
theorem pairing_apply (h : 𝓗[d, H₀]) (u : H₀) (i : Fin d) : pairing h u i = inner ℝ (h i) u :=
  rfl

theorem pairing_sub (h h' : 𝓗[d, H₀]) (u : H₀) :
    pairing h u - pairing h' u = pairing (h - h') u := by
  ext i
  simp [inner_sub_left]

/-- The vector field of `h ∈ 𝓗`: `toVectorField Φ h y = (⟪hᵢ, Φ y⟫)ᵢ`. When `H₀` is the RKHS of
the kernel `k(x, y) = ⟪Φ x, Φ y⟫`, this is the evaluation of `h` at `y`. -/
def toVectorField (Φ : EuclideanSpace ℝ (Fin d) → H₀) (h : 𝓗[d, H₀])
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  pairing h (Φ y)

variable {Φ : EuclideanSpace ℝ (Fin d) → H₀} {h h' : 𝓗[d, H₀]} {y y' : EuclideanSpace ℝ (Fin d)}

@[simp]
theorem toVectorField_apply (i : Fin d) : toVectorField Φ h y i = inner ℝ (h i) (Φ y) :=
  rfl

theorem toVectorField_eq_zero_of_eq_zero (hy : Φ y = 0) : toVectorField Φ h y = 0 := by
  simp [toVectorField, hy]

theorem hasFDerivAt_toVectorField {Φ' : EuclideanSpace ℝ (Fin d) →L[ℝ] H₀}
    (hΦ : HasFDerivAt Φ Φ' y) :
    HasFDerivAt (toVectorField Φ h) ((pairing h).comp Φ') y :=
  (pairing h).hasFDerivAt.comp y hΦ


/-- The Cauchy–Schwarz inequality for the pairing: `‖(⟪hᵢ, u⟫)ᵢ‖ ≤ ‖h‖ ‖u‖`. -/
theorem norm_pairing_apply_le (h : 𝓗[d, H₀]) (u : H₀) : ‖pairing h u‖ ≤ ‖h‖ * ‖u‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using abs_real_inner_le_norm (h i) u) 2

theorem norm_toVectorField_le : ‖toVectorField Φ h y‖ ≤ ‖h‖ * ‖Φ y‖ :=
  norm_pairing_apply_le h (Φ y)

theorem norm_toVectorField_sub_le :
    ‖toVectorField Φ h y - toVectorField Φ h y'‖ ≤ ‖h‖ * ‖Φ y - Φ y'‖ := by
  rw [toVectorField, toVectorField, ← map_sub]
  exact norm_pairing_apply_le h _

theorem norm_toVectorField_sub_toVectorField_le :
    ‖toVectorField Φ h y - toVectorField Φ h' y‖ ≤ ‖h - h'‖ * ‖Φ y‖ := by
  rw [toVectorField, toVectorField, pairing_sub]
  exact norm_pairing_apply_le _ _

/-! ### The update direction -/


/-- The element `ξₓ = s(x) k(·, x) + ∇ₓ k(·, x)` of `𝓗`, whose components are
`(ξₓ)ᵢ = s x eᵢ • Φ x + ∂ᵢ Φ x`. -/
def steinFeature (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : 𝓗[d, H₀] :=
  WithLp.toLp 2 fun i ↦
    s x (EuclideanSpace.single i 1) • Φ x + fderiv ℝ Φ x (EuclideanSpace.single i 1)

/-- The update direction `φ*_ν = ∫ ξₓ dν(x)` of SVGD for the measure `ν`. -/
def direction (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) : 𝓗[d, H₀] :=
  ∫ x, steinFeature Φ s x ∂ν

variable {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {x : EuclideanSpace ℝ (Fin d)}

@[simp]
theorem steinFeature_apply (i : Fin d) : steinFeature Φ s x i =
    s x (EuclideanSpace.single i 1) • Φ x + fderiv ℝ Φ x (EuclideanSpace.single i 1) :=
  rfl

/-- **The pairing with `ξₓ` is the Stein operator.** For `h ∈ 𝓗`,
`⟪h, ξₓ⟫_𝓗 = s x (h(x)) + div h (x) = 𝒜_s h (x)`, where `h(y) = (⟪hᵢ, Φ y⟫)ᵢ`. -/
theorem inner_steinFeature (hΦ : DifferentiableAt ℝ Φ x) (h : 𝓗[d, H₀]) :
    inner ℝ h (steinFeature Φ s x) = ProbabilityTheory.steinOperator s (toVectorField Φ h) x := by
  have hv : toVectorField Φ h x = ∑ i, inner ℝ (h i) (Φ x) • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [ProbabilityTheory.steinOperator, divergence_euclideanSpace,
    (hasFDerivAt_toVectorField hΦ.hasFDerivAt).fderiv, hv, map_sum, PiLp.inner_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [inner_add_right, inner_smul_right, real_inner_comm, mul_comm]

end SVGD
