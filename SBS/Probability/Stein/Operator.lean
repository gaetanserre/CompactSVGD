/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import SBS.Analysis.Calculus.Divergence

/-!
# The Langevin Stein operator

Let `E` be a real normed space. A *score* is a map `s : E → StrongDual ℝ E`. The (Langevin) Stein
operator with score `s` sends a vector field `φ : E → E` to the function
`steinOperator s φ x = s x (φ x) + divergence ℝ φ x`.

When `s` is the logarithmic derivative of a density `p`, i.e.
`s x = fderiv ℝ (fun y ↦ Real.log (p y)) x`, this is the Stein operator
`𝒜_p φ = ⟪∇ log p, φ⟫ + ∇ · φ` of `p`. The Stein identity only uses the relation `Dp = p • s`
between the density and the score, which we write `HasFDerivAt p (p x • s x) x`. It does not
require `p` to be positive: at a zero of a nonnegative differentiable density, both sides vanish.
The logarithmic derivative satisfies this relation at every point where `p` is differentiable and
either nonzero or locally nonnegative
(`DifferentiableAt.hasFDerivAt_self_smul_fderiv_log_of_eventually_nonneg`).

Under this relation, `p * 𝒜_s φ` is the divergence of `p • φ` (`mul_steinOperator_eq_divergence`).
This is the identity behind the Stein identity `∫ 𝒜_s φ d(p • μ) = 0`.

## Main definitions

* `ProbabilityTheory.steinOperator s φ`: the Stein operator with score `s`, applied to `φ`.

## Main statements

* `ProbabilityTheory.mul_steinOperator_eq_divergence`: if `Dp = p • s` at `x` and `φ` is
  differentiable at `x`, then `p x * 𝒜_s φ x = div (p • φ) x`.
* `DifferentiableAt.hasFDerivAt_self_smul_fderiv_log`,
  `DifferentiableAt.hasFDerivAt_self_smul_fderiv_log_of_eventually_nonneg`: the logarithmic
  derivative of a density is a score.
* `ProbabilityTheory.steinOperator_add`, `ProbabilityTheory.steinOperator_const_smul`,
  `ProbabilityTheory.steinOperator_smul`: algebraic properties of the Stein operator.
* `Continuous.steinOperator`, `Measurable.steinOperator`: regularity of the Stein operator.

## References

* [C. Stein, *A bound for the error in the normal approximation to the distribution of a sum of
  dependent random variables*][Stein1972]
* [Q. Liu, J. Lee, M. Jordan, *A Kernelized Stein Discrepancy for Goodness-of-fit Tests*][Liu2016]
* [J. Gorham, L. Mackey, *Measuring Sample Quality with Stein's Method*][Gorham2015]

## Tags

Stein operator, Stein's method, score function
-/

@[expose] public section

open Filter Set

open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Logarithmic derivatives are scores -/

section Score

variable {p : E → ℝ} {x : E}

/-- If `p` is differentiable at `x` and `p x ≠ 0`, then `Dp = p • D(log ∘ p)` at `x`. -/
theorem DifferentiableAt.hasFDerivAt_self_smul_fderiv_log (hp : DifferentiableAt ℝ p x)
    (hx : p x ≠ 0) : HasFDerivAt p (p x • fderiv ℝ (fun y ↦ Real.log (p y)) x) x := by
  rw [(hp.hasFDerivAt.log hx).fderiv, smul_smul, mul_inv_cancel₀ hx, one_smul]
  exact hp.hasFDerivAt

/-- If `p` is differentiable at `x` and nonnegative near `x`, then `Dp = p • D(log ∘ p)` at `x`.
At a zero of `p`, both sides vanish since `x` is a local minimum of `p`. -/
theorem DifferentiableAt.hasFDerivAt_self_smul_fderiv_log_of_eventually_nonneg
    (hp : DifferentiableAt ℝ p x) (h : 0 ≤ᶠ[𝓝 x] p) :
    HasFDerivAt p (p x • fderiv ℝ (fun y ↦ Real.log (p y)) x) x := by
  rcases eq_or_ne (p x) 0 with hx | hx
  · have hmin : IsLocalMin p x := by
      filter_upwards [h] with y hy
      rw [hx]
      exact hy
    rw [hx, zero_smul, ← hmin.hasFDerivAt_eq_zero hp.hasFDerivAt]
    exact hp.hasFDerivAt
  · exact hp.hasFDerivAt_self_smul_fderiv_log hx

end Score

namespace ProbabilityTheory

/-! ### The Stein operator -/

/-- The (Langevin) Stein operator with score `s : E → StrongDual ℝ E`, applied to the vector
field `φ : E → E`: `steinOperator s φ x = s x (φ x) + divergence ℝ φ x`.

When `s` is the logarithmic derivative of a density `p`, this is the Stein operator
`𝒜_p φ = ⟪∇ log p, φ⟫ + ∇ · φ` of `p`. -/
def steinOperator (s : E → StrongDual ℝ E) (φ : E → E) (x : E) : ℝ :=
  s x (φ x) + divergence ℝ φ x

variable {s t : E → StrongDual ℝ E} {φ ψ : E → E} {x : E}

theorem steinOperator_def : steinOperator s φ x = s x (φ x) + divergence ℝ φ x :=
  rfl

@[simp]
theorem steinOperator_zero_left : steinOperator 0 φ = divergence ℝ φ := by
  ext x
  simp [steinOperator]

@[simp]
theorem steinOperator_zero_right : steinOperator s 0 = 0 := by
  ext x
  simp [steinOperator]

theorem steinOperator_add_left :
    steinOperator (s + t) φ x = steinOperator s φ x + t x (φ x) := by
  simp only [steinOperator, Pi.add_apply, add_apply]
  ring

theorem steinOperator_add (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    steinOperator s (φ + ψ) x = steinOperator s φ x + steinOperator s ψ x := by
  simp only [steinOperator, Pi.add_apply, map_add, divergence_add hφ hψ]
  ring

@[simp]
theorem steinOperator_neg : steinOperator s (-φ) x = -steinOperator s φ x := by
  simp only [steinOperator, Pi.neg_apply, map_neg, divergence_neg]
  ring

theorem steinOperator_sub (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    steinOperator s (φ - ψ) x = steinOperator s φ x - steinOperator s ψ x := by
  simp only [steinOperator, Pi.sub_apply, map_sub, divergence_sub hφ hψ]
  ring

theorem steinOperator_const_smul (hφ : DifferentiableAt ℝ φ x) (c : ℝ) :
    steinOperator s (c • φ) x = c * steinOperator s φ x := by
  simp only [steinOperator, Pi.smul_apply, map_smul, smul_eq_mul, divergence_const_smul hφ]
  ring

theorem steinOperator_sum {ι : Type*} {u : Finset ι} {A : ι → E → E}
    (h : ∀ i ∈ u, DifferentiableAt ℝ (A i) x) :
    steinOperator s (∑ i ∈ u, A i) x = ∑ i ∈ u, steinOperator s (A i) x := by
  simp only [steinOperator, Finset.sum_apply, map_sum, divergence_sum h, Finset.sum_add_distrib]

variable [FiniteDimensional ℝ E]

/-- The product rule for the Stein operator: `𝒜_s (g • φ) = g * 𝒜_s φ + Dg (φ)`. -/
theorem steinOperator_smul {g : E → ℝ} (hg : DifferentiableAt ℝ g x)
    (hφ : DifferentiableAt ℝ φ x) :
    steinOperator s (g • φ) x = g x * steinOperator s φ x + fderiv ℝ g x (φ x) := by
  simp only [steinOperator, Pi.smul_apply', map_smul, smul_eq_mul, divergence_smul hg hφ]
  ring

/-- The Stein operator of a `C¹` field with a continuous score is continuous. -/
protected theorem _root_.Continuous.steinOperator (hs : Continuous s) (hφ : ContDiff ℝ 1 φ) :
    Continuous (steinOperator s φ) :=
  (hs.clm_apply hφ.continuous).add hφ.continuous_divergence

/-- The Stein operator of a measurable field with a measurable score is measurable. -/
@[fun_prop]
protected theorem _root_.Measurable.steinOperator [MeasurableSpace E] [BorelSpace E]
    (hs : Measurable s) (hφ : Measurable φ) : Measurable (steinOperator s φ) :=
  (ContinuousLinearMap.measurable_apply₂.comp (hs.prodMk hφ)).add (measurable_divergence φ)

/-- **The Stein operator is a divergence.** If `Dp = p • s` at `x` and `φ` is differentiable at
`x`, then `p x * 𝒜_s φ x = div (p • φ) x`. -/
theorem mul_steinOperator_eq_divergence {p : E → ℝ} (hp : HasFDerivAt p (p x • s x) x)
    (hφ : DifferentiableAt ℝ φ x) : p x * steinOperator s φ x = divergence ℝ (p • φ) x := by
  rw [divergence_smul hp.differentiableAt hφ, hp.fderiv, steinOperator,
    smul_apply, smul_eq_mul]
  ring

end ProbabilityTheory
