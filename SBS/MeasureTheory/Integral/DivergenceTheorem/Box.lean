/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import SBS.Analysis.Calculus.Divergence

/-!
# The divergence theorem on a box, in terms of `divergence`

This file restates the divergence theorem on a box of Mathlib,
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`, with the divergence
`divergence ℝ f` and with the outward flux `boxFlux a b f` of `f` through the boundary of the box
`[a, b] ⊆ ℝⁿ⁺¹`.

The `i`-th face `{x | x i = b i}` (resp. `{x | x i = a i}`) of `[a, b]` is parametrized by the
box `[a ∘ Fin.succAbove i, b ∘ Fin.succAbove i] ⊆ ℝⁿ` through `Fin.insertNth i (b i)`
(resp. `Fin.insertNth i (a i)`), and its outward unit normal is `Pi.single i 1`
(resp. `-Pi.single i 1`). So `boxFlux a b f` is the surface integral `∮_{∂[a, b]} f · n dS`.

## Main definitions

* `MeasureTheory.boxFlux a b f`: the outward flux of `f` through the boundary of `[a, b]`.

## Main statements

* `MeasureTheory.integral_divergence_eq_boxFlux`: the divergence theorem on `[a, b]`.
-/

@[expose] public section

open Set

noncomputable section

namespace MeasureTheory

variable {n : ℕ} (a b : Fin (n + 1) → ℝ)

/-- The outward flux of the vector field `f : ℝⁿ⁺¹ → ℝⁿ⁺¹` through the boundary of the box
`[a, b]`, i.e. the surface integral `∮_{∂[a, b]} f · n dS`. -/
def boxFlux (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f (i.insertNth (b i) x) i) -
      ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f (i.insertNth (a i) x) i)

variable {a b} {f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}

/-- **Divergence theorem on a box.** If `f` is continuous on `[a, b]`, differentiable on its
interior, and has an integrable divergence on `[a, b]`, then the integral of its divergence over
`[a, b]` is its outward flux through the boundary of `[a, b]`. -/
theorem integral_divergence_eq_boxFlux (hle : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ univ.pi fun i ↦ Ioo (a i) (b i), DifferentiableAt ℝ f x)
    (hi : IntegrableOn (divergence ℝ f) (Icc a b)) :
    ∫ x in Icc a b, divergence ℝ f x = boxFlux a b f := by
  have h : divergence ℝ f = fun x ↦ ∑ i, fderiv ℝ f x (Pi.single i 1) i :=
    funext fun _ ↦ divergence_pi
  rw [h] at hi ⊢
  exact integral_divergence_of_hasFDerivAt_off_countable a b hle f (fderiv ℝ f) ∅ countable_empty
    hc (fun x hx ↦ (hd x hx.1).hasFDerivAt) hi

end MeasureTheory
