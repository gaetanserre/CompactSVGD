/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.MeasureTheory.Integral.DivergenceTheorem.Box
public import SBS.Probability.Stein.Class

/-!
# The Stein class on a box

On a box `Ω = [a, b] ⊆ ℝⁿ⁺¹`, the divergence theorem identifies the condition defining the Stein
class with the vanishing of the boundary flux. If `p • φ` is continuous on `[a, b]`,
differentiable on its interior, and has an integrable divergence on `[a, b]`, then `φ` is in the
Stein class of `p` on `[a, b]` if and only if

  `∮_{∂[a, b]} p φ · n dS = 0`

(`ProbabilityTheory.mem_steinClass_Icc_iff`). This is the definition of the Stein class in
[Liu2016] and [Serre2025], for the domains on which `Stein Boltzmann Sampling` is run.

## Main statements

* `ProbabilityTheory.mem_steinClass_Icc_iff`: on a box, the Stein class is the set of fields with
  zero boundary flux.

## References

* [Q. Liu, J. Lee, M. Jordan, *A Kernelized Stein Discrepancy for Goodness-of-fit Tests*][Liu2016]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Definition A.2
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {n : ℕ} {a b : Fin (n + 1) → ℝ} {p : (Fin (n + 1) → ℝ) → ℝ}
  {φ : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}

/-- On a box `[a, b]`, a field `φ` such that `p • φ` is continuous on `[a, b]`, differentiable on
its interior and has an integrable divergence is in the Stein class of `p` if and only if the
flux of `p • φ` through the boundary of `[a, b]` vanishes. -/
theorem mem_steinClass_Icc_iff (hle : a ≤ b) (hc : ContinuousOn (p • φ) (Icc a b))
    (hd : ∀ x ∈ univ.pi fun i ↦ Ioo (a i) (b i), DifferentiableAt ℝ (p • φ) x)
    (hi : IntegrableOn (divergence ℝ (p • φ)) (Icc a b)) :
    φ ∈ steinClass (volume.restrict (Icc a b)) p ↔ boxFlux a b (p • φ) = 0 := by
  have hae : ∀ᵐ x ∂volume.restrict (Icc a b), DifferentiableAt ℝ (p • φ) x := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo) hd
  rw [mem_steinClass_iff, integral_divergence_eq_boxFlux hle hc hd hi]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hae, hi, h⟩⟩

end ProbabilityTheory
