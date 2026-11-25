/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithms along curves

If `log ∘ p` has derivative `s` on the interior of `Ω`, we give the derivative of `log ∘ p` along a
curve that is in the interior of `Ω` or constant. If `f' = c f` and `f t ≠ 0`, then `(log f)' = c`
at `t`.
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E → ℝ}

/-- The derivative of `τ ↦ log (p (γ τ))` at `t`, where `log ∘ p` has derivative `s` on the
interior of `Ω`, and either `γ t` is in the interior of `Ω`, or `γ` is constant with zero
velocity. -/
theorem hasDerivAt_log_comp_of_mem_interior_or_const {s : E → StrongDual ℝ E} {Ω : Set E}
    (hs : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ Real.log (p y)) (s x) x) {γ : ℝ → E} {γ' : E}
    {t : ℝ} (hγ : HasDerivAt γ γ' t) (h : γ t ∈ interior Ω ∨ (γ = fun _ ↦ γ t) ∧ γ' = 0) :
    HasDerivAt (fun τ ↦ Real.log (p (γ τ))) (s (γ t) γ') t := by
  rcases h with h | ⟨hc, h₀⟩
  · exact (hs _ h).comp_hasDerivAt t hγ
  · rw [h₀, map_zero, hc]
    exact hasDerivAt_const t _

theorem hasDerivAt_log_of_hasDerivAt_mul {f : ℝ → ℝ} {c t : ℝ} (hf : HasDerivAt f (c * f t) t)
    (ht : f t ≠ 0) : HasDerivAt (fun τ ↦ Real.log (f τ)) c t := by
  have := hf.log ht
  rwa [mul_div_cancel_right₀ _ ht] at this
