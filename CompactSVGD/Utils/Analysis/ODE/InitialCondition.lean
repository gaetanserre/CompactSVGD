/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.ODE.Basic

import CompactSVGD.Utils.Analysis.ODE.Gronwall

/-!
# Differentiability of solutions of ODEs with respect to the initial condition

Let `v : ℝ → E → E` be a time-dependent vector field on a proper normed space, Lipschitz in space
uniformly in time, with a spatial derivative `Dv t y` jointly continuous in `(t, y)`. If `α x` is
the solution with `α x s = x` and `J` solves the variational equation `J' t = Dv t (α x₀ t) ∘ J t`
with `J s = id`, then `x ↦ α x t` has derivative `J t` at `x₀`, forward and backward in time.

## Main statements

* `ODE.hasFDerivAt_apply_of_hasDerivAt_variational`: the time-`t` map is differentiable, with the
  solution of the variational equation as derivative.

## Implementation notes

The fields are only continuous in time, so the flow need not be differentiable in time and space
jointly. The proof compares `α x - α x₀` with `J (x - x₀)` by Grönwall's inequality instead.
-/

@[expose] public section

open Set Filter Metric Function Asymptotics

open scoped NNReal Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {K : ℝ≥0} {α : E → ℝ → E}
  {J : ℝ → E →L[ℝ] E} {s : ℝ} {x₀ : E}

variable (hv : ∀ t y, HasFDerivAt (v t) (Dv t y) y) (hDv : Continuous (uncurry Dv))
  (hK : ∀ t, LipschitzWith K (v t)) (hα : ∀ x, IsIntegralCurve (α x) v)
  (hα₀ : ∀ x, α x s = x) (hJ : ∀ t, HasDerivAt J ((Dv t (α x₀ t)).comp (J t)) t)
  (hJ₀ : J s = ContinuousLinearMap.id ℝ E)
include hv hDv hK hα hα₀ hJ hJ₀

/-- Differentiability with respect to the initial condition, forward in time. -/
private theorem hasFDerivAt_apply_of_hasDerivAt_variational_of_le {t : ℝ} (hst : s ≤ t) :
    HasFDerivAt (fun x ↦ α x t) (J t) x₀ := by
  set b := α x₀
  have hαc (x : E) : Continuous (α x) := continuous_iff_continuousAt.2 fun τ ↦ (hα x τ).continuousAt
  have hJc : Continuous J := continuous_iff_continuousAt.2 fun τ ↦ (hJ τ).continuousAt
  -- Lipschitz dependence on the initial condition.
  set L := Real.exp (K * (t - s))
  have hL : 0 < L := Real.exp_pos _
  have hlip (x : E) {τ : ℝ} (hτ : τ ∈ Icc s t) : ‖α x τ - b τ‖ ≤ L * ‖x - x₀‖ := by
    have := dist_le_of_trajectories_ODE (v := v) (K := K) (a := s) (b := t) hK
      (hαc x).continuousOn (fun τ _ ↦ (hα x τ).hasDerivWithinAt) (hαc x₀).continuousOn
      (fun τ _ ↦ (hα x₀ τ).hasDerivWithinAt) (le_of_eq (by rw [hα₀, hα₀])) τ hτ
    rw [dist_eq_norm, dist_eq_norm] at this
    refine this.trans ?_
    rw [mul_comm L]
    gcongr ‖x - x₀‖ * ?_
    exact Real.exp_le_exp.2 (by gcongr; exact hτ.2)
  -- Uniform continuity of `Dv` near the trajectory of `x₀`.
  have hQ : IsCompact (Icc s t ×ˢ cthickening 1 (b '' Icc s t)) :=
    isCompact_Icc.prod ((isCompact_Icc.image (hαc x₀)).cthickening)
  have hDvu := Metric.uniformContinuousOn_iff.1 (hQ.uniformContinuousOn_of_continuous
    hDv.continuousOn)
  set G₁ := gronwallBound 0 K 1 (t - s)
  have hG₁ : 0 ≤ G₁ := by
    simpa [G₁, gronwallBound_x0] using gronwallBound_mono le_rfl zero_le_one K.coe_nonneg
      (sub_nonneg.2 hst)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  set ε := c / (L * G₁ + 1)
  have hε : 0 < ε := by positivity
  obtain ⟨η, hη, hηDv⟩ := hDvu ε hε
  set η' := min η 1
  filter_upwards [ball_mem_nhds (0 : E) (show 0 < η' / L by positivity)] with h hh
  rw [mem_ball_zero_iff] at hh
  set x := x₀ + h
  have hx : x - x₀ = h := add_sub_cancel_left x₀ h
  -- The defect `δ τ = α x τ - b τ - J τ h` and its derivative.
  set δ : ℝ → E := fun τ ↦ α x τ - b τ - J τ h
  set δ' : ℝ → E := fun τ ↦ v τ (α x τ) - v τ (b τ) - (Dv τ (b τ)).comp (J τ) h
  have hδd (τ : ℝ) : HasDerivAt δ (δ' τ) τ := by
    have hJh : HasDerivAt (fun τ ↦ J τ h) ((Dv τ (b τ)).comp (J τ) h) τ := by
      simpa using (hJ τ).clm_apply (hasDerivAt_const τ h)
    exact ((hα x τ).sub (hα x₀ τ)).sub hJh
  have hδ₀ : δ s = 0 := by simp [δ, b, hα₀, hJ₀, hx]
  have hbound (τ : ℝ) (hτ : τ ∈ Icc s t) : ‖δ' τ‖ ≤ K * ‖δ τ‖ + ε * L * ‖h‖ := by
    have hab := hlip x hτ
    rw [hx] at hab
    have habη : ‖α x τ - b τ‖ < η' := hab.trans_lt (by
      rw [← lt_div_iff₀' hL]
      exact hh)
    -- The Taylor remainder of `v τ` between `b τ` and `α x τ`.
    have hR : ‖v τ (α x τ) - v τ (b τ) - Dv τ (b τ) (α x τ - b τ)‖ ≤ ε * ‖α x τ - b τ‖ :=
      (convex_closedBall (b τ) ‖α x τ - b τ‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun y _ ↦ (hv τ y).hasFDerivWithinAt) (fun y hy ↦ by
          have hyb : dist y (b τ) < η' := (mem_closedBall.1 hy).trans_lt habη
          have hQy : (τ, y) ∈ Icc s t ×ˢ cthickening 1 (b '' Icc s t) :=
            ⟨hτ, mem_cthickening_of_dist_le y (b τ) 1 _ (mem_image_of_mem _ hτ)
              (hyb.le.trans (min_le_right _ _))⟩
          have hQb : (τ, b τ) ∈ Icc s t ×ˢ cthickening 1 (b '' Icc s t) :=
            ⟨hτ, self_subset_cthickening _ (mem_image_of_mem _ hτ)⟩
          have := hηDv _ hQy _ hQb (by
            simpa [Prod.dist_eq] using hyb.trans_le (min_le_left _ _))
          rw [dist_eq_norm] at this
          exact this.le)
        (mem_closedBall_self (norm_nonneg _)) (by simp [mem_closedBall, dist_eq_norm])
    have hDvK : ‖Dv τ (b τ)‖ ≤ K := (hv τ (b τ)).le_of_lipschitz (hK τ)
    have hsplit : δ' τ = (v τ (α x τ) - v τ (b τ) - Dv τ (b τ) (α x τ - b τ)) +
        Dv τ (b τ) (δ τ) := by
      simp only [δ', δ, ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hsplit]
    calc ‖_ + Dv τ (b τ) (δ τ)‖ ≤ ε * ‖α x τ - b τ‖ + K * ‖δ τ‖ :=
          (norm_add_le _ _).trans (add_le_add hR
            ((ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)))
      _ ≤ K * ‖δ τ‖ + ε * L * ‖h‖ := by
          rw [add_comm, mul_assoc]
          gcongr
  -- Grönwall's inequality.
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := δ) (f' := δ') (a := s) (b := t)
    (fun τ _ ↦ (hδd τ).continuousAt.continuousWithinAt) (fun τ _ ↦ (hδd τ).hasDerivWithinAt)
    (by rw [hδ₀, norm_zero]) (fun τ hτ ↦ hbound τ (Ico_subset_Icc_self hτ)) t ⟨hst, le_rfl⟩
  rw [gronwallBound_δ0] at hgr
  change ‖α (x₀ + h) t - α x₀ t - J t h‖ ≤ c * ‖h‖
  calc ‖α (x₀ + h) t - α x₀ t - J t h‖ = ‖δ t‖ := rfl
    _ ≤ ε * L * ‖h‖ * G₁ := hgr
    _ = c * ‖h‖ * (L * G₁ / (L * G₁ + 1)) := by
        simp only [ε]
        field_simp
    _ ≤ c * ‖h‖ := mul_le_of_le_one_right (by positivity)
        ((div_le_one (by positivity)).2 (by linarith))

/-- Differentiability with respect to the initial condition, backward in time. This follows from
the forward statement by reversing time. -/
private theorem hasFDerivAt_apply_of_hasDerivAt_variational_of_ge {t : ℝ} (hts : t ≤ s) :
    HasFDerivAt (fun x ↦ α x t) (J t) x₀ := by
  have hr (τ : ℝ) : HasDerivAt (fun τ : ℝ ↦ 2 * s - τ) (-1) τ := by
    simpa using (hasDerivAt_id τ).const_sub (2 * s)
  have h := hasFDerivAt_apply_of_hasDerivAt_variational_of_le (v := fun τ y ↦ -v (2 * s - τ) y)
    (Dv := fun τ y ↦ -Dv (2 * s - τ) y) (K := K) (α := fun x τ ↦ α x (2 * s - τ))
    (J := fun τ ↦ J (2 * s - τ)) (s := s) (x₀ := x₀)
    (fun τ y ↦ (hv _ y).neg)
    ((hDv.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).neg)
    (fun τ ↦ LipschitzWith.of_dist_le_mul fun y y' ↦ by
      simpa [dist_neg_neg] using (hK (2 * s - τ)).dist_le_mul y y')
    (fun x τ ↦ by simpa [Function.comp_def] using (hα x (2 * s - τ)).scomp τ (hr τ))
    (fun x ↦ by simpa [two_mul] using hα₀ x)
    (fun τ ↦ by simpa [Function.comp_def] using (hJ (2 * s - τ)).scomp τ (hr τ))
    (by simpa [two_mul] using hJ₀) (t := 2 * s - t) (by linarith)
  simpa using h

/-- **Differentiability with respect to the initial condition.** If `α x` is the solution of
`α' = v t α` with `α x s = x` and `J` solves the variational equation `J' = Dv t (α x₀ t) ∘ J` with
`J s = id`, then `x ↦ α x t` has derivative `J t` at `x₀`, for every time `t`. -/
theorem hasFDerivAt_apply_of_hasDerivAt_variational (t : ℝ) :
    HasFDerivAt (fun x ↦ α x t) (J t) x₀ := by
  rcases le_total s t with hst | hts
  · exact hasFDerivAt_apply_of_hasDerivAt_variational_of_le hv hDv hK hα hα₀ hJ hJ₀ hst
  · exact hasFDerivAt_apply_of_hasDerivAt_variational_of_ge hv hDv hK hα hα₀ hJ hJ₀ hts

end ODE
