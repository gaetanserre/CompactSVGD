/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions

import CompactSVGD.ForMathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Global solutions of Lipschitz ODEs

Let `v : ℝ → E → E` be a time-dependent vector field on a Banach space `E`, continuous in time and
`K`-Lipschitz in space uniformly in time. For every initial condition `(t₀, x)`, the ODE
`α' t = v t (α t)` has a unique solution on `ℝ` (an integral curve of `v`),
`ODE.globalSolution v t₀ x`.

Existence is proved first for a bounded field, by gluing the local solutions of the
Picard–Lindelöf theorem on larger and larger intervals. In general, on a compact time interval, a
solution of the field cut off outside a large ball and outside this interval stays in the ball by
Grönwall's inequality, hence solves the original field there. The cut-off field is bounded.

This file is the API of `ODE.globalSolution`, defined in `CompactSVGD/Definitions.lean`.

## Main statements

* `ODE.exists_isIntegralCurve_of_lipschitzWith`: global existence.
* `IsIntegralCurve.eq_globalSolution`: uniqueness.
* `ODE.dist_globalSolution_le`: Lipschitz dependence on the initial condition.
* `ODE.globalSolution_eq_of_eqOn`: the solution at time `t` only depends on the field between `t₀`
  and `t`.
-/

@[expose] public section

open Set Metric

open scoped NNReal Topology

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ℝ → E → E} {K : ℝ≥0}

/-! ### Existence -/

/-- Solutions on larger and larger intervals glue into a solution on `ℝ`. -/
private theorem exists_isIntegralCurve_of_forall_nat (hv : ∀ t, LipschitzWith K (v t))
    {t₀ : ℝ} {x₀ : E} (h : ∀ n : ℕ, ∃ β : ℝ → E, β t₀ = x₀ ∧
      ∀ t ∈ Icc (t₀ - (n + 1)) (t₀ + (n + 1)), HasDerivAt β (v t (β t)) t) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurve α v := by
  choose β hβ₀ hβ using h
  have hβc (n : ℕ) : ContinuousOn (β n) (Icc (t₀ - (n + 1)) (t₀ + (n + 1))) :=
    fun t ht ↦ (hβ n t ht).continuousAt.continuousWithinAt
  -- The local solutions agree on the intersection of their intervals.
  have hcons (m n : ℕ) (hmn : m ≤ n) {t : ℝ} (ht : t ∈ Icc (t₀ - (m + 1)) (t₀ + (m + 1))) :
      β m t = β n t := by
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    have hsub : Icc (t₀ - (m + 1)) (t₀ + (m + 1)) ⊆ Icc (t₀ - (n + 1)) (t₀ + (n + 1)) :=
      Icc_subset_Icc (by linarith) (by linarith)
    refine ODE_solution_unique_of_mem_Icc (s := fun _ ↦ univ) (fun t _ ↦ (hv t).lipschitzOnWith)
      (by constructor <;> linarith : t₀ ∈ Ioo (t₀ - (m + 1)) (t₀ + (m + 1))) (hβc m)
      (fun t ht ↦ hβ m t (Ioo_subset_Icc_self ht)) (fun _ _ ↦ trivial) ((hβc n).mono hsub)
      (fun t ht ↦ hβ n t (hsub (Ioo_subset_Icc_self ht))) (fun _ _ ↦ trivial)
      (by rw [hβ₀, hβ₀]) ht
  -- The global solution.
  let α : ℝ → E := fun t ↦ β ⌈|t - t₀|⌉₊ t
  have hα (n : ℕ) {t : ℝ} (ht : |t - t₀| < n + 1) : α t = β n t := by
    have h₁ : |t - t₀| ≤ ⌈|t - t₀|⌉₊ := Nat.le_ceil _
    have h₂ : t ∈ Icc (t₀ - (min ⌈|t - t₀|⌉₊ n + 1)) (t₀ + (min ⌈|t - t₀|⌉₊ n + 1)) := by
      rcases le_total ⌈|t - t₀|⌉₊ n with h | h
      · rw [min_eq_left h]
        constructor <;> linarith [abs_le.1 h₁]
      · rw [min_eq_right h]
        constructor <;> linarith [(abs_lt.1 ht).1, (abs_lt.1 ht).2]
    rw [show α t = β ⌈|t - t₀|⌉₊ t from rfl, ← hcons (min ⌈|t - t₀|⌉₊ n) _ (min_le_left _ _) h₂,
      hcons (min ⌈|t - t₀|⌉₊ n) n (min_le_right _ _) h₂]
  refine ⟨α, by simpa [α] using hβ₀ 0, fun t ↦ ?_⟩
  -- Near `t`, `α` coincides with `β N`.
  set N := ⌈|t - t₀|⌉₊ + 1
  have hN : |t - t₀| < N := (Nat.le_ceil _).trans_lt (by simp [N])
  have hev : α =ᶠ[𝓝 t] β N := by
    have hopen : IsOpen {u : ℝ | |u - t₀| < N} :=
      isOpen_lt (continuous_abs.comp (continuous_sub_right t₀)) continuous_const
    filter_upwards [hopen.mem_nhds hN] with u hu
    exact hα N (hu.trans (by linarith))
  have hβN := hβ N t ⟨by linarith [(abs_lt.1 hN).1], by linarith [(abs_lt.1 hN).2]⟩
  rw [hev.eq_of_nhds]
  exact hβN.congr_of_eventuallyEq hev

/-- Global existence for a bounded Lipschitz vector field. -/
private theorem exists_isIntegralCurve_of_norm_le [CompleteSpace E] {L : ℝ≥0}
    (hvc : ∀ x, Continuous (v · x)) (hv : ∀ t, LipschitzWith K (v t)) (hL : ∀ t x, ‖v t x‖ ≤ L)
    (t₀ : ℝ) (x₀ : E) : ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurve α v := by
  refine exists_isIntegralCurve_of_forall_nat hv fun n ↦ ?_
  -- A local solution on `[t₀ - (n + 2), t₀ + (n + 2)]`.
  have hmem : t₀ ∈ Icc (t₀ - (n + 2)) (t₀ + (n + 2)) := by
    constructor <;> linarith
  have hpl : IsPicardLindelof v ⟨t₀, hmem⟩ x₀ (L * (n + 2)) 0 L K :=
    { lipschitzOnWith := fun t _ ↦ (hv t).lipschitzOnWith
      continuousOn := fun x _ ↦ (hvc x).continuousOn
      norm_le := fun t _ x _ ↦ hL t x
      mul_max_le := by simp }
  obtain ⟨β, hβ₀, hβ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨β, hβ₀, fun t ht ↦ (hβ t (Icc_subset_Icc (by linarith) (by linarith) ht)).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))⟩

/-- A `2`-Lipschitz retraction of `E` onto `closedBall 0 R` that does not increase norms: the radial
retraction `y ↦ (R / max R ‖y‖) • y`. -/
private theorem exists_retraction {R : ℝ} (hR : 0 < R) :
    ∃ r : E → E, LipschitzWith 2 r ∧ (∀ y, ‖r y‖ ≤ ‖y‖) ∧ (∀ y, ‖r y‖ ≤ R) ∧
      ∀ y, ‖y‖ ≤ R → r y = y := by
  refine ⟨fun y ↦ (R / max R ‖y‖) • y, ?_, fun y ↦ ?_, fun y ↦ ?_, fun y hy ↦ ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    set a := max R ‖y‖
    set b := max R ‖z‖
    have ha : R ≤ a := le_max_left _ _
    have hb : R ≤ b := le_max_left _ _
    have ha₀ : 0 < a := hR.trans_le ha
    have hb₀ : 0 < b := hR.trans_le hb
    have hab : |b - a| ≤ ‖y - z‖ := by
      simp only [a, b, max_comm R]
      exact (abs_max_sub_max_le_abs _ _ _).trans
        (by rw [abs_sub_comm]; exact abs_norm_sub_norm_le y z)
    have h₁ : R / a * ‖y - z‖ ≤ ‖y - z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (div_le_one_of_le₀ ha ha₀.le)
    have h₂ : |R / a - R / b| * ‖z‖ ≤ ‖y - z‖ := by
      have hsub : R / a - R / b = R / a * (b - a) / b := by
        field_simp
      rw [hsub, abs_div, abs_mul, abs_of_pos (div_pos hR ha₀), abs_of_pos hb₀]
      calc R / a * |b - a| / b * ‖z‖ = R / a * (‖z‖ / b) * |b - a| := by ring
        _ ≤ 1 * 1 * |b - a| := by
            gcongr
            exacts [div_le_one_of_le₀ ha ha₀.le, div_le_one_of_le₀ (le_max_right _ _) hb₀.le]
        _ ≤ ‖y - z‖ := by rwa [one_mul, one_mul]
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
    calc ‖(R / a) • y - (R / b) • z‖
        = ‖(R / a) • (y - z) + (R / a - R / b) • z‖ := by
          congr 1
          simp only [smul_sub, sub_smul]
          abel
      _ ≤ R / a * ‖y - z‖ + |R / a - R / b| * ‖z‖ := by
          refine (norm_add_le _ _).trans_eq ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (div_pos hR ha₀).le, Real.norm_eq_abs]
      _ ≤ 2 * ‖y - z‖ := by linarith
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (div_le_one_of_le₀ (le_max_left _ _) (hR.le.trans (le_max_left _ _)))
  · rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div,
      div_le_iff₀ (hR.trans_le (le_max_left _ _))]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR.le
  · rcases eq_or_ne y 0 with rfl | hy₀
    · simp
    change (R / max R ‖y‖) • y = y
    rw [max_eq_left hy, div_self ((norm_pos_iff.2 hy₀).trans_le hy).ne', one_smul]

/-- **Global existence for a Lipschitz vector field.** If `v` is continuous in time and
`K`-Lipschitz in space uniformly in time, then the ODE `α' t = v t (α t)` has a solution on `ℝ`
with `α t₀ = x₀`. -/
theorem exists_isIntegralCurve_of_lipschitzWith [CompleteSpace E]
    (hvc : ∀ x, Continuous (v · x)) (hv : ∀ t, LipschitzWith K (v t)) (t₀ : ℝ) (x₀ : E) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ IsIntegralCurve α v := by
  refine exists_isIntegralCurve_of_forall_nat hv fun n ↦ ?_
  set T : ℝ := n + 1
  have hT₀ : 0 ≤ T := by
    simp only [T]
    positivity
  have hT : t₀ - T ≤ t₀ + T := by linarith
  -- A bound `M ≥ 0` for `‖v t 0‖` on `[t₀ - T, t₀ + T]`, and the radius `R` of the ball.
  obtain ⟨M', hM'⟩ := (isCompact_Icc.image_of_continuousOn
    ((continuous_norm.comp (hvc 0)).continuousOn (s := Icc (t₀ - T) (t₀ + T)))).bddAbove
  set M := max M' 0
  have hM (t : ℝ) : ‖v (projIcc _ _ hT t) 0‖ ≤ M :=
    (hM' ⟨_, Subtype.property _, rfl⟩).trans (le_max_left _ _)
  set R := gronwallBound ‖x₀‖ K M T + 1
  have hR : 0 < R := by
    have : 0 ≤ gronwallBound ‖x₀‖ K M T := (norm_nonneg x₀).trans_eq (gronwallBound_x0 _ _ _).symm
      |>.trans (gronwallBound_mono (norm_nonneg _) (le_max_right _ _) K.coe_nonneg (by positivity))
    linarith
  -- The field cut off outside `closedBall 0 R` and outside `[t₀ - T, t₀ + T]` is bounded.
  obtain ⟨r, hrL, hr, hrR, hr_eq⟩ := exists_retraction (E := E) hR
  set w : ℝ → E → E := fun t y ↦ v (projIcc _ _ hT t) (r y)
  have hw (t : ℝ) (y : E) : ‖w t y‖ ≤ K * ‖r y‖ + M := by
    have := (hv (projIcc _ _ hT t)).norm_sub_le (r y) 0
    rw [sub_zero] at this
    linarith [norm_le_insert' (v (projIcc _ _ hT t) (r y)) (v (projIcc _ _ hT t) 0),
      hM t]
  have hwb (t : ℝ) (y : E) : ‖w t y‖ ≤ K * ‖y‖ + M :=
    (hw t y).trans (by gcongr; exact hr y)
  obtain ⟨β, hβ₀, hβ⟩ := exists_isIntegralCurve_of_norm_le (K := K * 2)
    (L := (K * R + M).toNNReal) (v := w)
    (fun y ↦ (hvc _).comp (continuous_subtypeVal.comp continuous_projIcc))
    (fun t ↦ (hv _).comp hrL)
    (fun t y ↦ (hw t y).trans ((add_le_add_left (mul_le_mul_of_nonneg_left
      (hrR y) K.coe_nonneg) M).trans (Real.le_coe_toNNReal _))) t₀ x₀
  -- By Grönwall's inequality, `β` stays in `closedBall 0 R` on `[t₀ - T, t₀ + T]`, where it
  -- solves the original field.
  refine ⟨β, hβ₀, fun t ht ↦ ?_⟩
  have hβR : ‖β t‖ ≤ R := by
    have := norm_le_gronwallBound_of_norm_deriv_le (t₀ := t₀) (t := t) (fun s _ ↦ hβ s)
      (fun s _ ↦ hwb s (β s))
    rw [hβ₀] at this
    refine this.trans ((gronwallBound_mono (norm_nonneg _) (le_max_right _ _) K.coe_nonneg
      (show |t - t₀| ≤ T from abs_sub_le_iff.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩)).trans
      (by linarith))
  have hwv : w t (β t) = v t (β t) := by
    simp only [w, projIcc_of_mem hT ht, hr_eq _ hβR]
  exact hwv ▸ hβ t

/-! ### The global solution -/

variable [CompleteSpace E] (hvc : ∀ x, Continuous (v · x)) (hv : ∀ t, LipschitzWith K (v t))
include hvc hv

private theorem globalSolution_spec (t₀ : ℝ) (x : E) :
    globalSolution v t₀ x t₀ = x ∧ IsIntegralCurve (globalSolution v t₀ x) v := by
  have h := exists_isIntegralCurve_of_lipschitzWith hvc hv t₀ x
  rw [globalSolution, dite_eq_left h]
  exact h.choose_spec

theorem globalSolution_self (t₀ : ℝ) (x : E) : globalSolution v t₀ x t₀ = x :=
  (globalSolution_spec hvc hv t₀ x).1

theorem isIntegralCurve_globalSolution (t₀ : ℝ) (x : E) :
    IsIntegralCurve (globalSolution v t₀ x) v :=
  (globalSolution_spec hvc hv t₀ x).2

theorem continuous_globalSolution (t₀ : ℝ) (x : E) : Continuous (globalSolution v t₀ x) :=
  (isIntegralCurve_globalSolution hvc hv t₀ x).continuous

/-- **Uniqueness.** An integral curve of `v` on `ℝ` is the global solution through its value at any
time `t₀`. -/
theorem _root_.IsIntegralCurve.eq_globalSolution {α : ℝ → E} (hα : IsIntegralCurve α v)
    (t₀ : ℝ) : α = globalSolution v t₀ (α t₀) :=
  ODE_solution_unique_univ (s := fun _ ↦ univ) (t₀ := t₀) (fun t ↦ (hv t).lipschitzOnWith)
    (fun t ↦ ⟨hα t, trivial⟩) (fun t ↦ ⟨isIntegralCurve_globalSolution hvc hv t₀ _ t, trivial⟩)
    (globalSolution_self hvc hv t₀ _).symm

/-- **The evolution law.** Following the solution from `r` to `s`, then from `s` to `t`, is
following it from `r` to `t`. -/
theorem globalSolution_globalSolution (r s t : ℝ) (x : E) :
    globalSolution v s (globalSolution v r x s) t = globalSolution v r x t :=
  (congrFun ((isIntegralCurve_globalSolution hvc hv r x).eq_globalSolution hvc hv s) t).symm

/-- **Lipschitz dependence on the initial condition.** Solutions through `x` and `y` at time `t₀`
are at distance at most `e^{K |t - t₀|} ‖x - y‖` at time `t`. -/
theorem dist_globalSolution_le (t₀ : ℝ) (x y : E) (t : ℝ) :
    dist (globalSolution v t₀ x t) (globalSolution v t₀ y t) ≤
      dist x y * Real.exp (K * |t - t₀|) := by
  have h := norm_le_gronwallBound_of_norm_deriv_le (ε := 0) (K := K) (t₀ := t₀) (t := t)
    (fun s _ ↦ (isIntegralCurve_globalSolution hvc hv t₀ x s).sub
      (isIntegralCurve_globalSolution hvc hv t₀ y s))
    (fun s _ ↦ by simpa [dist_eq_norm] using (hv s).dist_le_mul _ _)
  simpa [globalSolution_self hvc hv, gronwallBound_ε0, dist_eq_norm] using h

theorem continuous_globalSolution_apply (t₀ t : ℝ) : Continuous fun x ↦ globalSolution v t₀ x t :=
  (LipschitzWith.of_dist_le' fun x y ↦ (dist_globalSolution_le hvc hv t₀ x y t).trans_eq
    (mul_comm _ _)).continuous

omit hvc hv

/-- Two fields that agree between times `t₀` and `t` have the same solutions from `t₀` to `t`. -/
theorem globalSolution_eq_of_eqOn {v₁ v₂ : ℝ → E → E} {K₁ K₂ : ℝ≥0}
    (hvc₁ : ∀ x, Continuous (v₁ · x)) (hv₁ : ∀ t, LipschitzWith K₁ (v₁ t))
    (hvc₂ : ∀ x, Continuous (v₂ · x)) (hv₂ : ∀ t, LipschitzWith K₂ (v₂ t)) {t₀ t : ℝ}
    (heq : EqOn v₁ v₂ (uIcc t₀ t)) (x : E) :
    globalSolution v₁ t₀ x t = globalSolution v₂ t₀ x t := by
  set f := globalSolution v₁ t₀ x
  set g := globalSolution v₂ t₀ x
  -- Between `t₀` and `t`, `f` also solves the field `v₂`.
  have hf (s : ℝ) (hs : s ∈ uIcc t₀ t) : HasDerivAt f (v₂ s (f s)) s :=
    congrFun (heq hs) (f s) ▸ isIntegralCurve_globalSolution hvc₁ hv₁ t₀ x s
  have hg := isIntegralCurve_globalSolution hvc₂ hv₂ t₀ x
  have hfg : f t₀ = g t₀ :=
    (globalSolution_self hvc₁ hv₁ t₀ x).trans (globalSolution_self hvc₂ hv₂ t₀ x).symm
  rcases le_total t₀ t with h | h
  · rw [uIcc_of_le h] at hf
    exact ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ univ)
      (fun s _ ↦ (hv₂ s).lipschitzOnWith) (continuous_globalSolution hvc₁ hv₁ t₀ x).continuousOn
      (fun s hs ↦ (hf s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (fun _ _ ↦ trivial)
      (continuous_globalSolution hvc₂ hv₂ t₀ x).continuousOn
      (fun s _ ↦ (hg s).hasDerivWithinAt) (fun _ _ ↦ trivial) hfg ⟨h, le_rfl⟩
  · rw [uIcc_of_ge h] at hf
    exact ODE_solution_unique_of_mem_Icc_left (s := fun _ ↦ univ)
      (fun s _ ↦ (hv₂ s).lipschitzOnWith) (continuous_globalSolution hvc₁ hv₁ t₀ x).continuousOn
      (fun s hs ↦ (hf s (Ioc_subset_Icc_self hs)).hasDerivWithinAt) (fun _ _ ↦ trivial)
      (continuous_globalSolution hvc₂ hv₂ t₀ x).continuousOn
      (fun s _ ↦ (hg s).hasDerivWithinAt) (fun _ _ ↦ trivial) hfg ⟨le_rfl, h⟩

end ODE
