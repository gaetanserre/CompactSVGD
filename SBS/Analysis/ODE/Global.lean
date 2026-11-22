/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Global solutions of ODEs with a bounded Lipschitz vector field

Let `v : ℝ → E → E` be a time-dependent vector field on a Banach space `E`, which is continuous in
time, `K`-Lipschitz in space and bounded by `L`. Then for every initial condition `(t₀, x₀)`, the
ODE `α' t = v t (α t)` has a solution defined on all of `ℝ`
(`exists_forall_hasDerivAt_of_lipschitzWith`), which is unique by `ODE_solution_unique_univ`.

We also prove an invariance principle: if every point of the frontier of a closed set `s` is an
equilibrium of `v`, then a solution that meets `s` stays in `s` forever, in both time directions
(`mem_of_forall_frontier_eq_zero`). Indeed a solution leaving `s` must cross its frontier, and the
solution through an equilibrium is constant.

## Main statements

* `exists_forall_hasDerivAt_of_lipschitzWith`: global existence.
* `mem_of_forall_frontier_eq_zero`: invariance of a closed set whose frontier consists of
  equilibria.
-/

@[expose] public section

open Set Metric

open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ℝ → E → E} {K : ℝ≥0}

/-- **Global existence for a bounded Lipschitz vector field.** If `v` is continuous in time,
`K`-Lipschitz in space and bounded by `L`, then the ODE `α' = v t α` has a solution on `ℝ` with
`α t₀ = x₀`. -/
theorem exists_forall_hasDerivAt_of_lipschitzWith [CompleteSpace E] {L : ℝ≥0}
    (hv : ∀ t, LipschitzWith K (v t)) (hc : ∀ x, Continuous (v · x)) (hb : ∀ t x, ‖v t x‖ ≤ L)
    (t₀ : ℝ) (x₀ : E) : ∃ α : ℝ → E, α t₀ = x₀ ∧ ∀ t, HasDerivAt α (v t (α t)) t := by
  -- Local solutions on the intervals `[t₀ - (n + 1), t₀ + (n + 1)]`.
  have hmem (n : ℕ) : t₀ ∈ Icc (t₀ - (n + 1)) (t₀ + (n + 1)) := by
    constructor <;> linarith
  have hpl (n : ℕ) : IsPicardLindelof v ⟨t₀, hmem n⟩ x₀ (L * (n + 1)) 0 L K :=
    { lipschitzOnWith := fun t _ ↦ (hv t).lipschitzOnWith
      continuousOn := fun x _ ↦ (hc x).continuousOn
      norm_le := fun t _ x _ ↦ hb t x
      mul_max_le := by simp }
  choose β hβ₀ hβ using fun n ↦ (hpl n).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  -- At an interior point of its interval, `β n` has a derivative.
  have hβd (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (t₀ - (n + 1)) (t₀ + (n + 1))) :
      HasDerivAt (β n) (v t (β n t)) t :=
    (hβ n t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- The local solutions agree on the intersection of their intervals.
  have hcons (m n : ℕ) (hmn : m ≤ n) {t : ℝ} (ht : t ∈ Icc (t₀ - (m + 1)) (t₀ + (m + 1))) :
      β m t = β n t := by
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    have hsub : Icc (t₀ - (m + 1)) (t₀ + (m + 1)) ⊆ Icc (t₀ - (n + 1)) (t₀ + (n + 1)) :=
      Icc_subset_Icc (by linarith) (by linarith)
    refine ODE_solution_unique_of_mem_Icc (s := fun _ ↦ univ) (fun t _ ↦ (hv t).lipschitzOnWith)
      (by constructor <;> linarith : t₀ ∈ Ioo (t₀ - (m + 1)) (t₀ + (m + 1)))
      (fun t ht ↦ (hβ m t ht).continuousWithinAt)
      (fun t ht ↦ hβd m ht) (fun _ _ ↦ trivial)
      (fun t ht ↦ ((hβ n t (hsub ht)).mono hsub).continuousWithinAt)
      (fun t ht ↦ hβd n ⟨by linarith [ht.1], by linarith [ht.2]⟩) (fun _ _ ↦ trivial)
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
  have hβN := hβd N (t := t) ⟨by linarith [(abs_lt.1 hN).1], by linarith [(abs_lt.1 hN).2]⟩
  rw [hev.eq_of_nhds]
  exact hβN.congr_of_eventuallyEq hev

/-- **Invariance of a closed set whose frontier consists of equilibria.** Let `v` be Lipschitz in
space, and let `s` be a closed set such that `v t y = 0` for every `y ∈ frontier s`. Then a solution
of `α' = v t α` that meets `s` at some time stays in `s` at all times. -/
theorem mem_of_forall_frontier_eq_zero {s : Set E} (hs : IsClosed s)
    (hv : ∀ t, LipschitzWith K (v t)) (h₀ : ∀ t, ∀ y ∈ frontier s, v t y = 0) {α : ℝ → E}
    (hα : ∀ t, HasDerivAt α (v t (α t)) t) {t₀ : ℝ} (ht₀ : α t₀ ∈ s) (t : ℝ) : α t ∈ s := by
  have hαc : Continuous α := continuous_iff_continuousAt.2 fun t ↦ (hα t).continuousAt
  -- If `α` meets the frontier of `s`, then it is constant, equal to an equilibrium.
  have hconst {τ : ℝ} (hτ : α τ ∈ frontier s) : α = fun _ ↦ α τ :=
    ODE_solution_unique_univ (s := fun _ ↦ univ) (t₀ := τ) (fun t ↦ (hv t).lipschitzOnWith)
      (fun t ↦ ⟨hα t, trivial⟩) (fun t ↦ ⟨by simpa [h₀ t _ hτ] using hasDerivAt_const t (α τ),
        trivial⟩) rfl
  by_contra ht
  -- Otherwise, the connected set `α '' [t₀, t]` meets `s` and its complement, but not the
  -- frontier of `s`, which is impossible.
  by_cases hfr : ∃ τ ∈ uIcc t₀ t, α τ ∈ frontier s
  · obtain ⟨τ, -, hτ⟩ := hfr
    exact ht (congrFun (hconst hτ) t ▸ hs.frontier_subset hτ)
  push Not at hfr
  obtain ⟨_, ⟨τ, hτ, rfl⟩, hτ₁, hτ₂⟩ := (isPreconnected_uIcc.image α hαc.continuousOn)
    (interior s) (closure s)ᶜ isOpen_interior isClosed_closure.isOpen_compl
    (by
      rintro _ ⟨τ, hτ, rfl⟩
      by_cases hcl : α τ ∈ closure s
      · exact Or.inl (by_contra fun hi ↦ hfr τ hτ ⟨hcl, hi⟩)
      · exact Or.inr hcl)
    ⟨α t₀, ⟨t₀, left_mem_uIcc, rfl⟩,
      by_contra fun hi ↦ hfr t₀ left_mem_uIcc ⟨subset_closure ht₀, hi⟩⟩
    ⟨α t, ⟨t, right_mem_uIcc, rfl⟩, by rwa [hs.closure_eq]⟩
  exact hτ₂ (interior_subset_closure hτ₁)
