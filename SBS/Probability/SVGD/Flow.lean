/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Probability.SVGD.MeanField
public import SBS.Topology.Order.Gluing

/-!
# Existence of the mean-field SVGD flow

Let `Ω ⊆ ℝᵈ` be compact, let `s` be the score of the target distribution, assumed continuous on
`Ω` only, and let `Φ` be an admissible feature map (`SVGD.AdmissibleFeatureMap`). For every
probability measure `μ` concentrated on `Ω`, this file constructs a solution `(Tₜ)_{t ≥ 0}` of
the mean-field SVGD equation

  `∂ₜ Tₜ(x) = φ*_{μₜ}(Tₜ(x))`, `T₀ = id`, `μₜ = (Tₜ)#μ`,

whose maps `Tₜ` restrict to homeomorphisms of `Ω` (`SVGD.exists_flow`). This is the flow assumed
in Theorem 3.1 of [Serre2025]. No regularity of the target beyond the continuity of its score is
needed, and no regularity of `Ω` beyond compactness.

The solution is obtained by concatenating the solutions on the intervals `[n, n + 1]` given by
Schauder's fixed-point theorem (`SVGD.exists_meanField_Icc`): the solution on `[n + 1, n + 2]`
starts from the measure reached at time `n + 1`. This does not require uniqueness.

## Main definitions

* `SVGD.trajectoryHomeomorph`: the map `x ↦ trajectory Φ m s x t`, as a homeomorphism of `Ω`.

## Main statements

* `SVGD.exists_meanField`: existence of a curve `m` of update directions with
  `m t = φ*_{(Tₜ)#μ}` for `t ≥ 0`, where `Tₜ` is the flow of `m`.
* `SVGD.exists_flow`: existence of the mean-field SVGD flow.

## References

* [Q. Liu, *Stein Variational Gradient Descent as Gradient Flow*][Liu2017]
* [G. Serré, A. Kalogeratos, N. Vayatis, *Stein Boltzmann Sampling*][Serre2025], Theorem 3.1
-/

@[expose] public section

open MeasureTheory Set Function

open scoped NNReal Topology

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- The product space `𝓗[d, H₀] = H₀ᵈ` of the update directions of SVGD. -/
local notation "𝓗[" d ", " H₀ "]" => PiLp 2 fun _ : Fin d ↦ H₀

variable {Φ : EuclideanSpace ℝ (Fin d) → H₀}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {Ω : Set (EuclideanSpace ℝ (Fin d))} {K C B : ℝ≥0} {m : ℝ → 𝓗[d, H₀]}

/-! ### The flow maps are homeomorphisms of `Ω` -/

section Homeomorph

variable (hm : Continuous m) (hmB : ∀ t, ‖m t‖ ≤ B) (hΦK : LipschitzWith K Φ)
  (hΦC : ∀ y, ‖Φ y‖ ≤ C) (hΩ : IsCompact Ω) (hΦΩ : ∀ y ∈ frontier Ω, Φ y = 0)

/-- For `s ≤ t`, the map `x ↦ trajectory Φ m s x t`, as a homeomorphism of the compact set `Ω`.
Its inverse is `y ↦ trajectory Φ m t y s`. -/
def trajectoryHomeomorph {s t : ℝ} (hst : s ≤ t) : Ω ≃ₜ Ω :=
  have := isCompact_iff_compactSpace.1 hΩ
  Continuous.homeoOfEquivCompactToT2 (f :=
    { toFun := fun x ↦ ⟨trajectory Φ m s x t,
        trajectory_mem hm hmB hΦK hΦC hΩ.isClosed hΦΩ x.property t⟩
      invFun := fun y ↦ ⟨trajectory Φ m t y s,
        trajectory_mem hm hmB hΦK hΦC hΩ.isClosed hΦΩ y.property s⟩
      left_inv := fun x ↦ Subtype.ext (trajectory_trajectory_apply hm hmB hΦK hΦC s t x)
      right_inv := fun y ↦ Subtype.ext (trajectory_trajectory_apply hm hmB hΦK hΦC t s y) })
    (((continuous_trajectory_apply hm hmB hΦK hΦC hst).comp continuous_subtypeVal).subtype_mk _)

@[simp]
theorem coe_trajectoryHomeomorph_apply {s t : ℝ} (hst : s ≤ t) (x : Ω) :
    (trajectoryHomeomorph hm hmB hΦK hΦC hΩ hΦΩ hst x : EuclideanSpace ℝ (Fin d)) =
      trajectory Φ m s x t :=
  rfl

end Homeomorph

variable [CompleteSpace H₀] {μ : Measure (EuclideanSpace ℝ (Fin d))}

/-- **Existence of the mean-field SVGD equation on `[0, ∞)`**, in terms of update directions. Let
`Ω` be compact, let the score `s` be continuous on `Ω`, and let `Φ` be an admissible feature map.
For every probability measure `μ` concentrated on `Ω`, there is a continuous curve `m` of update
directions such that `m t = φ*_{(Tₜ)#μ}` for every `t ≥ 0`, where `Tₜ = trajectory Φ m 0 · t` is the
flow of the vector field of `m`. -/
theorem exists_meanField (hΦ : AdmissibleFeatureMap Φ Ω K C) (hΩ : IsCompact Ω)
    (hs : ContinuousOn s Ω) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    ∃ m : ℝ → 𝓗[d, H₀], Continuous m ∧ (∀ t, m t ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω)) ∧
      ∀ t, 0 ≤ t → m t = direction Φ s (μ.map (trajectory Φ m 0 · t)) := by
  set 𝒦 := closedConvexHull ℝ (steinFeature Φ s '' Ω)
  obtain ⟨B, hB⟩ := exists_norm_le_of_mem_closedConvexHull hΩ hΦ.contDiff hs
  -- A solution on `[n, n + 1]` from any probability measure concentrated on `Ω`.
  have hstep (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))) :
      ∃ m : ℝ → 𝓗[d, H₀], IsProbabilityMeasure ν →
      (∀ᵐ x ∂ν, x ∈ Ω) → Continuous m ∧ (∀ t, m t ∈ 𝒦) ∧
        ∀ t ∈ Icc (n : ℝ) (n + 1), m t = direction Φ s (ν.map (trajectory Φ m n · t)) := by
    by_cases h : IsProbabilityMeasure ν ∧ ∀ᵐ x ∂ν, x ∈ Ω
    · have := h.1
      obtain ⟨m, hm⟩ := exists_meanField_Icc hΦ hΩ hs h.2 (show (n : ℝ) ≤ n + 1 by linarith)
      exact ⟨m, fun _ _ ↦ hm⟩
    · exact ⟨0, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩
  choose step hstep using hstep
  -- The measures `νₙ` reached at the integer times, and the curves `mₙ` on `[n, n + 1]`.
  let ν : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun n ↦ Nat.rec μ (fun k νk ↦
    νk.map (trajectory Φ (step k νk) k · (k + 1))) n
  have hν₀ : ν 0 = μ := rfl
  have hνsucc (n : ℕ) : ν (n + 1) = (ν n).map (trajectory Φ (step n (ν n)) n · (n + 1)) := rfl
  let mₙ (n : ℕ) : ℝ → 𝓗[d, H₀] := step n (ν n)
  have hP (n : ℕ) : IsProbabilityMeasure (ν n) ∧ ∀ᵐ x ∂ν n, x ∈ Ω := by
    induction n with
    | zero => exact ⟨hν₀ ▸ inferInstance, hμ⟩
    | succ n ih =>
      have := ih.1
      obtain ⟨hc, hK, -⟩ := hstep n (ν n) ih.1 ih.2
      have hB' : ∀ t, ‖step n (ν n) t‖ ≤ B := fun t ↦ hB _ (hK t)
      rw [hνsucc]
      refine ⟨by infer_instance, ae_mem_map hΩ ih.2
        (continuous_trajectory_apply hc hB' hΦ.lipschitzWith hΦ.norm_le (by linarith))
        fun x hx ↦ trajectory_mem hc hB' hΦ.lipschitzWith hΦ.norm_le hΩ.isClosed
          hΦ.eq_zero_of_mem_frontier hx _⟩
  have hm (n : ℕ) := hstep n (ν n) (hP n).1 (hP n).2
  have hmB (n : ℕ) (t : ℝ) : ‖mₙ n t‖ ≤ B := hB _ ((hm n).2.1 t)
  -- The concatenated curve.
  let M : ℝ → 𝓗[d, H₀] := fun t ↦ mₙ ⌊t⌋₊ t
  have hM (n : ℕ) : EqOn M (mₙ n) (Icc n (n + 1)) := by
    intro t ht
    rcases ht.2.lt_or_eq with hlt | heq
    · have : ⌊t⌋₊ = n := (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans ht.1)).2 ⟨ht.1, hlt⟩
      simp only [M, this]
    · -- At `t = n + 1`, both curves are the update direction of `νₙ₊₁`.
      have hfl : ⌊t⌋₊ = n + 1 := by rw [heq]; exact_mod_cast Nat.floor_natCast (n + 1)
      have h₁ := (hm (n + 1)).2.2 t
        ⟨by rw [heq]; push_cast; linarith, by rw [heq]; push_cast; linarith⟩
      have h₂ := (hm n).2.2 t ⟨ht.1, ht.2⟩
      simp only [M, hfl]
      change step (n + 1) (ν (n + 1)) t = step n (ν n) t
      have hid : (fun x ↦ trajectory Φ (step (n + 1) (ν (n + 1))) ((n + 1 : ℕ) : ℝ) x t) = id := by
        funext x
        rw [heq, show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl]
        exact trajectory_self (hm (n + 1)).1 (hmB (n + 1)) hΦ.lipschitzWith hΦ.norm_le _ x
      rw [h₁, h₂, hid, Measure.map_id, hνsucc, heq]
  have hM₀ : EqOn M (mₙ 0) (Iic 1) := by
    intro t ht
    rcases ht.lt_or_eq with hlt | heq
    · simp only [M, Nat.floor_eq_zero.2 hlt]
    · exact hM 0 ⟨by simp [heq], by simp [heq]⟩
  have hMc : Continuous M := continuous_of_eqOn_Icc_nat (fun n ↦ (hm n).1) hM₀ hM
  have hMK (t : ℝ) : M t ∈ 𝒦 := (hm ⌊t⌋₊).2.1 t
  have hMB (t : ℝ) : ‖M t‖ ≤ B := hB _ (hMK t)
  -- On `[n, n + 1]`, the trajectories of `M` from time `0` follow those of `mₙ` from time `n`.
  have hT (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : t ∈ Icc (n : ℝ) (n + 1)) :
      trajectory Φ M 0 x t = trajectory Φ (mₙ n) n (trajectory Φ M 0 x n) t := by
    refine ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ univ)
      (v := fun t ↦ toVectorField Φ (mₙ n t))
      (fun t _ ↦ (lipschitzWith_toVectorField hΦ.lipschitzWith (hmB n t)).lipschitzOnWith)
      (continuous_trajectory hMc hMB hΦ.lipschitzWith hΦ.norm_le 0 x).continuousOn
      (fun τ hτ ↦ by
        have := (hasDerivAt_trajectory hMc hMB hΦ.lipschitzWith hΦ.norm_le 0 x τ).hasDerivWithinAt
          (s := Ici τ)
        rwa [hM n (Ico_subset_Icc_self hτ)] at this)
      (fun _ _ ↦ trivial)
      (continuous_trajectory (hm n).1 (hmB n) hΦ.lipschitzWith hΦ.norm_le _ _).continuousOn
      (fun τ _ ↦ (hasDerivAt_trajectory (hm n).1 (hmB n) hΦ.lipschitzWith hΦ.norm_le _ _
        τ).hasDerivWithinAt)
      (fun _ _ ↦ trivial)
      (trajectory_self (hm n).1 (hmB n) hΦ.lipschitzWith hΦ.norm_le _ _).symm ht
  -- The image of `μ` at the integer times is `νₙ`.
  have hTν (n : ℕ) : μ.map (trajectory Φ M 0 · n) = ν n := by
    induction n with
    | zero =>
      simp only [Nat.cast_zero, trajectory_self hMc hMB hΦ.lipschitzWith hΦ.norm_le]
      exact Measure.map_id
    | succ n ih =>
      have hcomp : (trajectory Φ M 0 · ((n + 1 : ℕ) : ℝ)) =
          (trajectory Φ (mₙ n) n · (n + 1)) ∘ (trajectory Φ M 0 · n) := by
        funext x
        rw [Nat.cast_succ]
        exact hT n x ⟨by linarith, le_rfl⟩
      rw [hcomp, ← Measure.map_map
        (continuous_trajectory_apply (hm n).1 (hmB n) hΦ.lipschitzWith hΦ.norm_le
          (by linarith)).measurable
        (continuous_trajectory_apply hMc hMB hΦ.lipschitzWith hΦ.norm_le
          (Nat.cast_nonneg n)).measurable, ih, hνsucc]
  refine ⟨M, hMc, hMK, fun t ht ↦ ?_⟩
  set n := ⌊t⌋₊
  have htn : t ∈ Icc (n : ℝ) (n + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  have hcomp : (trajectory Φ M 0 · t) =
      (trajectory Φ (mₙ n) n · t) ∘ (trajectory Φ M 0 · n) := funext fun x ↦ hT n x htn
  rw [hM n htn]
  change step n (ν n) t = _
  rw [(hm n).2.2 t htn, hcomp, ← Measure.map_map
    (continuous_trajectory_apply (hm n).1 (hmB n) hΦ.lipschitzWith hΦ.norm_le htn.1).measurable
    (continuous_trajectory_apply hMc hMB hΦ.lipschitzWith hΦ.norm_le
      (Nat.cast_nonneg n)).measurable, hTν]

/-- **Existence of the mean-field SVGD flow.** Let `Ω ⊆ ℝᵈ` be compact, let the score `s` of the
target be continuous on `Ω`, and let `Φ` be an admissible feature map. For every probability
measure `μ` concentrated on `Ω`, there is a family of maps `(Tₜ)_{t ≥ 0}` such that `T₀ = id`, each
`Tₜ` restricts to a homeomorphism of `Ω`, and the trajectories follow the SVGD vector field:
`∂ₜ Tₜ(x) = φ*_{μₜ}(Tₜ(x))` with `μₜ = (Tₜ)#μ`. -/
theorem exists_flow (hΦ : AdmissibleFeatureMap Φ Ω K C) (hΩ : IsCompact Ω)
    (hs : ContinuousOn s Ω) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω) :
    ∃ T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), (∀ x, T 0 x = x) ∧
      (∀ t, 0 ≤ t → ∃ e : Ω ≃ₜ Ω, ∀ x : Ω, (e x : EuclideanSpace ℝ (Fin d)) = T t x) ∧
      ∀ x, ∀ t, 0 ≤ t →
        HasDerivAt (T · x) (toVectorField Φ (direction Φ s (μ.map (T t))) (T t x)) t := by
  obtain ⟨m, hmc, hmK, hm⟩ := exists_meanField hΦ hΩ hs hμ
  obtain ⟨B, hB⟩ := exists_norm_le_of_mem_closedConvexHull hΩ hΦ.contDiff hs
  have hmB (t : ℝ) : ‖m t‖ ≤ B := hB _ (hmK t)
  refine ⟨fun t x ↦ trajectory Φ m 0 x t,
    fun x ↦ trajectory_self hmc hmB hΦ.lipschitzWith hΦ.norm_le 0 x,
    fun t ht ↦ ⟨trajectoryHomeomorph hmc hmB hΦ.lipschitzWith hΦ.norm_le hΩ
      hΦ.eq_zero_of_mem_frontier ht, fun _ ↦ rfl⟩, fun x t ht ↦ ?_⟩
  rw [← hm t ht]
  exact hasDerivAt_trajectory hmc hmB hΦ.lipschitzWith hΦ.norm_le 0 x t

end SVGD
