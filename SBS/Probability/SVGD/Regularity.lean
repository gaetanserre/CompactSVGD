/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import SBS.Probability.SVGD.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.TotallyBounded
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Regularity of the update direction of SVGD

Let `Ω ⊆ ℝᵈ` be a compact set. The target distribution only enters SVGD through its score `s`, and
the only assumption made on it here is that `s` is continuous on `Ω`. With a `C¹` feature map `Φ`,
this makes `x ↦ ξₓ` continuous on `Ω` (`SVGD.continuousOn_steinFeature`), hence bounded and
uniformly continuous on `Ω` (Lemma A.6 of [Serre2025]).

For every probability measure `ν` concentrated on `Ω`, the update direction `φ*_ν = ∫ ξₓ dν(x)`
is then well-defined, bounded by `B = max_Ω ‖ξ‖` (`SVGD.norm_direction_le`), and lies in the
closed convex hull of `ξ(Ω)` (`SVGD.direction_mem_closedConvexHull`). This hull is compact
(`SVGD.isCompact_closedConvexHull_steinFeature`). This compactness drives the existence of the
SVGD flow by Schauder's fixed-point theorem, without any Lipschitz assumption on the score.

## Main statements

* `SVGD.continuousOn_steinFeature`: `x ↦ ξₓ` is continuous on `Ω`.
* `SVGD.integrable_steinFeature`: `ξ` is integrable for finite measures concentrated on `Ω`.
* `SVGD.norm_direction_le`: `‖φ*_ν‖ ≤ B`.
* `SVGD.direction_mem_closedConvexHull`: `φ*_ν ∈ closedConvexHull ℝ (ξ '' Ω)`.
* `SVGD.isCompact_closedConvexHull_steinFeature`: this closed convex hull is compact.
* `SVGD.direction_map`: `φ*_{X#ν} = ∫ ξ_{X x} dν(x)`.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace SVGD

variable {d : ℕ} {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- The product space `𝓗[d, H₀] = H₀ᵈ` of the update directions of SVGD. -/
local notation "𝓗[" d ", " H₀ "]" => PiLp 2 fun _ : Fin d ↦ H₀

variable {Φ : EuclideanSpace ℝ (Fin d) → H₀}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- `x ↦ ξₓ` is continuous on `Ω` when the score is continuous on `Ω` and `Φ` is `C¹`. -/
theorem continuousOn_steinFeature (hΦ : ContDiff ℝ 1 Φ) (hs : ContinuousOn s Ω) :
    ContinuousOn (steinFeature Φ s) Ω :=
  (PiLp.continuous_toLp 2 _).comp_continuousOn <| continuousOn_pi.2 fun _ ↦
    ((hs.clm_apply continuousOn_const).smul hΦ.continuous.continuousOn).add
      ((hΦ.continuous_fderiv one_ne_zero).continuousOn.clm_apply continuousOn_const)

/-- `‖φ*_ν‖ ≤ B` for every probability measure `ν` concentrated on `Ω`, where `B` bounds `ξ` on
`Ω`. -/
theorem norm_direction_le {B : ℝ} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, x ∈ Ω) : ‖direction Φ s ν‖ ≤ B := by
  simpa [direction] using norm_integral_le_of_norm_le_const (hν.mono hB)

/-- The update direction of an image measure: `φ*_{X#ν} = ∫ ξ_{X x} dν(x)`. -/
theorem direction_map {ν : Measure (EuclideanSpace ℝ (Fin d))}
    {X : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hX : AEMeasurable X ν)
    (hξ : AEStronglyMeasurable (steinFeature Φ s) (ν.map X)) :
    direction Φ s (ν.map X) = ∫ x, steinFeature Φ s (X x) ∂ν :=
  integral_map hX hξ

variable (hΩ : IsCompact Ω) (hΦ : ContDiff ℝ 1 Φ) (hs : ContinuousOn s Ω)
include hΩ hΦ hs

/-- `ξ` is bounded on the compact set `Ω`. -/
theorem exists_norm_steinFeature_le : ∃ B, 0 ≤ B ∧ ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (continuousOn_steinFeature hΦ hs)
  exact ⟨max B 0, le_max_right _ _, fun x hx ↦ (hB x hx).trans (le_max_left _ _)⟩

/-- `ξ` is uniformly continuous on the compact set `Ω`. -/
theorem uniformContinuousOn_steinFeature : UniformContinuousOn (steinFeature Φ s) Ω :=
  hΩ.uniformContinuousOn_of_continuous (continuousOn_steinFeature hΦ hs)

/-- `ξ` is integrable for every finite measure concentrated on `Ω`. -/
theorem integrable_steinFeature {ν : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Ω) :
    Integrable (steinFeature Φ s) ν := by
  rw [← Measure.restrict_eq_self_of_ae_mem hν]
  exact (continuousOn_steinFeature hΦ hs).integrableOn_compact hΩ

variable [CompleteSpace H₀]

/-- The closed convex hull of `ξ(Ω)` is compact. -/
theorem isCompact_closedConvexHull_steinFeature :
    IsCompact (closedConvexHull ℝ (steinFeature Φ s '' Ω)) := by
  rw [closedConvexHull_eq_closure_convexHull, isCompact_iff_totallyBounded_isComplete]
  exact ⟨((hΩ.image_of_continuousOn (continuousOn_steinFeature hΦ hs)).totallyBounded.convexHull
    ).closure, isClosed_closure.isComplete⟩

/-- **The update direction lies in a compact convex set.** For every probability measure `ν`
concentrated on `Ω`, `φ*_ν` lies in the closed convex hull of `ξ(Ω)`. -/
theorem direction_mem_closedConvexHull {ν : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Ω) : direction Φ s ν ∈ closedConvexHull ℝ (steinFeature Φ s '' Ω) :=
  (convex_closedConvexHull).integral_mem isClosed_closedConvexHull
    (hν.mono fun _ hx ↦ subset_closedConvexHull (mem_image_of_mem _ hx))
    (integrable_steinFeature hΩ hΦ hs hν)

end SVGD
