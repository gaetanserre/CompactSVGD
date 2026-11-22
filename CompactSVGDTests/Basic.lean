/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

import CompactSVGD

/-!
# Tests for CompactSVGD

Typical uses of the Stein operator and of the objects of SVGD.
-/

@[expose] public section

open scoped SVGD

/-- With a zero score, the Stein operator is the divergence. -/
example (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    ProbabilityTheory.steinOperator 0 φ = divergence ℝ φ := by
  ext x
  simp [ProbabilityTheory.steinOperator]

/-- The components of the vector field of `h ∈ 𝓗` are the pairings `⟪hᵢ, Φ y⟫`. -/
example (Φ : EuclideanSpace ℝ (Fin 2) → ℝ) (h : 𝓗[2, ℝ]) (y : EuclideanSpace ℝ (Fin 2))
    (i : Fin 2) : SVGD.toVectorField Φ h y i = inner ℝ (h i) (Φ y) := by
  simp
