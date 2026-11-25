/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic

import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The closed convex hull of a compact set

In a real Banach space, the closed convex hull of a compact set is compact.
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {s : Set E}

/-- In a real Banach space, the closed convex hull of a compact set is compact. -/
theorem IsCompact.closedConvexHull (hs : IsCompact s) : IsCompact (closedConvexHull ℝ s) := by
  rw [closedConvexHull_eq_closure_convexHull, isCompact_iff_totallyBounded_isComplete]
  exact ⟨hs.totallyBounded.convexHull.closure, isClosed_closure.isComplete⟩
