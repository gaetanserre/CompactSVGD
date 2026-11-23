/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Euclidean space of dimension `1`

In `EuclideanSpace 𝕜 (Fin 1)`, the norm of `x` is the norm of its only coordinate `x 0`, and
`x = x 0 • e₀`.
-/

@[expose] public section

namespace EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜]

theorem norm_fin_one (x : EuclideanSpace 𝕜 (Fin 1)) : ‖x‖ = ‖x 0‖ := by
  simp [EuclideanSpace.norm_eq]

theorem apply_zero_smul_single_fin_one (x : EuclideanSpace 𝕜 (Fin 1)) :
    x 0 • EuclideanSpace.single 0 1 = x := by
  ext i
  fin_cases i
  simp

end EuclideanSpace
