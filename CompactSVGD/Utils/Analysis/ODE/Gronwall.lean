/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# Complements on Grönwall's inequality

With zero initial value, the Grönwall bound `gronwallBound 0 K ε x` is linear in the error rate `ε`
(`gronwallBound_δ0`). Its bound by `ε x e^{K x}` is `TauCeti.gronwallBound_zero_le_mul_exp`.
-/

@[expose] public section

theorem gronwallBound_δ0 (K ε x : ℝ) :
    gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x := by
  unfold gronwallBound
  split_ifs <;> ring
