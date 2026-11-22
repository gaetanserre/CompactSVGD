/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Preconnected sets crossing a set

A preconnected set that meets a set `V` and its complement meets the frontier of `V`. Otherwise it
would be covered by the disjoint open sets `interior V` and `(closure V)ᶜ`, and meet both of them.
The proof is adapted from the [Tau Ceti library](https://github.com/TauCetiProject/TauCeti).
-/

@[expose] public section

open Set

theorem IsPreconnected.inter_frontier_nonempty {X : Type*} [TopologicalSpace X] {S V : Set X}
    (hS : IsPreconnected S) (h₁ : (S ∩ V).Nonempty) (h₂ : (S \ V).Nonempty) :
    (S ∩ frontier V).Nonempty := by
  by_contra hcon
  have hsub : S ⊆ interior V ∪ (closure V)ᶜ := fun x hx ↦ by
    by_cases hc : x ∈ closure V
    · exact Or.inl (by_contra fun hi ↦ hcon ⟨x, hx, hc, hi⟩)
    · exact Or.inr hc
  rcases hS.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left (interior_subset.trans subset_closure)) hsub with h | h
  · obtain ⟨x, hxS, hxV⟩ := h₂
    exact hxV (interior_subset (h hxS))
  · obtain ⟨x, hxS, hxV⟩ := h₁
    exact h hxS (subset_closure hxV)
