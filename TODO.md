# TODO

Statements left to prove, planned `sorry`s and upstreaming candidates.

There is no `sorry` in the library `CompactSVGD`. The only `sorry`s are those of the comparator
challenge `CompactSVGDChallenge/Paper.lean`, one per theorem, by design.

## Mathematics

- [ ] Uniqueness of the mean-field SVGD flow, which needs a Lipschitz score.
- [x] A kernel with all the hypotheses of Theorem 3.1 in dimension `1`, on `[-1, 1]`
  (`SVGD.intervalFeatureMap`, `SVGD.isSteinUniversal_intervalFeatureMap`).
- [ ] Stein-universal kernels in dimension `d ≥ 2`: the weighted kernels `w(x) w(y) k₀(x, y)` on
  domains with a `C²` frontier of the notes on Theorem 3.1 (Hahn–Banach, Riesz–Markov, divergence
  theorem), or one weight per component on boxes, which needs a matrix-valued kernel.

## Upstreaming

- [ ] Mathlib candidates, all in `CompactSVGD/ForMathlib/`:
  - analysis: Barbalat's lemma, the two-sided Grönwall inequality and `gronwallBound_δ0`, the
    global solutions of Lipschitz ODEs (`Analysis/ODE/Global.lean`), the invariance results, the
    fixed points of causal maps on curves (`Topology/ContinuousMap/Bounded/Causal.lean`), the
    differentiability and the Jacobian of flows (`Analysis/ODE/`), `divergence`,
    `ContinuousLinearMap.contDiff_det` and Jacobi's formula at the identity, Liouville's formula,
    `LipschitzWith.exists_homeomorph_id_add` and the invariance of a set under it, the maximizer of
    `⟪·, v⟫` on the unit ball, `IsCompact.closedConvexHull`, the derivative of `log ∘ p` along a
    curve, the two-point problem `exists_hasDerivAt_sub_sub_mul`;
  - linear algebra and topology: `ContinuousLinearMap.traceCLM`,
    `IsPreconnected.inter_frontier_nonempty`, `continuous_of_eqOn_Icc_nat`;
  - measure theory and information theory: `measurable_det_fderiv`,
    `ContinuousOn.integrable_of_ae_mem`, `MeasureTheory.dist_integral_map_le`,
    `MeasureTheory.ae_withDensity_restrict_mem`, `MeasureTheory.ae_map_subtypeVal_mem`,
    `InformationTheory.ae_of_klDiv_ne_top`, `MeasurableEmbedding.klDiv_map`,
    `MeasurableEquiv.klDiv_map_left` and the Kullback–Leibler divergence of a transported measure.

  The definitions to upstream are the general ones of `CompactSVGD/Definitions.lean`: `divergence`,
  `ContinuousLinearMap.traceCLM` and `ODE.globalSolution`.
- [ ] Check Mathlib for these declarations after each update (`find_existing.py`).

## Comparator

- [ ] Regenerate the challenge (`python3 scripts/make_challenge.py`) after every change of
  `CompactSVGD/Paper.lean`, and run `lake comparator` on Linux from a clean build.
