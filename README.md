# CompactSVGD

A Lean 4 formalization of the mean-field theory of Stein Variational Gradient Descent (SVGD) on a
compact domain `Ω ⊆ ℝᵈ`, following the theoretical appendix of the revised version of *Stein
Boltzmann Sampling* (Serré, Kalogeratos, Vayatis). The numbering is that of the AISTATS 2025
version. There is no `sorry`, the project only depends on Mathlib (branch `master`), and the code
follows the Mathlib style guidelines.

## Organization

To trust the results, one only needs to trust Mathlib, the definitions of
[`CompactSVGD/Definitions.lean`](CompactSVGD/Definitions.lean), and the definitions and statements
of [`CompactSVGD/Paper.lean`](CompactSVGD/Paper.lean): `lake comparator` checks the rest (see
below). The project has three parts.

1. **`CompactSVGD/ForMathlib/`**, the general mathematics that Mathlib does not have yet: the
   divergence of a vector field, global solutions of Lipschitz ODEs and the Jacobian of their
   flows, Liouville's formula, Barbalat's lemma, fixed points of causal maps, the two-point problem
   for a scalar linear ODE, and the Kullback–Leibler divergence along a flow. Nothing there mentions
   an object of the paper.
2. **`CompactSVGD/FeatureMap/`**, the lemmas on the vector fields `y ↦ (⟪hᵢ, Φ y⟫)ᵢ` of the
   elements `h` of the product RKHS `𝓗 = H₀ᵈ` of a feature map `Φ : ℝᵈ → H₀`, on the
   trajectories of the vector field of a curve in `𝓗`, and on the feature map `x ↦ (wₙ gₙ(x))ₙ ∈ ℓ²`
   of a sequence of functions.
3. **`CompactSVGD/Paper.lean`**, the paper itself. It follows the appendix, in its order: every
   definition and result of the paper appears there, with its proof. The only additions are the
   construction of the mean-field SVGD flow, which the AISTATS 2025 version assumes, the primed
   versions of the results along the flow, a Stein-universal kernel on `[-1, 1]` in the last
   section, and private technical lemmas. The docstrings give the
   paper's numbering and the proofs are commented, so that the file can be read alongside the paper.
   The hypotheses on the space, the target and the kernel are gathered in one structure,
   `SVGD.StandingAssumptions`. The definitions it uses from `CompactSVGD/Definitions.lean` are
   recalled by `example`s proved by `rfl`.

All the definitions outside `Paper.lean` are gathered in `CompactSVGD/Definitions.lean`, so that
they can be checked by hand in one place. The other files only contain lemmas.

The results on the Boltzmann distribution (Definition 2.1, Properties A.1, Theorems B.1 and B.2)
and the asymptotic convergence of SBS (Theorem 3.3) are not formalized.

## The results of the paper

All the declarations below are in [`CompactSVGD/Paper.lean`](CompactSVGD/Paper.lean).

| Paper | Lean |
|---|---|
| Standing assumptions (Section 3, Appendix A.2.1) | `SVGD.AdmissibleTarget`, `SVGD.AdmissibleFeatureMap`, `SVGD.StandingAssumptions` |
| Stein operator, Definition A.2 (Stein class) | `ProbabilityTheory.steinOperator`, `ProbabilityTheory.steinClass` |
| Lemma A.3 (Stein's identity) | `ProbabilityTheory.stein_identity` |
| `ξ`, `φ*_μ`, Definition A.5 (KSD `𝔎(μ ∣ π)`) | `SVGD.steinFeature`, `SVGD.direction`, `SVGD.kernelSteinDiscrepancy` (notation `𝔎[Φ, s] μ`) |
| Reproducing property | `SVGD.reproducing_property` |
| Lemma A.6 (regularity of `ξ`) | `SVGD.xi_regularity_*`, `SVGD.continuousOn_steinOperator` |
| Theorem A.7 (steepest trajectory) | `SVGD.steepest_trajectory_*` |
| Theorem A.8 (KL steepest descent) | `SVGD.klFirstVariation`, `SVGD.kl_steepest_descent_*` |
| Definition A.9 (Stein-universal kernel: the functions `𝒜_π f + c` are dense in `C(Ω, ℝ)`) | `SVGD.IsSteinUniversal` |
| Existence of the mean-field SVGD flow (assumed in the paper) | `SVGD.IsMeanFieldCurve`, `SVGD.exists_meanField`, `SVGD.meanFieldCurve`, `SVGD.meanFieldFlow`, `SVGD.meanFieldCurve_eq_direction`, `SVGD.meanFieldFlow_zero`, `SVGD.exists_homeomorph_meanFieldFlow`, `SVGD.hasDerivAt_meanFieldFlow` |
| Theorem A.11 (time derivative of the KL divergence) | `SVGD.time_derivative_kl`, `SVGD.time_derivative_kl_antitoneOn` |
| Proposition 3.2 (the KSD is a valid discrepancy) | `SVGD.ksd_valid_discrepancy` |
| Lemma B.4, Corollary B.5, Lemma B.6 | `SVGD.ksd_uniform_continuity`, `SVGD.ksd_convergence`, `SVGD.cluster_points` |
| **Theorem 3.1 (weak convergence of SVGD)** | `SVGD.weak_convergence` |
| A kernel with all the hypotheses of Theorem 3.1 on `[-1, 1]` (not in the paper) | `SVGD.intervalFeatureMap`, `SVGD.admissibleFeatureMap_intervalFeatureMap`, `SVGD.isSteinUniversal_intervalFeatureMap`, `SVGD.weak_convergence_intervalFeatureMap` |

The mean-field flow is described by the curve `m : ℝ → 𝓗` of its update directions: its trajectories
are `T_t = trajectory Φ m 0 · t`, and the mean-field equation is `m t = φ*_{μ_t}` for `t ≥ 0`
(`SVGD.IsMeanFieldCurve Φ s μ m`), where `μ_t = (T_t)#μ`. A solution exists
(`SVGD.exists_meanField`): it is built on each `[n, n + 1]` by Tonelli's delayed approximations and
the Arzelà–Ascoli theorem, without a Lipschitz condition on the score, so its uniqueness is not
claimed. `SVGD.meanFieldCurve Φ s μ` picks one solution and `SVGD.meanFieldFlow Φ s μ` is its flow.
Theorem A.11, Lemma B.4, Corollary B.5, Lemma B.6 and Theorem 3.1 are stated for this flow, so they
do not assume its existence. Their primed versions (such as `SVGD.weak_convergence'`) hold for every
solution `m` of the mean-field equation.

The last section of `CompactSVGD/Paper.lean` shows that the hypotheses of Theorem 3.1 can be met.
In dimension `1`, on `Ω = [-1, 1]`, the kernel `k(x, y) = ∑ₙ wₙ² χ(x) Rₙ(x) χ(y) Rₙ(y)` is admissible
and Stein-universal for every score continuous on `Ω`. Here `Rₙ` is the primitive of `tⁿ - mₙ`
that vanishes at `±1`, `χ` is a smooth cutoff equal to `1` on `[-2, 2]`, and `wₙ > 0`. The proof of
Stein-universality solves the Stein equation `σ u + u' = φ - c` with `u(±1) = 0`, then approximates
`u'` by a polynomial (Weierstrass). Thus `SVGD.weak_convergence_intervalFeatureMap` is Theorem 3.1 on
`[-1, 1]` with no hypothesis on the kernel. Kernels in dimension `d ≥ 2` are not formalized.

## Checking the statements with `comparator`

`CompactSVGD/Paper.lean` is the solution of a `lake comparator` challenge. The challenge,
[`CompactSVGDChallenge/Paper.lean`](CompactSVGDChallenge/Paper.lean), is the same file with the
proof of every theorem replaced by `sorry`. Its definitions and statements are copied verbatim. It
is generated, together with the configuration [`comparator.json`](comparator.json), by

```bash
python3 scripts/make_challenge.py
```

`lake comparator` then checks that every theorem of the solution proves the statement of the
challenge, using only the axioms `propext`, `Quot.sound` and `Classical.choice`. It needs Linux with
`bubblewrap`, and a clean build of the project. The challenge only has the public imports of the
solution: Mathlib and `CompactSVGD/Definitions.lean`. The `example`s of the solution are copied too,
so building the challenge also checks them.
The CI checks that the challenge is up to date and builds it.

```bash
lake comparator
```

## Build

Fetch Mathlib's compiled files, then build:

```bash
lake exe cache get
```

```bash
lake build
```

## License

Apache 2.0. See [LICENSE](LICENSE).
