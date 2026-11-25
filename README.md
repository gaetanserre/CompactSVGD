# CompactSVGD

A Lean 4 formalization of the paper *Stein Variational Gradient Descent on a compact domain*
(G. Serré). It proves that, on a compact domain `Ω ⊆ ℝᵈ`, the continuous-time dynamics of SVGD
exists, that the time derivative of the Kullback–Leibler divergence to the target is minus the
kernelized Stein discrepancy, and that the dynamics converges weakly to the target when the kernel
is Stein-universal. There is no
`sorry`. The project depends on Mathlib and on [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
(branch `main`, which pins Mathlib), and the code follows the Mathlib style guidelines.

## Organization

To trust the results, one only needs to trust Mathlib, the definitions of
[`CompactSVGD/Definitions.lean`](CompactSVGD/Definitions.lean), and the definitions and statements
of [`CompactSVGD/Paper.lean`](CompactSVGD/Paper.lean): `lake comparator` checks the rest (see
below). The project has three parts.

1. **`CompactSVGD/ForMathlib/`**, the general mathematics that Mathlib does not have yet: the
   divergence of a vector field, global solutions of Lipschitz ODEs (built on Tau Ceti's
   `ODE.nonautonomousSolution`) and the Jacobian of their flows, Liouville's formula, Barbalat's
   lemma, the modulus of continuity, and the Kullback–Leibler divergence of a transported measure
   and along a flow. Nothing there mentions an object of the paper.
2. **`CompactSVGD/FeatureMap/`**, the lemmas on the vector fields `y ↦ (⟪hᵢ, Φ y⟫)ᵢ` of the
   elements `h` of `𝓗 = H₀ᵈ`, for a feature map `Φ : ℝᵈ → H₀`, and on the trajectories of the
   vector field of a curve in `𝓗`.
3. **`CompactSVGD/Paper.lean`**, the paper itself. It follows the paper section by section: every
   definition, assumption and result appears there in the paper's order, under the paper's name,
   with the paper's proof. The docstrings give the paper's numbering and the proofs are commented,
   so that the file can be read alongside the paper. The general results whose proof does not
   involve SVGD are proved in the two folders above and restated there. Schauder's fixed point
   theorem (Theorem 5) comes from Tau Ceti. The definitions used from
   `CompactSVGD/Definitions.lean` are recalled by `example`s proved by `rfl`.

All the definitions outside `Paper.lean` are gathered in `CompactSVGD/Definitions.lean`, so that
they can be checked by hand in one place. The other files only contain lemmas.

## The results of the paper

All the declarations below are in the namespace `SVGD` of
[`CompactSVGD/Paper.lean`](CompactSVGD/Paper.lean), except `ProbabilityTheory.steinOperator`.

| Paper | Lean |
|---|---|
| Assumption 1 (Target distribution) | `TargetAssumption` |
| Definition 1 (Stein operator) | `ProbabilityTheory.steinOperator` |
| Lemma 1 (Perturbations of the identity) | `perturbations_of_identity_*` |
| Lemma 2 (Transport of the Kullback–Leibler divergence) | `transport_kl`, `transport_kl_ne_top` |
| Theorem 1 (First variation of the Kullback–Leibler divergence) | `first_variation`, `first_variation_*` |
| Corollary 1 (Stein's identity for the target distribution) | `stein_identity`, `stein_identity_integrable` |
| Assumption 2 (Kernel), the standing assumptions | `KernelAssumption`, `StandingAssumptions` |
| Definition 2 (Kernelized Stein discrepancy `𝔎(ρ ∣ π)`) | `kernelSteinDiscrepancy` (notation `𝔎[Φ, s] ρ`) |
| Lemma 3 (Stein feature), Lemma 4 (Regularity of `ξ`) | `steinFeature`, `stein_feature`, `xi_regularity_*` |
| Theorem 2 (Stein witness) | `steinWitness`, `stein_witness`, `stein_witness_*` |
| Theorem 3 (KL steepest descent) | `klFirstVariation`, `kl_steepest_descent_*` |
| Equation (3), its solutions | `drift`, `IsSolution` |
| **Theorem 4 (Existence of the continuous-time dynamics)** | `exists_continuous_time_dynamics` |
| Lemma 5 (Positions for a given drift) | `positions_*` |
| Lemma 6 (Set of the Stein witnesses), Equation (4) | `witnessSet`, `witness_set_*`, `fixedPointMap`, `IsConsistent` |
| Lemma 7 (A consistent candidate gives a solution) | `consistent_candidate_isSolution` |
| Equation (5), Theorem 5 (Schauder) | `dist_steinWitness_map_le`, `schauder` |
| Lemma 8 (A consistent candidate on a bounded time interval) | `consistent_candidate_bounded_interval` |
| Lemma 9 (Properties of the solutions) | `witnessCurve`, `solution_properties_*` |
| Lemma 10 (Jacobian of `T_t`) | `jacobian_*` |
| **Theorem 6 (Time derivative of the KL divergence)** | `time_derivative_kl`, `time_derivative_kl_*` |
| Equations (8) and (9), Definition 3 (Stein-universal kernel) | `ksd_eq_zero_iff`, `steinWitness_eq_zero_iff`, `IsSteinUniversal`, `isSteinUniversal_iff`, `isSteinUniversal_iff_mean` |
| Proposition 1 (The KSD vanishes only at `π`) | `ksd_vanishes_only_at_target` |
| Lemma 11 (Barbalat), Lemma 12 (Uniform continuity of the KSD) | `barbalat`, `ksd_uniform_continuity`, `ksd_uniform_continuity_le` |
| Corollary 2 (Convergence of the KSD), Lemma 13 (Limit points have a zero KSD) | `ksd_convergence`, `limit_points_ksd_eq_zero` |
| **Theorem 7 (Convergence to the target distribution)** | `convergence_to_target` |

The existence proof follows the paper. A candidate drift `m` gives the positions `T^m_t` of the
particles (Lemma 5), and these positions give a new drift `G(m)(t) = φ*_{(T^m_t)#ρ₀}`. On a bounded
time interval, `G` has a fixed point by Schauder's theorem, on a convex set of curves that is
compact by the Arzelà–Ascoli theorem (Lemma 8). The fixed points on the intervals `[n, n + 1]` are
glued into a solution on `[0, ∞)` (Theorem 4). Its uniqueness is not claimed: Theorems 6 and 7 hold
for every solution.

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

Fetch Mathlib's compiled files:

```bash
lake exe cache get
```

The compiled files of Tau Ceti come from its public cache, described by a Lake configuration file
`.lake/tauceti-cache.toml`:

```toml
[[cache.service]]
name = "tauceti-public"
kind = "s3"
artifactEndpoint = "https://cache.taucetiproject.org/artifacts"
revisionEndpoint = "https://cache.taucetiproject.org/revisions"
```

Then fetch them and build:

```bash
LAKE_CONFIG=.lake/tauceti-cache.toml lake cache get --service tauceti-public --repo TauCetiProject/TauCeti --package TauCeti --mappings-only
```

```bash
LAKE_CONFIG=.lake/tauceti-cache.toml lake build
```

## License

Apache 2.0. See [LICENSE](LICENSE).
