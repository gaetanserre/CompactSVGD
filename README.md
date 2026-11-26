# CompactSVGD

A Lean 4 formalization of the theory of Stein Variational Gradient Descent (SVGD) on a compact
domain. It proves that, on a compact domain `Ω ⊆ ℝᵈ`, the continuous-time dynamics of SVGD
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

1. **`CompactSVGD/Utils/`**, the general mathematics that Mathlib or Tau Ceti do not have yet: the
   divergence of a vector field, global solutions of Lipschitz ODEs (built on Tau Ceti's
   `ODE.nonautonomousSolution`) and the Jacobian of their flows, Liouville's formula, Barbalat's
   lemma, the modulus of continuity, and the Kullback–Leibler divergence of a transported measure
   and along a flow. Nothing there mentions SVGD.
2. **`CompactSVGD/FeatureMap/`**, the lemmas on the vector fields `y ↦ (⟪hᵢ, Φ y⟫)ᵢ` of the
   elements `h` of `𝓗 = H₀ᵈ`, for a feature map `Φ : ℝᵈ → H₀`, and on the trajectories of the
   vector field of a curve in `𝓗`.
3. **`CompactSVGD/Paper.lean`**, the theory itself. Every definition, assumption and result appears
   there in a mathematical order, with a number (Assumption 1, Definition 2, Lemma 5, ...) given
   by its docstring, and every proof is commented, so that the file reads like a paper. The
   general results whose proof does not
   involve SVGD are proved in the two folders above and restated there. Schauder's fixed point
   theorem (Theorem 5) comes from Tau Ceti. The definitions used from
   `CompactSVGD/Definitions.lean` are recalled by `example`s proved by `rfl`.

All the definitions outside `Paper.lean` are gathered in `CompactSVGD/Definitions.lean`, so that
they can be checked by hand in one place. The other files only contain lemmas.

## Website

The results are presented on the website of the project,
[gaetanserre.fr/CompactSVGD](https://gaetanserre.fr/CompactSVGD/). It first shows the three main
results, Theorems 4, 6 and 7, with a map of their proofs. Then, it lists what they rest on, i.e. the
libraries, the axioms and the definitions to trust. Finally, the full development follows the order
of `Paper.lean`, and each result comes with its mathematical statement, a map or a sketch of its
proof, and its Lean statement and proof. The website is generated from
[`showcase/showcase.md`](showcase/showcase.md) by
[Showcase](https://github.com/gaetanserre/LeanShowcase). The API documentation is at
[gaetanserre.fr/CompactSVGD/docs](https://gaetanserre.fr/CompactSVGD/docs/).

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

Then build the project:

```bash
lake build
```

Tau Ceti's files will be compiled locally as downloading the whole cache would be too large.

## License

Apache 2.0. See [LICENSE](LICENSE).
