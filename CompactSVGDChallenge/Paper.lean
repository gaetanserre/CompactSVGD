/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Stein Variational Gradient Descent on a compact domain

This file develops the theory of Stein Variational Gradient Descent (SVGD) on a compact domain
`Ω ⊆ ℝᵈ`: the continuous-time dynamics of SVGD exists, the Kullback–Leibler divergence to the
target decreases along it at the rate of the kernelized Stein discrepancy, and the dynamics
converges weakly to the target when the kernel is Stein-universal. The main definitions,
assumptions and results are numbered, with one counter per kind (Assumption 1, Definition 2,
Lemma 5, ...), and their proofs are commented.

Theorems 4, 6 and 7 are numbered where they are announced, but stated after the lemmas of their
proof. The general results whose proof does not involve SVGD (Lemmas 1 and 2, Theorems 1 and 5,
Lemma 11, and the computations behind Lemma 10 and Theorem 6) are proved in
`CompactSVGD/Utils/` and `CompactSVGD/FeatureMap/`, and restated here. Schauder's fixed point
theorem (Theorem 5) comes from Tau Ceti.

The general definitions (divergence, global solutions of ODEs, vector fields of a feature map and
their trajectories, modulus of continuity) are in `CompactSVGD/Definitions.lean`; those used in the
statements are recalled here by `example`s proved by `rfl`.

## Main statements

* `SVGD.exists_continuous_time_dynamics`: **Theorem 4**, the continuous-time dynamics of SVGD
  exists.
* `SVGD.time_derivative_kl`: **Theorem 6**, `d/dt KL(ρ_t ‖ π) = -𝔎(ρ_t ∣ π)`.
* `SVGD.convergence_to_target`: **Theorem 7**, `ρ_t` converges weakly to `π` when the kernel is
  Stein-universal.

## Notation

| Mathematics | Lean |
|---|---|
| `ℝᵈ`, `λ` | `EuclideanSpace ℝ (Fin d)`, `volume` |
| `Ω°`, `∂Ω` | `interior Ω`, `frontier Ω` |
| `ρ ∈ 𝒫(Ω)` | `[IsProbabilityMeasure ρ]` and `∀ᵐ x ∂ρ, x ∈ Ω` |
| `T#ρ`, `KL(ρ ‖ ρ')` | `ρ.map T`, `klDiv ρ ρ'` (with values in `[0, ∞]`) |
| `π = p · λ_Ω`, its score | `π`, `p`, `s` |
| `𝒜_s v` | `ProbabilityTheory.steinOperator s v` |
| `Φ`, `H₀`, `𝓗 = H₀ᵈ`, `f_Φ` | `Φ`, `H₀`, `𝓗[d, H₀]`, `toVectorField Φ f` |
| `𝔎(ρ ∣ π)` | `𝔎[Φ, s] ρ`, i.e. `SVGD.kernelSteinDiscrepancy Φ s ρ` |
| `ξ_x`, `φ*_ρ`, `b(x, ρ)` | `steinFeature Φ s x`, `steinWitness Φ s ρ`, `drift Φ s ρ x` |
| `h'_f(0)` | `SVGD.klFirstVariation Φ π ρ f` |
| `(T_t)_{t ≥ 0}` solves the continuous-time SVGD equation | `SVGD.IsSolution Φ s Ω ρ₀ T` |
| `T^m_t(x)`, for a candidate `m` | `trajectory Φ m 0 x t` |
| `G_{ρ₀}(m)`, `𝒲` | `fixedPointMap Φ s ρ₀ m`, `witnessSet Φ s Ω` |
| `ω` | `modulusOfContinuityOn (steinFeature Φ s) Ω` |
| `ρ_n ⇀ ρ` | `∀ g, ContinuousOn g Ω → Tendsto (fun n ↦ ∫ x, g x ∂ρ_n) atTop (𝓝 (∫ x, g x ∂ρ))` |

## Implementation notes

* The bound `B` of `‖ξ_x‖` on `Ω` (Lemma 4 (ii)) is any such bound, not necessarily
  `max_{x ∈ Ω} ‖ξ_x‖`.
* A curve `m : [0, ∞) → 𝓗` is a curve `m : ℝ → 𝓗` whose values at negative times do not matter,
  and a family `(T_t)_{t ≥ 0}` is a map `T : ℝ → ℝᵈ → ℝᵈ`. The curve of the Stein witnesses of a
  solution is extended to negative times by its value at `0` (`SVGD.witnessCurve`), as in the
  proof of Lemma 10.
* The witness estimate (`SVGD.dist_steinWitness_map_le`) assumes `‖ψ₁(x) - ψ₂(x)‖ ≤ r` for
  `ρ`-almost every `x`, which is weaker than `sup_{x ∈ Ω} ‖ψ₁(x) - ψ₂(x)‖ ≤ r`.
* Lemma 10 states that `T_t` is differentiable. The continuity of `DT_t` is not formalized: the
  proof of Theorem 6 only needs the measurability of `x ↦ log det DT_t(x)`.
* The integrability parts of Theorem 1 and Corollary 1 (`SVGD.first_variation_integrable`,
  `SVGD.stein_identity_integrable`) assume neither that `v` is Lipschitz nor that `v = 0` on `∂Ω`:
  their proofs do not use these hypotheses.
* Lemma 13 (`SVGD.limit_points_ksd_eq_zero`) does not assume `ρ_∞ ∈ 𝒫(Ω)`. In the informal
  statement, this hypothesis makes the weak convergence and `E_{x ∼ ρ_∞}[𝒜_s f_Φ(x)]` meaningful.
  Here, the weak convergence is the hypothesis `hconv` on the integrals, and a Bochner integral is
  always defined.

## References

* [Q. Liu, D. Wang, *Stein Variational Gradient Descent*][Liu2016SVGD]
* [Q. Liu, J. Lee, M. Jordan, *A Kernelized Stein Discrepancy for Goodness-of-fit Tests*][Liu2016]
* [Q. Liu, *Stein Variational Gradient Descent as Gradient Flow*][Liu2017]
* [J. Schauder, *Der Fixpunktsatz in Funktionalräumen*][Schauder1930]
* [P. Billingsley, *Convergence of Probability Measures*][Billingsley1999]
* [H. K. Khalil, *Nonlinear Systems*][Khalil2002]
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InformationTheory ProbabilityTheory

open scoped NNReal ENNReal RealInnerProductSpace BoundedContinuousFunction

noncomputable section

/-! ## Setting -/

namespace SVGD

variable {d : ℕ}

/-- **Assumption 1 (Target distribution).** The target distribution `π = p · λ_Ω` has the density
`p` with respect to the Lebesgue measure on `Ω`, and the score `s`:
1. `π` is a probability measure;
2. `p` is measurable and continuous on `Ω`, and `p(x) > 0` for every `x ∈ Ω`;
3. for every `x ∈ Ω°`, `log p` is differentiable at `x` and `D(log p)(x) = s(x)`;
4. `s` is continuous on `Ω`. -/
structure TargetAssumption (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (π : Measure (EuclideanSpace ℝ (Fin d))) (p : EuclideanSpace ℝ (Fin d) → ℝ)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) : Prop where
  /-- `π = p · λ_Ω`. -/
  eq_withDensity : π = (volume.restrict Ω).withDensity fun x ↦ ENNReal.ofReal (p x)
  /-- (i) `π` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure π
  /-- (ii) `p` is measurable. -/
  measurable : Measurable p
  /-- (ii) `p` is continuous on `Ω`. -/
  continuousOn : ContinuousOn p Ω
  /-- (ii) `p` is positive on `Ω`. -/
  pos : ∀ x ∈ Ω, 0 < p x
  /-- (iii) `D(log p) = s` on `Ω°`. -/
  hasFDerivAt_log : ∀ x ∈ interior Ω, HasFDerivAt (fun y ↦ Real.log (p y)) (s x) x
  /-- (iv) `s` is continuous on `Ω`. -/
  continuousOn_score : ContinuousOn s Ω

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {π ρ : Measure (EuclideanSpace ℝ (Fin d))}
  {p : EuclideanSpace ℝ (Fin d) → ℝ}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}

/-- The target distribution is carried by `Ω`, i.e. `π(ℝᵈ \ Ω) = 0`. -/
theorem TargetAssumption.ae_mem (hπ : TargetAssumption Ω π p s) (hΩ : MeasurableSet Ω) :
    ∀ᵐ x ∂π, x ∈ Ω :=
  sorry

/-- Under Assumption 1, if `KL(ρ ‖ π) < ∞`, then `ρ` is carried by `Ω`. -/
theorem TargetAssumption.ae_mem_of_klDiv_ne_top (hπ : TargetAssumption Ω π p s)
    (hΩ : MeasurableSet Ω) (hKL : klDiv ρ π ≠ ∞) : ∀ᵐ x ∂ρ, x ∈ Ω :=
  sorry

end SVGD

/-! ## Stein's method

### The Stein operator and Stein's identity -/

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 1 (Stein operator).** The Stein operator of score `s : E → E*` maps a vector field
`v : E → E` to the function `𝒜_s v(x) = s(x)(v(x)) + ∇ · v(x)`. It is meaningful at every `x` where
`v` is differentiable, and `E` is meant to be finite-dimensional. -/
def steinOperator (s : E → StrongDual ℝ E) (v : E → E) (x : E) : ℝ :=
  s x (v x) + divergence ℝ v x

/-- The divergence (`CompactSVGD/Definitions.lean`) is the trace of the derivative. -/
example (v : E → E) (x : E) : divergence ℝ v x = LinearMap.trace ℝ E (fderiv ℝ v x) :=
  rfl

end ProbabilityTheory

/-! ### First variation of the Kullback–Leibler divergence -/

namespace SVGD

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {π ρ ρ₀ : Measure (EuclideanSpace ℝ (Fin d))} {p : EuclideanSpace ℝ (Fin d) → ℝ}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {K_v B : ℝ≥0}
  {T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

private theorem nnnorm_mul_lt_one {ε : ℝ} {K : ℝ≥0} (hε : |ε| * K < 1) : ‖ε‖₊ * K < 1 :=
  sorry

section Perturbation

variable {ε : ℝ} (hv : LipschitzWith K_v v) (hε : |ε| * K_v < 1)
include hv hε

/-- **Lemma 1 (Perturbations of the identity)**, first part. Let `v` be `K_v`-Lipschitz and
`|ε| K_v < 1`. Then `Ψ = I_d + ε v` is a homeomorphism of `ℝᵈ`. -/
theorem perturbations_of_identity_isHomeomorph : IsHomeomorph fun x ↦ x + ε • v x :=
  sorry

/-- **Lemma 1 (Perturbations of the identity)**, second part. If moreover `v` vanishes on `∂Ω`,
then `Ψ(Ω) = Ω`. -/
theorem perturbations_of_identity_image (hv₀ : ∀ y ∈ frontier Ω, v y = 0) :
    (fun x ↦ x + ε • v x) '' Ω = Ω :=
  sorry

/-- **Lemma 1 (Perturbations of the identity)**, third part. If moreover `v` vanishes on `∂Ω`,
then `Ψ(Ω°) = Ω°`. -/
theorem perturbations_of_identity_image_interior (hv₀ : ∀ y ∈ frontier Ω, v y = 0) :
    (fun x ↦ x + ε • v x) '' interior Ω = interior Ω :=
  sorry

end Perturbation

section Transport

variable [IsProbabilityMeasure ρ] {Ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
  (hΩ : IsCompact Ω) (hπ : TargetAssumption Ω π p s) (hΨ : IsHomeomorph Ψ)
  (hΨd : ∀ x ∈ Ω, DifferentiableAt ℝ Ψ x) (hΨΩ : Ψ '' Ω = Ω)
  (hdet : ∀ x ∈ Ω, 0 < (fderiv ℝ Ψ x).det) (hKL : klDiv ρ π ≠ ∞)
  (hlog : Integrable (fun x ↦ Real.log (fderiv ℝ Ψ x).det) ρ)
include hΩ hπ hΨ hΨd hΨΩ hdet hKL hlog

/-- **Lemma 2 (Transport of the Kullback–Leibler divergence)**, first part. Suppose that
Assumption 1 holds. Let `Ψ` be a homeomorphism of `ℝᵈ`, differentiable at every point of `Ω`, such
that `Ψ(Ω) = Ω` and `det DΨ > 0` on `Ω`. Let `ρ` be a probability measure with `KL(ρ ‖ π) < ∞`
such that `log det DΨ` is `ρ`-integrable. Then, `KL(Ψ#ρ ‖ π) < ∞`. -/
theorem transport_kl_ne_top : klDiv (ρ.map Ψ) π ≠ ∞ :=
  sorry

/-- **Lemma 2 (Transport of the Kullback–Leibler divergence)**, second part. Under the same
assumptions, `KL(Ψ#ρ ‖ π) = KL(ρ ‖ π) - ∫ (log p(Ψ(x)) - log p(x) + log det DΨ(x)) dρ(x)`. -/
theorem transport_kl :
    (klDiv (ρ.map Ψ) π).toReal = (klDiv ρ π).toReal -
      ∫ x, (Real.log (p (Ψ x)) - Real.log (p x) + Real.log (fderiv ℝ Ψ x).det) ∂ρ :=
  sorry

end Transport

section FirstVariation

variable [IsProbabilityMeasure ρ] (hΩ : IsCompact Ω) (hπ : TargetAssumption Ω π p s)
  (hv : ContDiff ℝ 1 v) (hvK : LipschitzWith K_v v) (hv₀ : ∀ y ∈ frontier Ω, v y = 0)
  (hKL : klDiv ρ π ≠ ∞)
include hΩ hπ hv hvK hv₀ hKL

omit hvK hv₀ in
/-- **Theorem 1 (First variation of the Kullback–Leibler divergence)**, integrability. Suppose
that Assumption 1 holds. Let `v` be `C¹` and `K_v`-Lipschitz, with `v = 0` on `∂Ω`, and let `ρ` be a
probability measure with `KL(ρ ‖ π) < ∞`. Then, `𝒜_s v` is `ρ`-integrable. -/
theorem first_variation_integrable : Integrable (steinOperator s v) ρ :=
  sorry

/-- **Theorem 1 (First variation of the Kullback–Leibler divergence)**, finiteness. Under the same
assumptions, there is `ε₀ > 0` such that `KL((I_d + ε v)#ρ ‖ π) < ∞` for every `ε ∈ (-ε₀, ε₀)`. -/
theorem first_variation_ne_top :
    ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Ioo (-ε₀) ε₀, klDiv (ρ.map fun x ↦ x + ε • v x) π ≠ ∞ :=
  sorry

/-- **Theorem 1 (First variation of the Kullback–Leibler divergence)**, derivative. Under the same
assumptions, `h : ε ↦ KL((I_d + ε v)#ρ ‖ π)` is differentiable at `0`, and
`h'(0) = -E_{x ∼ ρ}[𝒜_s v(x)]`. -/
theorem first_variation :
    HasDerivAt (fun ε : ℝ ↦ (klDiv (ρ.map fun x ↦ x + ε • v x) π).toReal)
      (-∫ x, steinOperator s v x ∂ρ) 0 :=
  sorry

end FirstVariation

section SteinIdentity

variable (hΩ : IsCompact Ω) (hπ : TargetAssumption Ω π p s) (hv : ContDiff ℝ 1 v)
  (hvK : LipschitzWith K_v v) (hv₀ : ∀ y ∈ frontier Ω, v y = 0)
include hΩ hπ hv hvK hv₀

omit hvK hv₀ in
/-- **Corollary 1 (Stein's identity for the target distribution)**, integrability. Suppose that
Assumption 1 holds, and let `v` be `C¹` and Lipschitz, with `v = 0` on `∂Ω`. Then, `𝒜_s v` is
`π`-integrable. -/
theorem stein_identity_integrable : Integrable (steinOperator s v) π :=
  sorry

/-- **Corollary 1 (Stein's identity for the target distribution).** Under the same assumptions,
`E_{x ∼ π}[𝒜_s v(x)] = 0`. -/
theorem stein_identity : ∫ x, steinOperator s v x ∂π = 0 :=
  sorry

end SteinIdentity

/-! ### The Stein discrepancy

The Stein discrepancy `𝕊(ρ, π) = sup_{v ∈ 𝓕} E_{x ∼ ρ}[𝒜_s v(x)]` is only used through its
kernelized version, `SVGD.kernelSteinDiscrepancy` (Definition 2). -/

/-! ## The kernelized Stein discrepancy

### The kernel -/

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]

/-- **Assumption 2 (Kernel).** The kernel is `k(x, y) = ⟪Φ(x), Φ(y)⟫_{H₀}`, for a feature map
`Φ : ℝᵈ → H₀` with values in a real Hilbert space `H₀`:
1. `Φ` is continuously differentiable on `ℝᵈ`;
2. `Φ` is `K`-Lipschitz;
3. `‖Φ(y)‖ ≤ C` for every `y ∈ ℝᵈ`;
4. `Φ(y) = 0` for every `y ∈ ∂Ω`. -/
structure KernelAssumption (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (K C : ℝ≥0) : Prop where
  /-- (i) `Φ` is continuously differentiable. -/
  contDiff : ContDiff ℝ 1 Φ
  /-- (ii) `Φ` is `K`-Lipschitz. -/
  lipschitzWith : LipschitzWith K Φ
  /-- (iii) `Φ` is bounded by `C`. -/
  norm_le : ∀ y, ‖Φ y‖ ≤ C
  /-- (iv) `Φ` vanishes on `∂Ω`. -/
  eq_zero_of_mem_frontier : ∀ y ∈ frontier Ω, Φ y = 0

/-- The space `𝓗 = H₀ᵈ` (`CompactSVGD/Definitions.lean`), with
`⟪f, g⟫_𝓗 = ∑ᵢ ⟪fᵢ, gᵢ⟫_{H₀}`. -/
example : 𝓗[d, H₀] = PiLp 2 fun _ : Fin d ↦ H₀ :=
  rfl

/-- The vector field `f_Φ(y) = (⟪f₁, Φ(y)⟫, ..., ⟪f_d, Φ(y)⟫)` of `f ∈ 𝓗`, i.e. `f_Φ = P_f ∘ Φ`. -/
example (Φ : EuclideanSpace ℝ (Fin d) → H₀) (f : 𝓗[d, H₀]) (y : EuclideanSpace ℝ (Fin d)) :
    toVectorField Φ f y = WithLp.toLp 2 fun i ↦ ⟪f i, Φ y⟫ :=
  rfl

variable {Φ : EuclideanSpace ℝ (Fin d) → H₀} {K C : ℝ≥0}

/-- By (i) of Assumption 2, every vector field `f_Φ` is continuously differentiable. -/
theorem KernelAssumption.contDiff_toVectorField (hΦ : KernelAssumption Φ Ω K C)
    (f : 𝓗[d, H₀]) : ContDiff ℝ 1 (toVectorField Φ f) :=
  sorry

/-- By (ii) of Assumption 2, `f_Φ` is `‖f‖ K`-Lipschitz. -/
theorem KernelAssumption.lipschitzWith_toVectorField (hΦ : KernelAssumption Φ Ω K C)
    (f : 𝓗[d, H₀]) : LipschitzWith (‖f‖₊ * K) (toVectorField Φ f) :=
  sorry

/-- By (iv) of Assumption 2, `f_Φ` vanishes on `∂Ω`. -/
theorem KernelAssumption.toVectorField_eq_zero (hΦ : KernelAssumption Φ Ω K C)
    (f : 𝓗[d, H₀]) : ∀ y ∈ frontier Ω, toVectorField Φ f y = 0 :=
  sorry

/-- **The standing assumptions**: `Ω` is compact, and Assumptions 1 and 2 hold. -/
structure StandingAssumptions (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (π : Measure (EuclideanSpace ℝ (Fin d))) (p : EuclideanSpace ℝ (Fin d) → ℝ)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (Φ : EuclideanSpace ℝ (Fin d) → H₀) (K C : ℝ≥0) : Prop where
  /-- The domain `Ω` is compact. -/
  isCompact : IsCompact Ω
  /-- Assumption 1 (Target distribution). -/
  target : TargetAssumption Ω π p s
  /-- Assumption 2 (Kernel). -/
  kernel : KernelAssumption Φ Ω K C

theorem StandingAssumptions.measurableSet (hS : StandingAssumptions Ω π p s Φ K C) :
    MeasurableSet Ω :=
  sorry

/-! ### Definition of the kernelized Stein discrepancy -/

/-- **Definition 2 (Kernelized Stein discrepancy).**
`𝔎(ρ ∣ π) = sup_{f ∈ 𝓗, ‖f‖ ≤ 1} E_{x ∼ ρ}[𝒜_s f_Φ(x)]²`. The supremum is a real supremum, hence
`0` if the family is unbounded. It is finite for `ρ ∈ 𝒫(Ω)` (Theorem 2). -/
def kernelSteinDiscrepancy (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⨆ f : closedBall (0 : 𝓗[d, H₀]) 1, (∫ x, steinOperator s (toVectorField Φ f) x ∂ρ) ^ 2

/-- The kernelized Stein discrepancy `𝔎(ρ ∣ π)`, written `𝔎[Φ, s] ρ`: it depends on the target `π`
only through its score `s`. -/
scoped notation "𝔎[" Φ ", " s "]" => kernelSteinDiscrepancy Φ s

/-- The kernelized Stein discrepancy is nonnegative. -/
theorem ksd_nonneg (ρ : Measure (EuclideanSpace ℝ (Fin d))) : 0 ≤ 𝔎[Φ, s] ρ :=
  sorry

/-- For `f ∈ 𝓗`, `𝒜_s f_Φ` is continuous on `Ω`. -/
theorem continuousOn_steinOperator (hS : StandingAssumptions Ω π p s Φ K C) (f : 𝓗[d, H₀]) :
    ContinuousOn (steinOperator s (toVectorField Φ f)) Ω :=
  sorry

/-- `𝔎(π ∣ π) = 0`, by Corollary 1. -/
theorem ksd_target_eq_zero (hS : StandingAssumptions Ω π p s Φ K C) : 𝔎[Φ, s] π = 0 :=
  sorry

/-! ### The Stein witness -/

/-- The **Stein feature** `ξ_x ∈ 𝓗` of `x`, with components `(ξ_x)ᵢ = s(x)(eᵢ) Φ(x) + DΦ(x)(eᵢ)`. -/
def steinFeature (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : 𝓗[d, H₀] :=
  WithLp.toLp 2 fun i ↦
    s x (EuclideanSpace.single i 1) • Φ x + fderiv ℝ Φ x (EuclideanSpace.single i 1)

/-- **Lemma 3 (Stein feature).** Suppose that the standing assumptions hold. Then,
`𝒜_s f_Φ(x) = ⟪f, ξ_x⟫_𝓗` for all `x ∈ ℝᵈ` and `f ∈ 𝓗`. -/
theorem stein_feature (hS : StandingAssumptions Ω π p s Φ K C) (x : EuclideanSpace ℝ (Fin d))
    (f : 𝓗[d, H₀]) : steinOperator s (toVectorField Φ f) x = ⟪f, steinFeature Φ s x⟫ :=
  sorry

section XiRegularity

variable (hS : StandingAssumptions Ω π p s Φ K C)
include hS

/-- **Lemma 4 (Regularity of `ξ`)**, (i). The map `x ↦ ξ_x` is uniformly continuous from `Ω` to
`𝓗`. -/
theorem xi_regularity_uniformContinuousOn : UniformContinuousOn (steinFeature Φ s) Ω :=
  sorry

/-- **Lemma 4 (Regularity of `ξ`)**, (ii). `‖ξ_x‖` is bounded on `Ω`. -/
theorem xi_regularity_exists_bound : ∃ B : ℝ≥0, ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B :=
  sorry

/-- The image of `Ω` by `x ↦ ξ_x` is compact. -/
theorem isCompact_image_steinFeature : IsCompact (steinFeature Φ s '' Ω) :=
  sorry

/-- **Lemma 4 (Regularity of `ξ`)**, (iii). For every `ρ ∈ 𝒫(Ω)`, `x ↦ ξ_x` is `ρ`-integrable. -/
theorem xi_regularity_integrable [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) :
    Integrable (steinFeature Φ s) ρ :=
  sorry

end XiRegularity

/-- The **Stein witness** `φ*_ρ = E_{x ∼ ρ}[ξ_x]` of `ρ`, a Bochner integral in `𝓗`
(Theorem 2). -/
def steinWitness (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) : 𝓗[d, H₀] :=
  ∫ x, steinFeature Φ s x ∂ρ

section SteinWitness

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ]
  (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
include hS hρ

/-- **Theorem 2 (Stein witness)**, existence. Suppose that the standing assumptions hold, and let
`ρ ∈ 𝒫(Ω)`. Then, `E_{x ∼ ρ}[𝒜_s f_Φ(x)] = ⟪f, φ*_ρ⟫_𝓗` for every `f ∈ 𝓗`. -/
theorem stein_witness (f : 𝓗[d, H₀]) :
    ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ = ⟪f, steinWitness Φ s ρ⟫ :=
  sorry

/-- **Theorem 2 (Stein witness)**, uniqueness. Under the same assumptions, `φ*_ρ` is the only
`f' ∈ 𝓗` such that `E_{x ∼ ρ}[𝒜_s f_Φ(x)] = ⟪f, f'⟫_𝓗` for every `f ∈ 𝓗`. -/
theorem stein_witness_unique {f' : 𝓗[d, H₀]}
    (hf' : ∀ f, ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ = ⟪f, f'⟫) :
    f' = steinWitness Φ s ρ :=
  sorry

/-- **Theorem 2 (Stein witness)**, (i). On the closed unit ball of `𝓗`, the function
`f ↦ E_{x ∼ ρ}[𝒜_s f_Φ(x)]` reaches its maximum at `f* = φ*_ρ / ‖φ*_ρ‖_𝓗`, which is `0` when
`φ*_ρ = 0`. -/
theorem stein_witness_isMaxOn :
    IsMaxOn (fun f : 𝓗[d, H₀] ↦ ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ)
      (closedBall 0 1) (‖steinWitness Φ s ρ‖⁻¹ • steinWitness Φ s ρ) :=
  sorry

/-- **Theorem 2 (Stein witness)**, (ii). `𝔎(ρ ∣ π) = ‖φ*_ρ‖²_𝓗`. -/
theorem stein_witness_ksd : 𝔎[Φ, s] ρ = ‖steinWitness Φ s ρ‖ ^ 2 :=
  sorry

/-- **Theorem 2 (Stein witness)**, (ii). `𝔎(ρ ∣ π) = E_{x ∼ ρ}[𝒜_s (φ*_ρ)_Φ(x)]`. -/
theorem stein_witness_ksd_eq_integral :
    𝔎[Φ, s] ρ = ∫ x, steinOperator s (toVectorField Φ (steinWitness Φ s ρ)) x ∂ρ :=
  sorry

/-- `E_{x ∼ ρ}[𝒜_s f_Φ(x)]² ≤ 𝔎(ρ ∣ π)` for every `f` of the closed unit ball of `𝓗`
(Definition 2). -/
theorem sq_integral_steinOperator_le_ksd {f : 𝓗[d, H₀]} (hf : ‖f‖ ≤ 1) :
    (∫ x, steinOperator s (toVectorField Φ f) x ∂ρ) ^ 2 ≤ 𝔎[Φ, s] ρ :=
  sorry

end SteinWitness

/-- `‖φ*_ρ‖_𝓗 ≤ B` for `ρ ∈ 𝒫(Ω)`, where `B` bounds `‖ξ_x‖_𝓗` on `Ω`. -/
theorem norm_steinWitness_le (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) : ‖steinWitness Φ s ρ‖ ≤ B :=
  sorry

/-- `‖(φ*_ρ)_Φ(y)‖ ≤ B C` for `ρ ∈ 𝒫(Ω)` and `y ∈ ℝᵈ`. -/
theorem norm_toVectorField_steinWitness_le (hS : StandingAssumptions Ω π p s Φ K C)
    (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
    (y : EuclideanSpace ℝ (Fin d)) : ‖toVectorField Φ (steinWitness Φ s ρ) y‖ ≤ B * C :=
  sorry

/-- The Stein witness of `π` vanishes, as `𝔎(π ∣ π) = 0`. -/
theorem steinWitness_target_eq_zero [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C) :
    steinWitness Φ s π = 0 :=
  sorry

/-! ## The steepest descent of the KL divergence -/

/-- The first variation `h'_f(0)` of the Kullback–Leibler divergence to `π` at `ρ` along `f ∈ 𝓗`,
where `h_f(ε) = KL((I_d + ε f_Φ)#ρ ‖ π)`. It is `0` if `h_f` is not differentiable at `0`. -/
def klFirstVariation (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (π ρ : Measure (EuclideanSpace ℝ (Fin d))) (f : 𝓗[d, H₀]) : ℝ :=
  deriv (fun ε : ℝ ↦ (klDiv (ρ.map fun x ↦ x + ε • toVectorField Φ f x) π).toReal) 0

section KLSteepestDescent

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ]
  (hKL : klDiv ρ π ≠ ∞)
include hS hKL

omit [CompleteSpace H₀] in
/-- **Theorem 3 (KL steepest descent)**, (i), finiteness. Suppose that the standing assumptions
hold, and let `ρ` be a probability measure with `KL(ρ ‖ π) < ∞`. For every `f ∈ 𝓗`, `h_f` is
real-valued on a neighborhood of `0`. -/
theorem kl_steepest_descent_ne_top (f : 𝓗[d, H₀]) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), klDiv (ρ.map fun x ↦ x + ε • toVectorField Φ f x) π ≠ ∞ :=
  sorry

/-- **Theorem 3 (KL steepest descent)**, (i). For every `f ∈ 𝓗`, `h_f` is differentiable at `0`,
and `h'_f(0) = -⟪f, φ*_ρ⟫_𝓗`. -/
theorem kl_steepest_descent_hasDerivAt (f : 𝓗[d, H₀]) :
    HasDerivAt (fun ε : ℝ ↦ (klDiv (ρ.map fun x ↦ x + ε • toVectorField Φ f x) π).toReal)
      (-⟪f, steinWitness Φ s ρ⟫) 0 :=
  sorry

/-- **Theorem 3 (KL steepest descent)**, (i), as the first variation `h'_f(0) = -⟪f, φ*_ρ⟫_𝓗`. -/
theorem kl_steepest_descent_eq_inner (f : 𝓗[d, H₀]) :
    klFirstVariation Φ π ρ f = -⟪f, steinWitness Φ s ρ⟫ :=
  sorry

/-- **Theorem 3 (KL steepest descent)**, (ii). On the closed unit ball of `𝓗`, `f ↦ h'_f(0)`
reaches its minimum at `f* = φ*_ρ / ‖φ*_ρ‖_𝓗`, which is `0` when `φ*_ρ = 0`. -/
theorem kl_steepest_descent_isMinOn :
    IsMinOn (klFirstVariation Φ π ρ) (closedBall 0 1)
      (‖steinWitness Φ s ρ‖⁻¹ • steinWitness Φ s ρ) :=
  sorry

/-- **Theorem 3 (KL steepest descent)**, (ii), uniqueness. If `φ*_ρ ≠ 0`, then `f*` is the only
minimizer of `f ↦ h'_f(0)` on the closed unit ball of `𝓗`. -/
theorem kl_steepest_descent_eq (hφ : steinWitness Φ s ρ ≠ 0) {f : 𝓗[d, H₀]}
    (hf : f ∈ closedBall 0 1)
    (hmin : klFirstVariation Φ π ρ f =
      klFirstVariation Φ π ρ (‖steinWitness Φ s ρ‖⁻¹ • steinWitness Φ s ρ)) :
    f = ‖steinWitness Φ s ρ‖⁻¹ • steinWitness Φ s ρ :=
  sorry

/-- **Theorem 3 (KL steepest descent)**, (iii). `h'_{φ*_ρ}(0) = -𝔎(ρ ∣ π)`. -/
theorem kl_steepest_descent_ksd : klFirstVariation Φ π ρ (steinWitness Φ s ρ) = -𝔎[Φ, s] ρ :=
  sorry

end KLSteepestDescent

/-! ## SVGD in continuous time

### The continuous-time dynamics -/

/-- The **drift** `b(x, ρ) = (φ*_ρ)_Φ(x)` of the continuous-time dynamics: the velocity of a
particle located at `x` when the particles are distributed according to `ρ`. -/
def drift (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  toVectorField Φ (steinWitness Φ s ρ) x

/-- **A solution of the continuous-time SVGD equation** from `ρ₀`: a family `(T_t)_{t ≥ 0}` of
continuous maps from `ℝᵈ` to `ℝᵈ` such that `T_0 = I_d`, `ρ_t = (T_t)#ρ₀ ∈ 𝒫(Ω)` for every
`t ≥ 0`, and `d/dt T_t(x) = b(T_t(x), ρ_t)` for all `x ∈ ℝᵈ` and `t ≥ 0`, with a right derivative
at `t = 0`. -/
structure IsSolution (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (ρ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop where
  /-- Every `T_t` is continuous. -/
  continuous : ∀ t, 0 ≤ t → Continuous (T t)
  /-- `T_0 = I_d`. -/
  zero : T 0 = id
  /-- `ρ_t = (T_t)#ρ₀` is carried by `Ω`. -/
  ae_mem : ∀ t, 0 ≤ t → ∀ᵐ y ∂ρ₀.map (T t), y ∈ Ω
  /-- The continuous-time SVGD equation `d/dt T_t(x) = b(T_t(x), ρ_t)`, with a right derivative at
  `0`. -/
  hasDerivWithinAt : ∀ x t, 0 ≤ t →
    HasDerivWithinAt (T · x) (drift Φ s (ρ₀.map (T t)) (T t x)) (Ici 0) t

/-! ### Existence of a solution

Theorem 4 (Existence of the continuous-time dynamics), `SVGD.exists_continuous_time_dynamics`, is
proved below, after the lemmas of its proof.

### Strategy of the proof of Theorem 4

A **candidate** is a continuous and bounded curve `m : [0, ∞) → 𝓗`. At time `t`, it gives the
velocity `m(t)_Φ(y)` to a particle located at `y`. The position at time `t` of the particle that
starts from `x` is `T^m_t(x) = trajectory Φ m 0 x t` (`CompactSVGD/Definitions.lean`). -/

/-- The positions `T^m_t(x)` are the global solutions of `α' = m(t)_Φ(α)` with `α(0) = x`. -/
example (m : ℝ → 𝓗[d, H₀]) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m 0 x = ODE.integralCurveThrough (fun t ↦ toVectorField Φ (m t)) 0 x :=
  rfl

/-! ### From the drift to the positions -/

section Positions

variable (hS : StandingAssumptions Ω π p s Φ K C) {R : ℝ≥0} {m : ℝ → 𝓗[d, H₀]}
  (hm : Continuous m) (hmR : ∀ t, ‖m t‖ ≤ R)
include hS hm hmR

/-- **Lemma 5 (Positions for a given drift)**, existence. Suppose that the standing assumptions
hold, and let `m` be a continuous curve with `‖m(t)‖_𝓗 ≤ R`. Then, `t ↦ T^m_t(x)` solves
`d/dt T^m_t(x) = m(t)_Φ(T^m_t(x))`. -/
theorem positions_hasDerivAt (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (trajectory Φ m 0 x) (toVectorField Φ (m t) (trajectory Φ m 0 x t)) t :=
  sorry

/-- **Lemma 5 (Positions for a given drift)**, initial condition. `T^m_0(x) = x`. -/
theorem positions_zero (x : EuclideanSpace ℝ (Fin d)) : trajectory Φ m 0 x 0 = x :=
  sorry

/-- **Lemma 5 (Positions for a given drift)**, uniqueness. The solution of
`d/dt α(t) = m(t)_Φ(α(t))`, `α(0) = x`, is unique on `[0, ∞)`. -/
theorem positions_unique {α : ℝ → EuclideanSpace ℝ (Fin d)} {x : EuclideanSpace ℝ (Fin d)}
    (hα₀ : α 0 = x)
    (hα : ∀ t, 0 ≤ t → HasDerivWithinAt α (toVectorField Φ (m t) (α t)) (Ici 0) t) {t : ℝ}
    (ht : 0 ≤ t) : α t = trajectory Φ m 0 x t :=
  sorry

/-- **Lemma 5 (Positions for a given drift)**, (i). `T^m_t` is a homeomorphism of `ℝᵈ`. -/
theorem positions_isHomeomorph (t : ℝ) : IsHomeomorph (trajectory Φ m 0 · t) :=
  sorry

/-- **Lemma 5 (Positions for a given drift)**, (i). `T^m_t(Ω) = Ω`. -/
theorem positions_image (t : ℝ) : (trajectory Φ m 0 · t) '' Ω = Ω :=
  sorry

/-- **Lemma 5 (Positions for a given drift)**, (ii). `‖T^m_t(x) - T^m_{t'}(x)‖ ≤ R C |t - t'|`. -/
theorem positions_dist_le (x : EuclideanSpace ℝ (Fin d)) (t t' : ℝ) :
    dist (trajectory Φ m 0 x t) (trajectory Φ m 0 x t') ≤ R * C * |t - t'| :=
  sorry

/-- **Lemma 5 (Positions for a given drift)**, (iii). Let `m'` be another continuous curve with
`‖m'(t)‖_𝓗 ≤ R`. If `‖m(r) - m'(r)‖_𝓗 ≤ Δ` for `r ∈ [0, t]`, then
`‖T^m_t(x) - T^{m'}_t(x)‖ ≤ C t e^{R K t} Δ`. -/
theorem positions_dist_le_of_dist_le {m' : ℝ → 𝓗[d, H₀]} (hm' : Continuous m')
    (hmR' : ∀ t, ‖m' t‖ ≤ R) {t Δ : ℝ} (ht : 0 ≤ t) (hΔ : ∀ r ∈ Icc 0 t, dist (m r) (m' r) ≤ Δ)
    (x : EuclideanSpace ℝ (Fin d)) :
    dist (trajectory Φ m 0 x t) (trajectory Φ m' 0 x t) ≤ C * t * Real.exp (R * K * t) * Δ :=
  sorry

end Positions

/-! ### From the positions to the drift -/

/-- The map `G_{ρ₀}(m) : t ↦ φ*_{(T^m_t)#ρ₀}`, which sends a candidate `m` to the drift that SVGD
prescribes for the positions that `m` produces. -/
def fixedPointMap (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ₀ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → 𝓗[d, H₀]) (t : ℝ) : 𝓗[d, H₀] :=
  steinWitness Φ s (ρ₀.map (trajectory Φ m 0 · t))

/-- A candidate `m` is **consistent** when `m = G_{ρ₀}(m)`, i.e. `m(t) = φ*_{(T^m_t)#ρ₀}` for every
`t ≥ 0`, i.e. `m` is a fixed point of `G_{ρ₀}`. -/
def IsConsistent (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ₀ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → 𝓗[d, H₀]) : Prop :=
  ∀ t, 0 ≤ t → m t = fixedPointMap Φ s ρ₀ m t

/-- The set `𝒲` of Lemma 6: the closed convex hull of `{ξ_x | x ∈ Ω}` in `𝓗`. -/
def witnessSet (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set 𝓗[d, H₀] :=
  closedConvexHull ℝ (steinFeature Φ s '' Ω)

/-- **Lemma 6 (Set of the Stein witnesses)**, compactness. Suppose that the standing assumptions
hold. Then, `𝒲` is compact. -/
theorem witness_set_isCompact [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C) :
    IsCompact (witnessSet Φ s Ω) :=
  sorry

/-- **Lemma 6 (Set of the Stein witnesses)**, bound. `‖f‖_𝓗 ≤ B` for every `f ∈ 𝒲`, where `B`
bounds `‖ξ_x‖_𝓗` on `Ω`. -/
theorem witness_set_norm_le (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B) {f : 𝓗[d, H₀]}
    (hf : f ∈ witnessSet Φ s Ω) : ‖f‖ ≤ B :=
  sorry

/-- **Lemma 6 (Set of the Stein witnesses)**, Stein witnesses. `φ*_ρ ∈ 𝒲` for every
`ρ ∈ 𝒫(Ω)`. -/
theorem witness_set_steinWitness_mem [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
    [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) : steinWitness Φ s ρ ∈ witnessSet Φ s Ω :=
  sorry

/-- **Lemma 7 (A consistent candidate gives a solution).** Suppose that the standing assumptions
hold. Let `ρ₀ ∈ 𝒫(Ω)`, and let `m` be a candidate with values in `𝒲` such that `m = G_{ρ₀}(m)`.
Then, the maps `T_t = T^m_t` solve the continuous-time SVGD equation. -/
theorem consistent_candidate_isSolution (hS : StandingAssumptions Ω π p s Φ K C)
    (hρ₀ : ∀ᵐ x ∂ρ₀, x ∈ Ω) {m : ℝ → 𝓗[d, H₀]} (hm : Continuous m)
    (hm𝒲 : ∀ t, m t ∈ witnessSet Φ s Ω) (hcons : IsConsistent Φ s ρ₀ m) :
    IsSolution Φ s Ω ρ₀ fun t x ↦ trajectory Φ m 0 x t :=
  sorry

/-! ### A consistent candidate on a bounded time interval

The modulus of continuity of the Stein feature on `Ω` is
`ω(r) = sup {‖ξ_x - ξ_y‖_𝓗 | x, y ∈ Ω, ‖x - y‖ ≤ r}`, i.e.
`modulusOfContinuityOn (steinFeature Φ s) Ω` (`CompactSVGD/Definitions.lean`). -/

example (r : ℝ) : modulusOfContinuityOn (steinFeature Φ s) Ω r =
    sSup {e | ∃ x ∈ Ω, ∃ y ∈ Ω, dist x y ≤ r ∧
      dist (steinFeature Φ s x) (steinFeature Φ s y) = e} :=
  rfl

section Modulus

variable (hS : StandingAssumptions Ω π p s Φ K C)
include hS

/-- The modulus of continuity `ω` of the Stein feature on `Ω` is nondecreasing. -/
theorem monotone_modulus_steinFeature : Monotone (modulusOfContinuityOn (steinFeature Φ s) Ω) :=
  sorry

/-- `ω(r)` tends to `0` as `r` tends to `0`, by (i) of Lemma 4. -/
theorem tendsto_modulus_steinFeature :
    Tendsto (modulusOfContinuityOn (steinFeature Φ s) Ω) (𝓝 0) (𝓝 0) :=
  sorry

/-- `‖ξ_x - ξ_y‖_𝓗 ≤ ω(r)` for `x, y ∈ Ω` with `‖x - y‖ ≤ r`. -/
theorem dist_steinFeature_le_modulus {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) (hy : y ∈ Ω)
    {r : ℝ} (hxy : dist x y ≤ r) :
    dist (steinFeature Φ s x) (steinFeature Φ s y) ≤ modulusOfContinuityOn (steinFeature Φ s) Ω r :=
  sorry

/-- **Witness estimate.** Let `ψ₁, ψ₂` move the particles of `ρ ∈ 𝒫(Ω)` into `Ω`, each by at most
`r` from the other. Then, `‖φ*_{(ψ₁)#ρ} - φ*_{(ψ₂)#ρ}‖_𝓗 ≤ ω(r)`. -/
theorem dist_steinWitness_map_le [IsProbabilityMeasure ρ]
    {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (h₁ : AEMeasurable ψ₁ ρ)
    (h₂ : AEMeasurable ψ₂ ρ) (hψ₁ : ∀ᵐ x ∂ρ, ψ₁ x ∈ Ω) (hψ₂ : ∀ᵐ x ∂ρ, ψ₂ x ∈ Ω) {r : ℝ}
    (hr : ∀ᵐ x ∂ρ, dist (ψ₁ x) (ψ₂ x) ≤ r) :
    dist (steinWitness Φ s (ρ.map ψ₁)) (steinWitness Φ s (ρ.map ψ₂)) ≤
      modulusOfContinuityOn (steinFeature Φ s) Ω r :=
  sorry

end Modulus

/-- **Theorem 5 (Schauder).** Let `Γ` be a nonempty, compact and convex subset of a real normed
space. Then, every continuous map from `Γ` to `Γ` has a fixed point. It is usually stated in
a Banach space, but completeness is not needed. -/
theorem schauder {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Γ : Set X}
    (hΓ : IsCompact Γ) (hconv : Convex ℝ Γ) (hne : Γ.Nonempty) (G : C(Γ, Γ)) :
    ∃ g, Function.IsFixedPt G g :=
  sorry

/-- **Lemma 8 (A consistent candidate on a bounded time interval).** Suppose that the standing
assumptions hold. Let `ρ ∈ 𝒫(Ω)` and `a > 0`. Then, there is a continuous curve
`g : [0, a] → 𝒲` such that `g(t) = φ*_{(T^g_t)#ρ}` for every `t ∈ [0, a]`, where `T^g_t` are the
positions of Lemma 5 for the extension of `g` to `[0, ∞)` by the constant `g(a)`. -/
theorem consistent_candidate_bounded_interval [CompleteSpace H₀]
    (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
    {a : ℝ} (ha : 0 < a) :
    ∃ g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀], (∀ t, g t ∈ witnessSet Φ s Ω) ∧
      ∀ t, g t = steinWitness Φ s (ρ.map (trajectory Φ (IccExtend ha.le ⇑g) 0 · t)) :=
  sorry

/-! ### From a bounded time interval to all times -/

/-- **Theorem 4 (Existence of the continuous-time dynamics).** Suppose that the standing
assumptions hold, and let `ρ₀ ∈ 𝒫(Ω)`. Then, there is a family `(T_t)_{t ≥ 0}` of maps from `ℝᵈ` to
`ℝᵈ` that solves the continuous-time SVGD equation. -/
theorem exists_continuous_time_dynamics [CompleteSpace H₀]
    (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ₀] (hρ₀ : ∀ᵐ x ∂ρ₀, x ∈ Ω) :
    ∃ T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), IsSolution Φ s Ω ρ₀ T :=
  sorry

/-! ### Properties of the solutions -/

/-- The curve `m(t) = φ*_{ρ_t}` of the Stein witnesses of a family `(T_t)_{t ≥ 0}`, where
`ρ_t = (T_t)#ρ₀` (Lemma 9). It is extended to negative times by `m(0)`. -/
def witnessCurve (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (t : ℝ) : 𝓗[d, H₀] :=
  steinWitness Φ s (ρ₀.map (T (max t 0)))

theorem witnessCurve_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    witnessCurve Φ s ρ₀ T t = steinWitness Φ s (ρ₀.map (T t)) :=
  sorry

section SolutionProperties

variable (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ₀]
  (hT : IsSolution Φ s Ω ρ₀ T)
include hS hT

/-- The particles of a solution move at speed at most `B C` (proof of Lemma 9). -/
private theorem IsSolution.dist_le (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin d)) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    dist (T t x) (T t' x) ≤ B * C * |t - t'| :=
  sorry

/-- **Lemma 9 (Properties of the solutions)**, (i). Suppose that the standing assumptions hold, let
`ρ₀ ∈ 𝒫(Ω)`, let `(T_t)_{t ≥ 0}` solve the continuous-time SVGD equation, and let `m(t) = φ*_{ρ_t}`.
Then, `‖m(t) - m(t')‖_𝓗 ≤ ω(B C |t - t'|)` for all `t, t' ≥ 0`. -/
theorem solution_properties_dist_le (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    dist (witnessCurve Φ s ρ₀ T t) (witnessCurve Φ s ρ₀ T t') ≤
      modulusOfContinuityOn (steinFeature Φ s) Ω (B * C * |t - t'|) :=
  sorry

/-- **Lemma 9 (Properties of the solutions)**, (i). The curve `m` of the Stein witnesses of a
solution is continuous. -/
theorem solution_properties_continuous : Continuous (witnessCurve Φ s ρ₀ T) :=
  sorry

/-- The Stein witnesses of a solution are bounded. -/
private theorem exists_norm_witnessCurve_le : ∃ B : ℝ≥0, ∀ t, ‖witnessCurve Φ s ρ₀ T t‖ ≤ B :=
  sorry

/-- **Lemma 9 (Properties of the solutions)**, (ii). For every `t ≥ 0`, `T_t = T^m_t`, the
positions of Lemma 5 for the curve `m` of the Stein witnesses. -/
theorem solution_properties_eq_positions {t : ℝ} (ht : 0 ≤ t) :
    T t = (trajectory Φ (witnessCurve Φ s ρ₀ T) 0 · t) :=
  sorry

/-- **Lemma 9 (Properties of the solutions)**, (iii). For every `t ≥ 0`, `T_t` is a homeomorphism
of `ℝᵈ`. -/
theorem solution_properties_isHomeomorph {t : ℝ} (ht : 0 ≤ t) : IsHomeomorph (T t) :=
  sorry

/-- **Lemma 9 (Properties of the solutions)**, (iii). For every `t ≥ 0`, `T_t(Ω) = Ω`. -/
theorem solution_properties_image {t : ℝ} (ht : 0 ≤ t) : T t '' Ω = Ω :=
  sorry

/-- **Lemma 9 (Properties of the solutions)**, (iv). The points of `∂Ω` are at rest:
`T_t(z) = z` for all `z ∈ ∂Ω` and `t ≥ 0`. -/
theorem solution_properties_boundary {z : EuclideanSpace ℝ (Fin d)} (hz : z ∈ frontier Ω)
    {t : ℝ} (ht : 0 ≤ t) : T t z = z :=
  sorry

end SolutionProperties

/-! ## The time derivative of the KL divergence

### Decrease of the Kullback–Leibler divergence

Theorem 6 (Time derivative of the KL divergence), `SVGD.time_derivative_kl`, is proved below,
after the lemmas of its proof.

### Strategy of the proof of Theorem 6

The velocity field of the particles at time `t` is `v_t = b(·, ρ_t) = m(t)_Φ`, where `m` is the
curve of the Stein witnesses (`SVGD.witnessCurve`), and `J_t(x) = det DT_t(x)`.

### The Jacobian of `T_t` -/

section Jacobian

variable (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ₀]
  (hT : IsSolution Φ s Ω ρ₀ T)
include hS hT

/-- **Lemma 10 (Jacobian of `T_t`)**, differentiability. Suppose that the standing assumptions hold,
and let `(T_t)_{t ≥ 0}` solve the continuous-time SVGD equation. For every `t ≥ 0`, `T_t` is
differentiable on `ℝᵈ`. -/
theorem jacobian_differentiable {t : ℝ} (ht : 0 ≤ t) : Differentiable ℝ (T t) :=
  sorry

/-- **Lemma 10 (Jacobian of `T_t`)**, (i). `J_t(x) > 0`. -/
theorem jacobian_pos (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    0 < (fderiv ℝ (T t) x).det :=
  sorry

/-- **Lemma 10 (Jacobian of `T_t`)**, (ii). `∂ₜ log J_t(x) = ∇ · v_t(T_t(x))`, with a right
derivative at `t = 0`. -/
theorem jacobian_hasDerivWithinAt (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ Real.log (fderiv ℝ (T t) x).det)
      (divergence ℝ (drift Φ s (ρ₀.map (T t))) (T t x)) (Ici 0) t :=
  sorry

/-- **Lemma 10 (Jacobian of `T_t`)**, (iii). `|log J_t(x)| ≤ d B K t`, where `B` bounds `‖ξ_x‖_𝓗`
on `Ω`. -/
theorem jacobian_abs_log_le (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    |Real.log (fderiv ℝ (T t) x).det| ≤ d * B * K * t :=
  sorry

end Jacobian

/-! ### Differentiation of the KL divergence -/

section TimeDerivativeKL

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
  [IsProbabilityMeasure ρ₀] (hKL : klDiv ρ₀ π ≠ ∞) (hT : IsSolution Φ s Ω ρ₀ T)
include hS hKL hT

omit [CompleteSpace H₀] in
/-- **Theorem 6 (Time derivative of the KL divergence)**, finiteness. Suppose that the standing
assumptions hold. Let `ρ₀` be a probability measure with `KL(ρ₀ ‖ π) < ∞`, let `(T_t)_{t ≥ 0}` solve
the continuous-time SVGD equation, and let `ρ_t = (T_t)#ρ₀`. Then, `KL(ρ_t ‖ π) < ∞` for every
`t ≥ 0`. -/
theorem time_derivative_kl_ne_top {t : ℝ} (ht : 0 ≤ t) : klDiv (ρ₀.map (T t)) π ≠ ∞ :=
  sorry

/-- **Theorem 6 (Time derivative of the KL divergence).** Under the same assumptions,
`t ↦ KL(ρ_t ‖ π)` is differentiable on `[0, ∞)`, with a right derivative at `0`, and
`d/dt KL(ρ_t ‖ π) = -𝔎(ρ_t ∣ π)`. -/
theorem time_derivative_kl {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ (klDiv (ρ₀.map (T t)) π).toReal) (-𝔎[Φ, s] (ρ₀.map (T t)))
      (Ici 0) t :=
  sorry

/-- **Theorem 6 (Time derivative of the KL divergence)**, monotonicity. `t ↦ KL(ρ_t ‖ π)` is
nonincreasing on `[0, ∞)`. -/
theorem time_derivative_kl_antitoneOn :
    AntitoneOn (fun t ↦ (klDiv (ρ₀.map (T t)) π).toReal) (Ici 0) :=
  sorry

end TimeDerivativeKL

/-! ## Convergence

### Weak convergence and Stein-universal kernels

A sequence `(ρ_n)` of `𝒫(Ω)` converges weakly to `ρ ∈ 𝒫(Ω)` if `E_{x ∼ ρ_n}[g(x)] → E_{x ∼ ρ}[g(x)]`
for every `g ∈ C⁰(Ω)`. Here, `g ∈ C⁰(Ω)` is a function `g : ℝᵈ → ℝ` continuous on `Ω`, whose values
outside `Ω` do not matter, and the restriction `ρ|_Ω` of `ρ` to `Ω` is the measure
`ρ.comap ((↑) : Ω → ℝᵈ)` on the subtype `Ω`. -/

section KSDZero

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ]
  (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
include hS hρ

/-- **Characterization of a zero KSD**, first equivalence. For `ρ ∈ 𝒫(Ω)`,
`𝔎(ρ ∣ π) = 0 ⟺ φ*_ρ = 0`. -/
theorem ksd_eq_zero_iff : 𝔎[Φ, s] ρ = 0 ↔ steinWitness Φ s ρ = 0 :=
  sorry

/-- **Characterization of a zero KSD**, second equivalence. For `ρ ∈ 𝒫(Ω)`,
`φ*_ρ = 0 ⟺ ∀ f ∈ 𝓗, E_{x ∼ ρ}[𝒜_s f_Φ(x)] = 0`. -/
theorem steinWitness_eq_zero_iff :
    steinWitness Φ s ρ = 0 ↔ ∀ f, ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ = 0 :=
  sorry

end KSDZero

/-- **Definition 3 (Stein-universal kernel).** The kernel is Stein-universal if the set of the
functions `𝒜_s f_Φ + c`, for `f ∈ 𝓗` and `c ∈ ℝ`, restricted to `Ω`, is dense in `C⁰(Ω)` for the
uniform convergence on `Ω`. As `Ω` is compact, the topology of `C(Ω, ℝ)` is that of the uniform
convergence on `Ω`. -/
def IsSteinUniversal (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Dense {g : C(Ω, ℝ) | ∃ f : 𝓗[d, H₀], ∃ c : ℝ,
    ∀ x : Ω, g x = steinOperator s (toVectorField Φ f) x + c}

open scoped Classical in
/-- The extension by `0` of a function of `C(Ω, ℝ)` is continuous on `Ω`. -/
private theorem continuousOn_dite (g : C(Ω, ℝ)) :
    ContinuousOn (fun x ↦ if hx : x ∈ Ω then g ⟨x, hx⟩ else 0) Ω :=
  sorry

/-- **Definition 3 (Stein-universal kernel)**, unfolded. Suppose that the standing assumptions
hold. The kernel is Stein-universal if and only if, for every `g ∈ C⁰(Ω)` and every `η > 0`, there
are `f ∈ 𝓗` and `c ∈ ℝ` such that `sup_{x ∈ Ω} |g(x) - 𝒜_s f_Φ(x) - c| ≤ η`. -/
theorem isSteinUniversal_iff (hS : StandingAssumptions Ω π p s Φ K C) :
    IsSteinUniversal Φ s Ω ↔ ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω → ∀ η > 0,
      ∃ f : 𝓗[d, H₀], ∃ c : ℝ, ∀ x ∈ Ω, |g x - steinOperator s (toVectorField Φ f) x - c| ≤ η :=
  sorry

/-- If `|g - A - c| ≤ η` on `Ω` and `E_μ[A] = 0` for a probability measure `μ` carried by `Ω`,
then `|E_μ[g] - c| ≤ η`. -/
private theorem abs_integral_sub_le_of_integral_eq_zero {μ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Ω) {g A : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : Integrable g μ) (hA : Integrable A μ) (hA₀ : ∫ x, A x ∂μ = 0) {c η : ℝ}
    (h : ∀ x ∈ Ω, |g x - A x - c| ≤ η) : |∫ x, g x ∂μ - c| ≤ η :=
  sorry

/-- **Stein-universality through means.** Suppose that the standing assumptions hold. The kernel is
Stein-universal if and only if, for every `g ∈ C⁰(Ω)` and every `η > 0`, there is `f ∈ 𝓗` such that
`sup_{x ∈ Ω} |g(x) - E_{y ∼ π}[g(y)] - 𝒜_s f_Φ(x)| ≤ η`. -/
theorem isSteinUniversal_iff_mean (hS : StandingAssumptions Ω π p s Φ K C) :
    IsSteinUniversal Φ s Ω ↔ ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω → ∀ η > 0,
      ∃ f : 𝓗[d, H₀], ∀ x ∈ Ω,
        |g x - ∫ y, g y ∂π - steinOperator s (toVectorField Φ f) x| ≤ η :=
  sorry

/-- **Proposition 1 (The KSD vanishes only at `π`).** Suppose that the standing assumptions hold,
and that the kernel is Stein-universal. Then, `𝔎(ρ ∣ π) = 0 ⟺ ρ = π` for every `ρ ∈ 𝒫(Ω)`. -/
theorem ksd_vanishes_only_at_target [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
    (hU : IsSteinUniversal Φ s Ω) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) :
    𝔎[Φ, s] ρ = 0 ↔ ρ = π :=
  sorry

/-! ### Convergence to the target distribution

Theorem 7 (Convergence to the target distribution), `SVGD.convergence_to_target`, is proved
below, after the lemmas of its proof.

### Strategy of the proof of Theorem 7

The proof has three steps: `𝔎(ρ_t ∣ π) → 0` (`SVGD.ksd_convergence`), the limit points of `ρ_t`
have a zero KSD (`SVGD.limit_points_ksd_eq_zero`), and these limit points are `π`
(`SVGD.convergence_to_target`).

### The KSD tends to zero -/

/-- **Lemma 11 (Barbalat).** Let `u : [0, ∞) → [0, ∞)` be uniformly continuous, and let `M` be such
that `∫₀ᵃ u(t) dt ≤ M` for every `a ≥ 0`. Then, `u(t) → 0` as `t → ∞`. -/
theorem barbalat {u : ℝ → ℝ} (hu : UniformContinuousOn u (Ici 0))
    (hu₀ : ∀ t ∈ Ici (0 : ℝ), 0 ≤ u t) {M : ℝ} (hM : ∀ a ∈ Ici (0 : ℝ), ∫ t in 0..a, u t ≤ M) :
    Tendsto u atTop (𝓝 0) :=
  sorry

section KSDConvergence

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
  [IsProbabilityMeasure ρ₀] (hT : IsSolution Φ s Ω ρ₀ T)
include hS hT

/-- **Lemma 12 (Uniform continuity of the KSD)**, bound. Suppose that the standing assumptions hold,
let `ρ₀ ∈ 𝒫(Ω)`, let `(T_t)_{t ≥ 0}` solve the continuous-time SVGD equation, and let
`ρ_t = (T_t)#ρ₀`. Then, `|𝔎(ρ_t ∣ π) - 𝔎(ρ_{t'} ∣ π)| ≤ 2 B ω(B C |t - t'|)` for all `t, t' ≥ 0`. -/
theorem ksd_uniform_continuity_le (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B) {t t' : ℝ}
    (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    |𝔎[Φ, s] (ρ₀.map (T t)) - 𝔎[Φ, s] (ρ₀.map (T t'))| ≤
      2 * B * modulusOfContinuityOn (steinFeature Φ s) Ω (B * C * |t - t'|) :=
  sorry

/-- **Lemma 12 (Uniform continuity of the KSD).** `t ↦ 𝔎(ρ_t ∣ π)` is uniformly continuous on
`[0, ∞)`. -/
theorem ksd_uniform_continuity :
    UniformContinuousOn (fun t ↦ 𝔎[Φ, s] (ρ₀.map (T t))) (Ici 0) :=
  sorry

/-- **Corollary 2 (Convergence of the KSD).** Suppose that the standing assumptions hold. Let `ρ₀`
be a probability measure with `KL(ρ₀ ‖ π) < ∞`, let `(T_t)_{t ≥ 0}` solve the continuous-time SVGD
equation, and let `ρ_t = (T_t)#ρ₀`. Then, `𝔎(ρ_t ∣ π) → 0` as `t → ∞`. -/
theorem ksd_convergence (hKL : klDiv ρ₀ π ≠ ∞) :
    Tendsto (fun t ↦ 𝔎[Φ, s] (ρ₀.map (T t))) atTop (𝓝 0) :=
  sorry

/-! ### Limit points of the dynamics -/

/-- **Lemma 13 (Limit points have a zero KSD).** Suppose that the standing assumptions hold. Let
`ρ₀` be a probability measure with `KL(ρ₀ ‖ π) < ∞`, let `(T_t)_{t ≥ 0}` solve the continuous-time
SVGD equation, and let `ρ_t = (T_t)#ρ₀`. Let `t_n → ∞` and `ρ_∞ ∈ 𝒫(Ω)` be such that
`ρ_{t_n} ⇀ ρ_∞`. Then, `𝔎(ρ_∞ ∣ π) = 0`. -/
theorem limit_points_ksd_eq_zero (hKL : klDiv ρ₀ π ≠ ∞) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) {ρ_lim : Measure (EuclideanSpace ℝ (Fin d))}
    (hconv : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω →
      Tendsto (fun n ↦ ∫ x, g x ∂ρ₀.map (T (t n))) atTop (𝓝 (∫ x, g x ∂ρ_lim))) :
    𝔎[Φ, s] ρ_lim = 0 :=
  sorry

/-! ### Identification of the limit -/

/-- **Theorem 7 (Convergence to the target distribution).** Suppose that the standing assumptions
hold, and that the kernel is Stein-universal. Let `ρ₀` be a probability measure with
`KL(ρ₀ ‖ π) < ∞`, let `(T_t)_{t ≥ 0}` solve the continuous-time SVGD equation, and let
`ρ_t = (T_t)#ρ₀`. Then, `ρ_t` converges weakly to `π`: `E_{x ∼ ρ_t}[g(x)] → E_{x ∼ π}[g(x)]` for
every `g ∈ C⁰(Ω)`. -/
theorem convergence_to_target (hU : IsSteinUniversal Φ s Ω) (hKL : klDiv ρ₀ π ≠ ∞)
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : ContinuousOn g Ω) :
    Tendsto (fun t ↦ ∫ x, g x ∂ρ₀.map (T t)) atTop (𝓝 (∫ x, g x ∂π)) :=
  sorry

end KSDConvergence

end SVGD
