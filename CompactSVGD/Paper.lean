/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import CompactSVGD.Definitions
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.Compact

import CompactSVGD.FeatureMap.Trajectory
import CompactSVGD.FeatureMap.VectorField
import CompactSVGD.ForMathlib.Analysis.Calculus.Barbalat
import CompactSVGD.ForMathlib.Analysis.Calculus.Divergence
import CompactSVGD.ForMathlib.Analysis.Convex.TotallyBounded
import CompactSVGD.ForMathlib.Analysis.InnerProductSpace.PiL2
import CompactSVGD.ForMathlib.Analysis.InnerProductSpace.UnitBall
import CompactSVGD.ForMathlib.Analysis.Normed.PerturbationOfIdentity
import CompactSVGD.ForMathlib.Analysis.ODE.Gronwall
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Basic
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.FirstVariation
import CompactSVGD.ForMathlib.InformationTheory.KullbackLeibler.Transport
import CompactSVGD.ForMathlib.MeasureTheory.Function.LocallyIntegrable
import CompactSVGD.ForMathlib.MeasureTheory.Measure.Map
import CompactSVGD.ForMathlib.MeasureTheory.Measure.WithDensity
import CompactSVGD.ForMathlib.Topology.MetricSpace.ModulusOfContinuity
import CompactSVGD.ForMathlib.Topology.Order.Gluing
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import TauCeti.Analysis.Convex.SchauderFixedPoint

/-!
# Stein Variational Gradient Descent on a compact domain

This file formalizes the paper *Stein Variational Gradient Descent on a compact domain*
(G. Serré). It follows the paper section by section: every definition, assumption and result of the
paper appears here in the paper's order, under the paper's name and with the paper's proof. The
numbering of the statements (Assumption 1, Definition 2, Lemma 5, ...), of the sections and of the
equations is that of the paper.

Three theorems are stated in the paper before their proof: Theorem 4 (Section 6.2, proved in
Section 6.7), Theorem 6 (Section 7.1, proved in Section 7.4) and Theorem 7 (Section 8.2, proved in
Section 8.6). They appear here where their proof ends. The general results whose proof does not
involve SVGD (Lemmas 1 and 2, Theorems 1 and 5, Lemma 11, and the computations behind Lemma 10 and
Theorem 6) are proved in `CompactSVGD/ForMathlib/` and `CompactSVGD/FeatureMap/`, and restated
here. Schauder's fixed point theorem (Theorem 5) comes from Tau Ceti.

The general definitions (divergence, global solutions of ODEs, vector fields of a feature map and
their trajectories, modulus of continuity) are in `CompactSVGD/Definitions.lean`; those used in the
statements are recalled here by `example`s proved by `rfl`.

## Notation

| Paper | Lean |
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
| `(T_t)_{t ≥ 0}` solves Equation (3) | `SVGD.IsSolution Φ s Ω ρ₀ T` |
| `T^m_t(x)`, for a candidate `m` | `trajectory Φ m 0 x t` |
| `G_{ρ₀}(m)`, `𝒲`, `ω` | `fixedPointMap Φ s ρ₀ m`, `witnessSet Φ s Ω`, `modulusOfContinuityOn ξ Ω` |
| `ρ_n ⇀ ρ` | `∀ g, ContinuousOn g Ω → Tendsto (fun n ↦ ∫ x, g x ∂ρ_n) atTop (𝓝 (∫ x, g x ∂ρ))` |

## Implementation notes

* The domain `Ω` is a compact set of the paper's notations. Here, its compactness is a hypothesis
  `hΩ : IsCompact Ω`, or a field of `SVGD.StandingAssumptions`.
* The constant `B = max_{x ∈ Ω} ‖ξ_x‖` of Lemma 4 is replaced by any bound `B` of `‖ξ_x‖` on `Ω`.
* A curve `m : [0, ∞) → 𝓗` is a curve `m : ℝ → 𝓗` whose values at negative times do not matter,
  and a family `(T_t)_{t ≥ 0}` is a map `T : ℝ → ℝᵈ → ℝᵈ`. The curve of the Stein witnesses of a
  solution is extended to negative times by its value at `0` (`SVGD.witnessCurve`), as in the
  proof of Lemma 10.
* Equation (5) is stated with an almost everywhere bound instead of a supremum over `Ω`.
* Lemma 10 states that `T_t` is differentiable. The continuity of `DT_t` is not formalized: the
  proof of Theorem 6 only needs the measurability of `x ↦ log det DT_t(x)`.

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

/-! ## Section 2: Setting -/

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

/-- The target distribution is carried by `Ω`, i.e. `π(ℝᵈ \ Ω) = 0` (Section 3.2). -/
theorem TargetAssumption.ae_mem (hπ : TargetAssumption Ω π p s) (hΩ : IsCompact Ω) :
    ∀ᵐ x ∂π, x ∈ Ω :=
  hπ.eq_withDensity ▸ ae_withDensity_restrict_mem hΩ.measurableSet _

/-- Under Assumption 1, if `KL(ρ ‖ π) < ∞`, then `ρ` is carried by `Ω` (Section 3.2). -/
theorem TargetAssumption.ae_mem_of_klDiv_ne_top (hπ : TargetAssumption Ω π p s)
    (hΩ : IsCompact Ω) (hKL : klDiv ρ π ≠ ∞) : ∀ᵐ x ∂ρ, x ∈ Ω :=
  InformationTheory.ae_mem_of_klDiv_ne_top hΩ.measurableSet (hπ.eq_withDensity ▸ hKL)

end SVGD

/-! ## Section 3: Stein's method

### Section 3.1: The Stein operator and Stein's identity -/

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

/-! ### Section 3.2: First variation of the Kullback–Leibler divergence -/

namespace SVGD

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {π ρ : Measure (EuclideanSpace ℝ (Fin d))}
  {p : EuclideanSpace ℝ (Fin d) → ℝ}
  {s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d))}
  {v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {K_v : ℝ≥0}

private theorem nnnorm_mul_lt_one {ε : ℝ} {K : ℝ≥0} (hε : |ε| * K < 1) : ‖ε‖₊ * K < 1 := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_mul, coe_nnNorm, Real.norm_eq_abs, NNReal.coe_one]
  exact hε

section Perturbation

variable {ε : ℝ} (hv : LipschitzWith K_v v) (hε : |ε| * K_v < 1)
include hv hε

/-- **Lemma 1 (Perturbations of the identity)**, first part. Let `v` be `K_v`-Lipschitz and
`|ε| K_v < 1`. Then `Ψ = I_d + ε v` is a homeomorphism of `ℝᵈ`. -/
theorem perturbations_of_identity_isHomeomorph : IsHomeomorph fun x ↦ x + ε • v x := by
  have hu : LipschitzWith (‖ε‖₊ * K_v) fun x ↦ ε • v x := (lipschitzWith_smul ε).comp hv
  obtain ⟨e, he⟩ := hu.exists_homeomorph_id_add (nnnorm_mul_lt_one hε)
  exact he ▸ e.isHomeomorph

/-- **Lemma 1 (Perturbations of the identity)**, second part. If moreover `v` vanishes on `∂Ω`,
then `Ψ(Ω) = Ω`. -/
theorem perturbations_of_identity_image (hv₀ : ∀ y ∈ frontier Ω, v y = 0) :
    (fun x ↦ x + ε • v x) '' Ω = Ω := by
  have hu : LipschitzWith (‖ε‖₊ * K_v) fun x ↦ ε • v x := (lipschitzWith_smul ε).comp hv
  exact hu.image_add_eq_of_forall_frontier_eq_zero (nnnorm_mul_lt_one hε) fun y hy ↦ by
    simp [hv₀ y hy]

/-- **Lemma 1 (Perturbations of the identity)**, third part. If moreover `v` vanishes on `∂Ω`,
then `Ψ(Ω°) = Ω°`. -/
theorem perturbations_of_identity_image_interior (hv₀ : ∀ y ∈ frontier Ω, v y = 0) :
    (fun x ↦ x + ε • v x) '' interior Ω = interior Ω := by
  have hu : LipschitzWith (‖ε‖₊ * K_v) fun x ↦ ε • v x := (lipschitzWith_smul ε).comp hv
  exact hu.image_add_eq_of_forall_frontier_eq_zero (nnnorm_mul_lt_one hε) fun y hy ↦ by
    simp [hv₀ y (frontier_interior_subset hy)]

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
theorem transport_kl_ne_top : klDiv (ρ.map Ψ) π ≠ ∞ := by
  obtain ⟨hπ, -, hp, hpc, hp₀, -, -⟩ := hπ
  subst hπ
  exact klDiv_map_ne_top (e := (hΨ.homeomorph Ψ).toMeasurableEquiv) hΩ hp hpc hp₀ hΨd hΨΩ hdet
    hlog hKL

/-- **Lemma 2 (Transport of the Kullback–Leibler divergence)**, second part. Under the same
assumptions, `KL(Ψ#ρ ‖ π) = KL(ρ ‖ π) - ∫ (log p(Ψ(x)) - log p(x) + log det DΨ(x)) dρ(x)`. -/
theorem transport_kl :
    (klDiv (ρ.map Ψ) π).toReal = (klDiv ρ π).toReal -
      ∫ x, (Real.log (p (Ψ x)) - Real.log (p x) + Real.log (fderiv ℝ Ψ x).det) ∂ρ := by
  obtain ⟨hπ, -, hp, hpc, hp₀, -, -⟩ := hπ
  subst hπ
  exact toReal_klDiv_map_eq (e := (hΨ.homeomorph Ψ).toMeasurableEquiv) hΩ hp hpc hp₀ hΨd hΨΩ hdet
    hlog hKL

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
  ((hπ.continuousOn_score.clm_apply hv.continuous.continuousOn).add
    hv.continuous_divergence.continuousOn).integrable_of_ae_mem hΩ
      (hπ.ae_mem_of_klDiv_ne_top hΩ hKL)

/-- **Theorem 1 (First variation of the Kullback–Leibler divergence)**, finiteness. Under the same
assumptions, there is `ε₀ > 0` such that `KL((I_d + ε v)#ρ ‖ π) < ∞` for every `ε ∈ (-ε₀, ε₀)`. -/
theorem first_variation_ne_top :
    ∃ ε₀ > (0 : ℝ), ∀ ε ∈ Ioo (-ε₀) ε₀, klDiv (ρ.map fun x ↦ x + ε • v x) π ≠ ∞ := by
  obtain ⟨hπ, -, hp, hpc, hp₀, -, -⟩ := hπ
  subst hπ
  obtain ⟨ε₀, hε₀, h⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_klDiv_map_add_smul_ne_top hvK hΩ hp hpc hp₀ hv hv₀ hKL)
  exact ⟨ε₀, hε₀, fun ε hε ↦ h ε (by rwa [Real.ball_eq_Ioo, zero_sub, zero_add])⟩

/-- **Theorem 1 (First variation of the Kullback–Leibler divergence)**, derivative. Under the same
assumptions, `h : ε ↦ KL((I_d + ε v)#ρ ‖ π)` is differentiable at `0`, and
`h'(0) = -E_{x ∼ ρ}[𝒜_s v(x)]`. -/
theorem first_variation :
    HasDerivAt (fun ε : ℝ ↦ (klDiv (ρ.map fun x ↦ x + ε • v x) π).toReal)
      (-∫ x, steinOperator s v x ∂ρ) 0 := by
  obtain ⟨hπ, -, hp, hpc, hp₀, hs, hsc⟩ := hπ
  subst hπ
  exact hasDerivAt_toReal_klDiv_map_add_smul hvK hΩ hp hpc hp₀ hs hsc hv hv₀ hKL

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
  have := hπ.isProbabilityMeasure
  first_variation_integrable hΩ hπ hv (by simp)

/-- **Corollary 1 (Stein's identity for the target distribution).** Under the same assumptions,
`E_{x ∼ π}[𝒜_s v(x)] = 0`. -/
theorem stein_identity : ∫ x, steinOperator s v x ∂π = 0 := by
  have := hπ.isProbabilityMeasure
  -- `h : ε ↦ KL((I_d + ε v)#π ‖ π)` is nonnegative and vanishes at `0`, so `h'(0) = 0`.
  have hmin : IsLocalMin (fun ε : ℝ ↦ (klDiv (π.map fun x ↦ x + ε • v x) π).toReal) 0 :=
    .of_forall fun ε ↦ by simp
  have := hmin.hasDerivAt_eq_zero (first_variation hΩ hπ hv hvK hv₀ (by simp))
  linarith

end SteinIdentity

/-! ### Section 3.3: The Stein discrepancy

The Stein discrepancy `𝕊(ρ, π) = sup_{v ∈ 𝓕} E_{x ∼ ρ}[𝒜_s v(x)]` is only used through its kernelized
version, `SVGD.kernelSteinDiscrepancy` (Definition 2). -/

/-! ## Section 4: The kernelized Stein discrepancy

### Section 4.1: The kernel -/

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

/-- By (i) of Assumption 2, every vector field `f_Φ` is continuously differentiable
(Section 4.1). -/
theorem KernelAssumption.contDiff_toVectorField (hΦ : KernelAssumption Φ Ω K C)
    (f : 𝓗[d, H₀]) : ContDiff ℝ 1 (toVectorField Φ f) :=
  (pairing f).contDiff.comp hΦ.contDiff

/-- By (ii) of Assumption 2, `f_Φ` is `‖f‖ K`-Lipschitz (Section 4.1). -/
theorem KernelAssumption.lipschitzWith_toVectorField (hΦ : KernelAssumption Φ Ω K C)
    (f : 𝓗[d, H₀]) : LipschitzWith (‖f‖₊ * K) (toVectorField Φ f) :=
  SVGD.lipschitzWith_toVectorField hΦ.lipschitzWith f

/-- By (iv) of Assumption 2, `f_Φ` vanishes on `∂Ω` (Section 4.1). -/
theorem KernelAssumption.toVectorField_eq_zero (hΦ : KernelAssumption Φ Ω K C)
    (f : 𝓗[d, H₀]) {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ frontier Ω) :
    toVectorField Φ f y = 0 :=
  toVectorField_eq_zero_of_eq_zero (hΦ.eq_zero_of_mem_frontier y hy)

/-- **The standing assumptions** (Section 4.1): `Ω` is compact, and Assumptions 1 and 2 hold. -/
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

/-! ### Section 4.2: The kernelized Stein discrepancy -/

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

/-- The kernelized Stein discrepancy is nonnegative (Section 4.2). -/
theorem ksd_nonneg (ρ : Measure (EuclideanSpace ℝ (Fin d))) : 0 ≤ 𝔎[Φ, s] ρ :=
  Real.iSup_nonneg fun _ ↦ sq_nonneg _

/-- For `f ∈ 𝓗`, `𝒜_s f_Φ` is continuous on `Ω` (Section 4.2). -/
theorem continuousOn_steinOperator (hS : StandingAssumptions Ω π p s Φ K C) (f : 𝓗[d, H₀]) :
    ContinuousOn (steinOperator s (toVectorField Φ f)) Ω :=
  (hS.target.continuousOn_score.clm_apply
    (hS.kernel.contDiff_toVectorField f).continuous.continuousOn).add
      (hS.kernel.contDiff_toVectorField f).continuous_divergence.continuousOn

/-- `𝔎(π ∣ π) = 0`, by Corollary 1 (Section 4.2). -/
theorem ksd_target_eq_zero (hS : StandingAssumptions Ω π p s Φ K C) : 𝔎[Φ, s] π = 0 := by
  have h (f : 𝓗[d, H₀]) : ∫ x, steinOperator s (toVectorField Φ f) x ∂π = 0 :=
    stein_identity hS.isCompact hS.target (hS.kernel.contDiff_toVectorField f)
      (hS.kernel.lipschitzWith_toVectorField f) fun _ hy ↦ hS.kernel.toVectorField_eq_zero f hy
  simp [kernelSteinDiscrepancy, h]

/-! ### Section 4.3: The Stein witness -/

/-- The **Stein feature** `ξ_x ∈ 𝓗` of `x`, with components `(ξ_x)ᵢ = s(x)(eᵢ) Φ(x) + DΦ(x)(eᵢ)`
(Section 4.3). -/
def steinFeature (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : 𝓗[d, H₀] :=
  WithLp.toLp 2 fun i ↦
    s x (EuclideanSpace.single i 1) • Φ x + fderiv ℝ Φ x (EuclideanSpace.single i 1)

/-- **Lemma 3 (Stein feature).** Suppose that the standing assumptions hold. Then,
`𝒜_s f_Φ(x) = ⟪f, ξ_x⟫_𝓗` for all `x ∈ ℝᵈ` and `f ∈ 𝓗`. -/
theorem stein_feature (hS : StandingAssumptions Ω π p s Φ K C) (x : EuclideanSpace ℝ (Fin d))
    (f : 𝓗[d, H₀]) : steinOperator s (toVectorField Φ f) x = ⟪f, steinFeature Φ s x⟫ := by
  -- `f_Φ = P_f ∘ Φ` is differentiable at `x`, and `∇ · f_Φ(x) = ∑ᵢ ⟪fᵢ, DΦ(x)(eᵢ)⟫`.
  have hv : toVectorField Φ f x = ∑ i, ⟪f i, Φ x⟫ • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [steinOperator, divergence_euclideanSpace,
    (hasFDerivAt_toVectorField ((hS.kernel.contDiff.differentiable one_ne_zero) x).hasFDerivAt).fderiv,
    hv, map_sum, PiLp.inner_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [steinFeature, inner_add_right, inner_smul_right, real_inner_comm, mul_comm]

section XiRegularity

variable (hS : StandingAssumptions Ω π p s Φ K C)
include hS

/-- **Lemma 4 (Regularity of `ξ`)**, (i). The map `x ↦ ξ_x` is uniformly continuous from `Ω` to
`𝓗`. -/
theorem xi_regularity_uniformContinuousOn : UniformContinuousOn (steinFeature Φ s) Ω := by
  -- The components `s(x)(eᵢ) Φ(x) + DΦ(x)(eᵢ)` are continuous, and `Ω` is compact (Heine–Cantor).
  refine hS.isCompact.uniformContinuousOn_of_continuous
    ((PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun _ ↦ ?_))
  exact ((hS.target.continuousOn_score.clm_apply continuousOn_const).smul
    hS.kernel.contDiff.continuous.continuousOn).add
      ((hS.kernel.contDiff.continuous_fderiv one_ne_zero).continuousOn.clm_apply continuousOn_const)

/-- **Lemma 4 (Regularity of `ξ`)**, (ii). `‖ξ_x‖` is bounded on `Ω`. -/
theorem xi_regularity_exists_bound : ∃ B : ℝ≥0, ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hS.isCompact.exists_bound_of_continuousOn
    (xi_regularity_uniformContinuousOn hS).continuousOn
  exact ⟨B.toNNReal, fun x hx ↦ (hB x hx).trans (Real.le_coe_toNNReal B)⟩

/-- **Lemma 4 (Regularity of `ξ`)**, (iii). For every `ρ ∈ 𝒫(Ω)`, `x ↦ ξ_x` is `ρ`-integrable. -/
theorem xi_regularity_integrable [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) :
    Integrable (steinFeature Φ s) ρ :=
  (xi_regularity_uniformContinuousOn hS).continuousOn.integrable_of_ae_mem hS.isCompact hρ

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
    ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ = ⟪f, steinWitness Φ s ρ⟫ := by
  -- `⟪f, ·⟫` commutes with the Bochner integral, and `𝒜_s f_Φ(x) = ⟪f, ξ_x⟫` (Lemma 3).
  rw [steinWitness, ← integral_inner (xi_regularity_integrable hS hρ) f]
  exact integral_congr_ae (.of_forall fun x ↦ stein_feature hS x f)

/-- **Theorem 2 (Stein witness)**, uniqueness. Under the same assumptions, `φ*_ρ` is the only
`f' ∈ 𝓗` such that `E_{x ∼ ρ}[𝒜_s f_Φ(x)] = ⟪f, f'⟫_𝓗` for every `f ∈ 𝓗`. -/
theorem stein_witness_unique {f' : 𝓗[d, H₀]}
    (hf' : ∀ f, ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ = ⟪f, f'⟫) :
    f' = steinWitness Φ s ρ := by
  -- `⟪f, f' - φ*_ρ⟫ = 0` for every `f`, in particular for `f = f' - φ*_ρ`.
  have h := hf' (f' - steinWitness Φ s ρ)
  rw [stein_witness hS hρ] at h
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ), inner_sub_right, ← h, sub_self]

/-- **Theorem 2 (Stein witness)**, (i). On the closed unit ball of `𝓗`, the function
`f ↦ E_{x ∼ ρ}[𝒜_s f_Φ(x)]` reaches its maximum at `f* = φ*_ρ / ‖φ*_ρ‖_𝓗`, which is `0` when
`φ*_ρ = 0`. -/
theorem stein_witness_isMaxOn :
    IsMaxOn (fun f : 𝓗[d, H₀] ↦ ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ)
      (closedBall 0 1) (‖steinWitness Φ s ρ‖⁻¹ • steinWitness Φ s ρ) := by
  -- By the Cauchy–Schwarz inequality.
  simpa only [stein_witness hS hρ] using isMaxOn_inner_closedBall _

/-- **Theorem 2 (Stein witness)**, (ii). `𝔎(ρ ∣ π) = ‖φ*_ρ‖²_𝓗`. -/
theorem stein_witness_ksd : 𝔎[Φ, s] ρ = ‖steinWitness Φ s ρ‖ ^ 2 := by
  simp only [kernelSteinDiscrepancy, stein_witness hS hρ]
  exact iSup_closedBall_inner_sq _

/-- **Theorem 2 (Stein witness)**, (ii). `𝔎(ρ ∣ π) = E_{x ∼ ρ}[𝒜_s (φ*_ρ)_Φ(x)]`. -/
theorem stein_witness_ksd_eq_integral :
    𝔎[Φ, s] ρ = ∫ x, steinOperator s (toVectorField Φ (steinWitness Φ s ρ)) x ∂ρ := by
  rw [stein_witness_ksd hS hρ, stein_witness hS hρ, real_inner_self_eq_norm_sq]

/-- `E_{x ∼ ρ}[𝒜_s f_Φ(x)]² ≤ 𝔎(ρ ∣ π)` for every `f` of the closed unit ball of `𝓗`
(Definition 2). -/
theorem sq_integral_steinOperator_le_ksd {f : 𝓗[d, H₀]} (hf : ‖f‖ ≤ 1) :
    (∫ x, steinOperator s (toVectorField Φ f) x ∂ρ) ^ 2 ≤ 𝔎[Φ, s] ρ := by
  -- `|⟪f, φ*_ρ⟫| ≤ ‖f‖ ‖φ*_ρ‖ ≤ ‖φ*_ρ‖`, by the Cauchy–Schwarz inequality.
  rw [stein_witness hS hρ, stein_witness_ksd hS hρ]
  have h : |⟪f, steinWitness Φ s ρ⟫| ≤ ‖steinWitness Φ s ρ‖ :=
    (abs_real_inner_le_norm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg (steinWitness Φ s ρ)))
  simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

end SteinWitness

/-- `‖φ*_ρ‖_𝓗 ≤ B` for `ρ ∈ 𝒫(Ω)`, where `B` bounds `‖ξ_x‖_𝓗` on `Ω` (Section 4.3). -/
theorem norm_steinWitness_le {B : ℝ≥0} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) : ‖steinWitness Φ s ρ‖ ≤ B := by
  simpa [steinWitness] using norm_integral_le_of_norm_le_const (hρ.mono hB)

/-- `‖(φ*_ρ)_Φ(y)‖ ≤ B C` for `ρ ∈ 𝒫(Ω)` and `y ∈ ℝᵈ` (Section 4.3). -/
theorem norm_toVectorField_steinWitness_le (hS : StandingAssumptions Ω π p s Φ K C) {B : ℝ≥0}
    (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
    (y : EuclideanSpace ℝ (Fin d)) : ‖toVectorField Φ (steinWitness Φ s ρ) y‖ ≤ B * C :=
  norm_toVectorField_le_of_le hS.kernel.norm_le (norm_steinWitness_le hB hρ) y

/-- The Stein witness of `π` vanishes, as `𝔎(π ∣ π) = 0` (Section 4.3). -/
theorem steinWitness_target_eq_zero [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C) :
    steinWitness Φ s π = 0 := by
  have := hS.target.isProbabilityMeasure
  have h := stein_witness_ksd hS (hS.target.ae_mem hS.isCompact)
  rwa [ksd_target_eq_zero hS, eq_comm, sq_eq_zero_iff, norm_eq_zero] at h

/-! ## Section 5: The steepest descent of the KL divergence -/

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
    ∀ᶠ ε in 𝓝 (0 : ℝ), klDiv (ρ.map fun x ↦ x + ε • toVectorField Φ f x) π ≠ ∞ := by
  obtain ⟨ε₀, hε₀, h⟩ := first_variation_ne_top hS.isCompact hS.target
    (hS.kernel.contDiff_toVectorField f) (hS.kernel.lipschitzWith_toVectorField f)
    (fun _ hy ↦ hS.kernel.toVectorField_eq_zero f hy) hKL
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hε₀) hε₀] with ε hε using h ε hε

/-- **Theorem 3 (KL steepest descent)**, (i). For every `f ∈ 𝓗`, `h_f` is differentiable at `0`,
and `h'_f(0) = -⟪f, φ*_ρ⟫_𝓗`. -/
theorem kl_steepest_descent_hasDerivAt (f : 𝓗[d, H₀]) :
    HasDerivAt (fun ε : ℝ ↦ (klDiv (ρ.map fun x ↦ x + ε • toVectorField Φ f x) π).toReal)
      (-⟪f, steinWitness Φ s ρ⟫) 0 := by
  -- Theorem 1 with `v = f_Φ`, and Theorem 2.
  have h := first_variation hS.isCompact hS.target (hS.kernel.contDiff_toVectorField f)
    (hS.kernel.lipschitzWith_toVectorField f) (fun _ hy ↦ hS.kernel.toVectorField_eq_zero f hy)
    hKL
  rwa [stein_witness hS (hS.target.ae_mem_of_klDiv_ne_top hS.isCompact hKL)] at h

/-- **Theorem 3 (KL steepest descent)**, (i), as the first variation `h'_f(0) = -⟪f, φ*_ρ⟫_𝓗`. -/
theorem kl_steepest_descent_eq_inner (f : 𝓗[d, H₀]) :
    klFirstVariation Φ π ρ f = -⟪f, steinWitness Φ s ρ⟫ :=
  (kl_steepest_descent_hasDerivAt hS hKL f).deriv

/-- **Theorem 3 (KL steepest descent)**, (ii). On the closed unit ball of `𝓗`, `f ↦ h'_f(0)`
reaches its minimum at `f* = φ*_ρ / ‖φ*_ρ‖_𝓗`, which is `0` when `φ*_ρ = 0`. -/
theorem kl_steepest_descent_isMinOn :
    IsMinOn (klFirstVariation Φ π ρ) (closedBall 0 1)
      (‖steinWitness Φ s ρ‖⁻¹ • steinWitness Φ s ρ) := fun f hf ↦ by
  change klFirstVariation Φ π ρ _ ≤ klFirstVariation Φ π ρ f
  rw [kl_steepest_descent_eq_inner hS hKL, kl_steepest_descent_eq_inner hS hKL,
    inner_inv_norm_smul_self, neg_le_neg_iff]
  exact inner_le_norm_of_mem_closedBall hf

/-- **Theorem 3 (KL steepest descent)**, (ii), uniqueness. If `φ*_ρ ≠ 0`, then `f*` is the only
minimizer of `f ↦ h'_f(0)` on the closed unit ball of `𝓗`. -/
theorem kl_steepest_descent_eq (hφ : steinWitness Φ s ρ ≠ 0) {f : 𝓗[d, H₀]}
    (hf : f ∈ closedBall 0 1)
    (hmin : klFirstVariation Φ π ρ f =
      klFirstVariation Φ π ρ (‖steinWitness Φ s ρ‖⁻¹ • steinWitness Φ s ρ)) :
    f = ‖steinWitness Φ s ρ‖⁻¹ • steinWitness Φ s ρ := by
  rw [kl_steepest_descent_eq_inner hS hKL, kl_steepest_descent_eq_inner hS hKL,
    inner_inv_norm_smul_self, neg_inj] at hmin
  exact eq_inv_norm_smul_of_inner_eq_norm hφ hf hmin

/-- **Theorem 3 (KL steepest descent)**, (iii). `h'_{φ*_ρ}(0) = -𝔎(ρ ∣ π)`. -/
theorem kl_steepest_descent_ksd : klFirstVariation Φ π ρ (steinWitness Φ s ρ) = -𝔎[Φ, s] ρ := by
  rw [kl_steepest_descent_eq_inner hS hKL, real_inner_self_eq_norm_sq,
    stein_witness_ksd hS (hS.target.ae_mem_of_klDiv_ne_top hS.isCompact hKL)]

end KLSteepestDescent

/-! ## Section 6: SVGD in continuous time

### Section 6.1: The continuous-time dynamics -/

/-- The **drift** `b(x, ρ) = (φ*_ρ)_Φ(x)` of the continuous-time dynamics: the velocity of a
particle located at `x` when the particles are distributed according to `ρ` (Section 6.1). -/
def drift (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  toVectorField Φ (steinWitness Φ s ρ) x

/-- **A solution of Equation (3)** from `ρ₀`: a family `(T_t)_{t ≥ 0}` of continuous maps from `ℝᵈ`
to `ℝᵈ` such that `T_0 = I_d`, `ρ_t = (T_t)#ρ₀ ∈ 𝒫(Ω)` for every `t ≥ 0`, and
`d/dt T_t(x) = b(T_t(x), ρ_t)` for all `x ∈ ℝᵈ` and `t ≥ 0`, with a right derivative at `t = 0`
(Section 6.1). -/
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
  /-- Equation (3): `d/dt T_t(x) = b(T_t(x), ρ_t)`, with a right derivative at `0`. -/
  hasDerivWithinAt : ∀ x t, 0 ≤ t →
    HasDerivWithinAt (T · x) (drift Φ s (ρ₀.map (T t)) (T t x)) (Ici 0) t

/-! ### Section 6.2: Existence of a solution

Theorem 4 (Existence of the continuous-time dynamics) is proved in Section 6.7
(`SVGD.exists_continuous_time_dynamics`).

### Section 6.3: Strategy of the proof

A **candidate** is a continuous and bounded curve `m : [0, ∞) → 𝓗`. At time `t`, it gives the
velocity `m(t)_Φ(y)` to a particle located at `y`. The position at time `t` of the particle that
starts from `x` is `T^m_t(x) = trajectory Φ m 0 x t` (`CompactSVGD/Definitions.lean`). -/

/-- The positions `T^m_t(x)` are the global solutions of `α' = m(t)_Φ(α)` with `α(0) = x`. -/
example (m : ℝ → 𝓗[d, H₀]) (x : EuclideanSpace ℝ (Fin d)) :
    trajectory Φ m 0 x = ODE.globalSolution (fun t ↦ toVectorField Φ (m t)) 0 x :=
  rfl

/-! ### Section 6.4: From the drift to the positions -/

section Positions

variable (hS : StandingAssumptions Ω π p s Φ K C) {R : ℝ≥0} {m : ℝ → 𝓗[d, H₀]}
  (hm : Continuous m) (hmR : ∀ t, ‖m t‖ ≤ R)
include hS hm hmR

/-- **Lemma 5 (Positions for a given drift)**, existence. Suppose that the standing assumptions
hold, and let `m` be a continuous curve with `‖m(t)‖_𝓗 ≤ R`. Then, `t ↦ T^m_t(x)` solves
`d/dt T^m_t(x) = m(t)_Φ(T^m_t(x))`. -/
theorem positions_hasDerivAt (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (trajectory Φ m 0 x) (toVectorField Φ (m t) (trajectory Φ m 0 x t)) t :=
  hasDerivAt_trajectory hm hmR hS.kernel.lipschitzWith 0 x t

/-- **Lemma 5 (Positions for a given drift)**, initial condition. `T^m_0(x) = x`. -/
theorem positions_zero (x : EuclideanSpace ℝ (Fin d)) : trajectory Φ m 0 x 0 = x :=
  trajectory_self hm hmR hS.kernel.lipschitzWith 0 x

/-- **Lemma 5 (Positions for a given drift)**, uniqueness. The solution of
`d/dt α(t) = m(t)_Φ(α(t))`, `α(0) = x`, is unique on `[0, ∞)`. -/
theorem positions_unique {α : ℝ → EuclideanSpace ℝ (Fin d)} {x : EuclideanSpace ℝ (Fin d)}
    (hα₀ : α 0 = x)
    (hα : ∀ t, 0 ≤ t → HasDerivWithinAt α (toVectorField Φ (m t) (α t)) (Ici 0) t) {t : ℝ}
    (ht : 0 ≤ t) : α t = trajectory Φ m 0 x t :=
  ODE_solution_unique_of_mem_Icc_right (v := fun t ↦ toVectorField Φ (m t)) (s := fun _ ↦ univ)
    (fun τ _ ↦ (lipschitzWith_toVectorField_of_norm_le hS.kernel.lipschitzWith (hmR τ)).lipschitzOnWith)
    (fun τ hτ ↦ (hα τ hτ.1).continuousWithinAt.mono fun _ h ↦ h.1)
    (fun τ hτ ↦ (hα τ hτ.1).mono (Ici_subset_Ici.2 hτ.1)) (fun _ _ ↦ mem_univ _)
    (continuous_trajectory hm hmR hS.kernel.lipschitzWith 0 x).continuousOn
    (fun τ _ ↦ (positions_hasDerivAt hS hm hmR x τ).hasDerivWithinAt) (fun _ _ ↦ mem_univ _)
    (by rw [hα₀, positions_zero hS hm hmR]) ⟨ht, le_rfl⟩

/-- **Lemma 5 (Positions for a given drift)**, (i). `T^m_t` is a homeomorphism of `ℝᵈ`. -/
theorem positions_isHomeomorph (t : ℝ) : IsHomeomorph (trajectory Φ m 0 · t) :=
  isHomeomorph_trajectory hm hmR hS.kernel.lipschitzWith 0 t

/-- **Lemma 5 (Positions for a given drift)**, (i). `T^m_t(Ω) = Ω`. -/
theorem positions_image (t : ℝ) : (trajectory Φ m 0 · t) '' Ω = Ω := by
  -- A trajectory that meets `Ω` stays in `Ω`, and `T^m_t` is inverted by following the
  -- trajectories backward.
  have hK := hS.kernel
  refine (image_subset_iff.2 fun x hx ↦ trajectory_mem hm hmR hK.lipschitzWith
    hK.eq_zero_of_mem_frontier hx t).antisymm fun y hy ↦ ?_
  exact ⟨trajectory Φ m t y 0, trajectory_mem hm hmR hK.lipschitzWith hK.eq_zero_of_mem_frontier hy 0,
    trajectory_trajectory_apply hm hmR hK.lipschitzWith t 0 y⟩

/-- **Lemma 5 (Positions for a given drift)**, (ii). `‖T^m_t(x) - T^m_{t'}(x)‖ ≤ R C |t - t'|`. -/
theorem positions_dist_le (x : EuclideanSpace ℝ (Fin d)) (t t' : ℝ) :
    dist (trajectory Φ m 0 x t) (trajectory Φ m 0 x t') ≤ R * C * |t - t'| := by
  have := (lipschitzWith_trajectory hm hmR hS.kernel.lipschitzWith hS.kernel.norm_le 0
    x).dist_le_mul t t'
  rwa [Real.dist_eq, NNReal.coe_mul] at this

/-- **Lemma 5 (Positions for a given drift)**, (iii). Let `m'` be another continuous curve with
`‖m'(t)‖_𝓗 ≤ R`. If `‖m(r) - m'(r)‖_𝓗 ≤ Δ` for `r ∈ [0, t]`, then
`‖T^m_t(x) - T^{m'}_t(x)‖ ≤ C t e^{R K t} Δ`. -/
theorem positions_dist_le_of_dist_le {m' : ℝ → 𝓗[d, H₀]} (hm' : Continuous m')
    (hmR' : ∀ t, ‖m' t‖ ≤ R) {t Δ : ℝ} (ht : 0 ≤ t) (hΔ : ∀ r ∈ Icc 0 t, dist (m r) (m' r) ≤ Δ)
    (x : EuclideanSpace ℝ (Fin d)) :
    dist (trajectory Φ m 0 x t) (trajectory Φ m' 0 x t) ≤ C * t * Real.exp (R * K * t) * Δ := by
  -- Grönwall's inequality, with a zero initial gap.
  have hΔ₀ : 0 ≤ Δ := dist_nonneg.trans (hΔ 0 ⟨le_rfl, ht⟩)
  have h := dist_trajectory_trajectory_le_of_dist_le hm hmR hS.kernel.lipschitzWith
    hS.kernel.norm_le hm' hmR' ht (fun τ hτ ↦ hΔ τ (Ico_subset_Icc_self hτ)) x
  rw [sub_zero] at h
  exact h.trans ((gronwallBound_zero_le (by positivity) (by positivity) t).trans_eq (by ring))

end Positions

/-! ### Section 6.5: From the positions to the drift -/

/-- The map `G_{ρ₀}(m) : t ↦ φ*_{(T^m_t)#ρ₀}`, which sends a candidate `m` to the drift that SVGD
prescribes for the positions that `m` produces (Section 6.5). -/
def fixedPointMap (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ₀ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → 𝓗[d, H₀]) (t : ℝ) : 𝓗[d, H₀] :=
  steinWitness Φ s (ρ₀.map (trajectory Φ m 0 · t))

/-- A candidate `m` is **consistent** when `m = G_{ρ₀}(m)`, i.e. `m(t) = φ*_{(T^m_t)#ρ₀}` for every
`t ≥ 0` (Equation (4)). -/
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
  (hS.isCompact.image_of_continuousOn
    (xi_regularity_uniformContinuousOn hS).continuousOn).closedConvexHull

/-- **Lemma 6 (Set of the Stein witnesses)**, bound. `‖f‖_𝓗 ≤ B` for every `f ∈ 𝒲`, where `B`
bounds `‖ξ_x‖_𝓗` on `Ω`. -/
theorem witness_set_norm_le {B : ℝ≥0} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B) {f : 𝓗[d, H₀]}
    (hf : f ∈ witnessSet Φ s Ω) : ‖f‖ ≤ B := by
  -- The closed ball of radius `B` is closed and convex, and it contains every `ξ_x`.
  have h : witnessSet Φ s Ω ⊆ closedBall 0 B := closedConvexHull_min (by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.2 (hB x hx)) (convex_closedBall 0 B) isClosed_closedBall
  exact mem_closedBall_zero_iff.1 (h hf)

/-- **Lemma 6 (Set of the Stein witnesses)**, Stein witnesses. `φ*_ρ ∈ 𝒲` for every
`ρ ∈ 𝒫(Ω)`. -/
theorem witness_set_steinWitness_mem [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
    [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) : steinWitness Φ s ρ ∈ witnessSet Φ s Ω :=
  -- A mean of points of a closed convex set stays in this set.
  (convex_closedConvexHull).integral_mem isClosed_closedConvexHull
    (hρ.mono fun _ hx ↦ subset_closedConvexHull (mem_image_of_mem _ hx))
    (xi_regularity_integrable hS hρ)

/-- **Lemma 7 (A consistent candidate gives a solution).** Suppose that the standing assumptions
hold. Let `ρ₀ ∈ 𝒫(Ω)`, and let `m` be a candidate with values in `𝒲` such that `m = G_{ρ₀}(m)`.
Then, the maps `T_t = T^m_t` solve Equation (3). -/
theorem consistent_candidate_isSolution [CompleteSpace H₀]
    (hS : StandingAssumptions Ω π p s Φ K C) {ρ₀ : Measure (EuclideanSpace ℝ (Fin d))}
    (hρ₀ : ∀ᵐ x ∂ρ₀, x ∈ Ω) {m : ℝ → 𝓗[d, H₀]} (hm : Continuous m)
    (hm𝒲 : ∀ t, m t ∈ witnessSet Φ s Ω) (hcons : IsConsistent Φ s ρ₀ m) :
    IsSolution Φ s Ω ρ₀ fun t x ↦ trajectory Φ m 0 x t := by
  obtain ⟨B, hB⟩ := xi_regularity_exists_bound hS
  have hmB (t : ℝ) : ‖m t‖ ≤ B := witness_set_norm_le hB (hm𝒲 t)
  have hK := hS.kernel
  refine ⟨fun t _ ↦ continuous_trajectory_apply hm hmB hK.lipschitzWith 0 t,
    funext (positions_zero hS hm hmB), fun t _ ↦ ae_map_trajectory_mem hm hmB hK.lipschitzWith
      hS.isCompact.measurableSet hK.eq_zero_of_mem_frontier hρ₀ 0 t, fun x t ht ↦ ?_⟩
  -- As `m(t) = φ*_{ρ_t}`, the equation of Lemma 5 is Equation (3).
  rw [drift, ← fixedPointMap, ← hcons t ht]
  exact (positions_hasDerivAt hS hm hmB x t).hasDerivWithinAt

/-! ### Section 6.6: A consistent candidate on a bounded time interval

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

/-- The modulus of continuity `ω` of the Stein feature on `Ω` is nondecreasing (Section 6.6). -/
theorem monotone_modulus_steinFeature : Monotone (modulusOfContinuityOn (steinFeature Φ s) Ω) :=
  monotone_modulusOfContinuityOn (hS.isCompact.image_of_continuousOn
    (xi_regularity_uniformContinuousOn hS).continuousOn).isBounded

/-- `ω(r)` tends to `0` as `r` tends to `0`, by (i) of Lemma 4 (Section 6.6). -/
theorem tendsto_modulus_steinFeature :
    Tendsto (modulusOfContinuityOn (steinFeature Φ s) Ω) (𝓝 0) (𝓝 0) :=
  tendsto_modulusOfContinuityOn (xi_regularity_uniformContinuousOn hS)

/-- `‖ξ_x - ξ_y‖_𝓗 ≤ ω(r)` for `x, y ∈ Ω` with `‖x - y‖ ≤ r` (Section 6.6). -/
theorem dist_steinFeature_le_modulus {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) (hy : y ∈ Ω)
    {r : ℝ} (hxy : dist x y ≤ r) :
    dist (steinFeature Φ s x) (steinFeature Φ s y) ≤ modulusOfContinuityOn (steinFeature Φ s) Ω r :=
  dist_le_modulusOfContinuityOn (hS.isCompact.image_of_continuousOn
    (xi_regularity_uniformContinuousOn hS).continuousOn).isBounded hx hy hxy

/-- **Equation (5).** Let `ψ₁, ψ₂` move the particles of `ρ ∈ 𝒫(Ω)` into `Ω`, each by at most `r`
from the other. Then, `‖φ*_{(ψ₁)#ρ} - φ*_{(ψ₂)#ρ}‖_𝓗 ≤ ω(r)`. Here, the supremum over `Ω` of the
paper is replaced by an almost everywhere bound. -/
theorem dist_steinWitness_map_le [CompleteSpace H₀] [IsProbabilityMeasure ρ]
    {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (h₁ : AEMeasurable ψ₁ ρ)
    (h₂ : AEMeasurable ψ₂ ρ) (hψ₁ : ∀ᵐ x ∂ρ, ψ₁ x ∈ Ω) (hψ₂ : ∀ᵐ x ∂ρ, ψ₂ x ∈ Ω) {r : ℝ}
    (hr : ∀ᵐ x ∂ρ, dist (ψ₁ x) (ψ₂ x) ≤ r) :
    dist (steinWitness Φ s (ρ.map ψ₁)) (steinWitness Φ s (ρ.map ψ₂)) ≤
      modulusOfContinuityOn (steinFeature Φ s) Ω r := by
  have hΩm := hS.isCompact.measurableSet
  -- By the change of variables formula, `φ*_{ψ#ρ} = E_{x ∼ ρ}[ξ_{ψ(x)}]`.
  have hmap {ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hψ : AEMeasurable ψ ρ)
      (hψΩ : ∀ᵐ x ∂ρ, ψ x ∈ Ω) :
      Integrable (fun x ↦ steinFeature Φ s (ψ x)) ρ ∧
        steinWitness Φ s (ρ.map ψ) = ∫ x, steinFeature Φ s (ψ x) ∂ρ := by
    have hΩ' : ∀ᵐ y ∂ρ.map ψ, y ∈ Ω := (ae_map_iff hψ hΩm).2 hψΩ
    have hm : AEStronglyMeasurable (steinFeature Φ s) (ρ.map ψ) := by
      rw [← Measure.restrict_eq_self_of_ae_mem hΩ']
      exact (xi_regularity_uniformContinuousOn hS).continuousOn.aestronglyMeasurable hΩm
    exact ⟨(integrable_map_measure hm hψ).1 (xi_regularity_integrable hS hΩ'),
      integral_map hψ hm⟩
  obtain ⟨hi₁, he₁⟩ := hmap h₁ hψ₁
  obtain ⟨hi₂, he₂⟩ := hmap h₂ hψ₂
  -- The norm of a mean is at most the mean of the norms.
  rw [he₁, he₂, dist_eq_norm, ← integral_sub hi₁ hi₂]
  refine (norm_integral_le_of_norm_le_const
    (C := modulusOfContinuityOn (steinFeature Φ s) Ω r) ?_).trans_eq (by simp)
  filter_upwards [hψ₁, hψ₂, hr] with x hx₁ hx₂ hx
  rw [← dist_eq_norm]
  exact dist_steinFeature_le_modulus hS hx₁ hx₂ hx

end Modulus

/-- **Theorem 5 (Schauder).** Let `Γ` be a nonempty, compact and convex subset of a real normed
space. Then, every continuous map from `Γ` to `Γ` has a fixed point. The paper states it in a
Banach space, but completeness is not needed. -/
theorem schauder {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Γ : Set X}
    (hΓ : IsCompact Γ) (hconv : Convex ℝ Γ) (hne : Γ.Nonempty) (G : C(Γ, Γ)) :
    ∃ g, Function.IsFixedPt G g :=
  TauCeti.schauderFixedPoint_compactConvex hΓ hconv hne G

/-- **Lemma 8 (A consistent candidate on a bounded time interval).** Suppose that the standing
assumptions hold. Let `ρ ∈ 𝒫(Ω)` and `a > 0`. Then, there is a continuous curve
`g : [0, a] → 𝒲` such that `g(t) = φ*_{(T^g_t)#ρ}` for every `t ∈ [0, a]`, where `T^g_t` are the
positions of Lemma 5 for the extension of `g` to `[0, ∞)` by the constant `g(a)`. -/
theorem consistent_candidate_bounded_interval [CompleteSpace H₀]
    (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
    {a : ℝ} (ha : 0 < a) :
    ∃ g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀], (∀ t, g t ∈ witnessSet Φ s Ω) ∧
      ∀ t, g t = steinWitness Φ s (ρ.map (trajectory Φ (IccExtend ha.le ⇑g) 0 · t)) := by
  classical
  set 𝒲 := witnessSet Φ s Ω
  set ω := modulusOfContinuityOn (steinFeature Φ s) Ω
  have hK := hS.kernel
  obtain ⟨B, hB⟩ := xi_regularity_exists_bound hS
  have h𝒲 : IsCompact 𝒲 := witness_set_isCompact hS
  have hω₀ (r : ℝ) : 0 ≤ ω r := modulusOfContinuityOn_nonneg _ _ r
  have hωsmall (c : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ r, 0 ≤ r → r < δ → ω (c * r) < ε :=
    exists_pos_forall_modulusOfContinuityOn_mul_lt (xi_regularity_uniformContinuousOn hS) c hε
  -- A curve `g` with values in `𝒲` is extended by `g(a)`: the extension is a candidate bounded by
  -- `B`, and `T^g_t` are its positions.
  have hext {g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]} (hg : ∀ t, g t ∈ 𝒲) :
      Continuous (IccExtend ha.le ⇑g) ∧ ∀ τ, ‖IccExtend ha.le (⇑g) τ‖ ≤ B :=
    ⟨g.continuous.Icc_extend', fun _ ↦ witness_set_norm_le hB (hg _)⟩
  have hpos {g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]} (hg : ∀ t, g t ∈ 𝒲) (t : ℝ) :
      AEMeasurable (trajectory Φ (IccExtend ha.le ⇑g) 0 · t) ρ ∧
        ∀ᵐ x ∂ρ, trajectory Φ (IccExtend ha.le ⇑g) 0 x t ∈ Ω :=
    ⟨(continuous_trajectory_apply (hext hg).1 (hext hg).2 hK.lipschitzWith 0 t).aemeasurable,
      hρ.mono fun _ hx ↦ trajectory_mem (hext hg).1 (hext hg).2 hK.lipschitzWith
        hK.eq_zero_of_mem_frontier hx t⟩
  -- The map `G g(t) = φ*_{(T^g_t)#ρ}`, on raw curves.
  let F (g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]) (t : Icc (0 : ℝ) a) : 𝓗[d, H₀] :=
    steinWitness Φ s (ρ.map (trajectory Φ (IccExtend ha.le ⇑g) 0 · t))
  have hF𝒲 {g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]} (hg : ∀ t, g t ∈ 𝒲) (t : Icc (0 : ℝ) a) :
      F g t ∈ 𝒲 := by
    exact witness_set_steinWitness_mem hS ((ae_map_iff (hpos hg t).1
      hS.isCompact.measurableSet).2 (hpos hg t).2)
  -- The particles move at speed at most `B C` (Lemma 5 (ii)), so that, by Equation (5), the Stein
  -- witness changes by at most `ω(B C |t - t'|)` between the times `t` and `t'`.
  have hFpace {g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]} (hg : ∀ t, g t ∈ 𝒲) (t t' : Icc (0 : ℝ) a) :
      dist (F g t) (F g t') ≤ ω (B * C * dist t t') :=
    dist_steinWitness_map_le hS (hpos hg t).1 (hpos hg t').1 (hpos hg t).2 (hpos hg t').2
      (.of_forall fun x ↦ (positions_dist_le hS (hext hg).1 (hext hg).2 x t t').trans_eq
        (by rw [Subtype.dist_eq, Real.dist_eq]))
  have hFc {g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]} (hg : ∀ t, g t ∈ 𝒲) : Continuous (F g) :=
    Metric.continuous_iff.2 fun t ε hε ↦ by
      obtain ⟨δ, hδ, h⟩ := hωsmall (B * C) hε
      exact ⟨δ, hδ, fun t' ht' ↦ (hFpace hg t' t).trans_lt (h _ dist_nonneg ht')⟩
  -- The map `G` on bounded continuous curves.
  let G (g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]) : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀] :=
    if hg : ∀ t, g t ∈ 𝒲 then BoundedContinuousFunction.mkOfCompact ⟨F g, hFc hg⟩ else g
  have hG {g : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]} (hg : ∀ t, g t ∈ 𝒲) (t : Icc (0 : ℝ) a) :
      G g t = F g t := by
    simp [G, hg]
  -- A convex and compact set `Γ` of curves: those with values in `𝒲` that vary at the pace of the
  -- Stein witnesses.
  let Γ : Set (Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]) :=
    {g | (∀ t, g t ∈ 𝒲) ∧ ∀ t t', dist (g t) (g t') ≤ ω (B * C * dist t t')}
  have hΓne : Γ.Nonempty := by
    obtain ⟨x, hx⟩ := hρ.exists
    refine ⟨BoundedContinuousFunction.const _ (steinFeature Φ s x),
      fun _ ↦ subset_closedConvexHull (mem_image_of_mem _ hx), fun t t' ↦ ?_⟩
    simpa using hω₀ _
  have hΓconv : Convex ℝ Γ := by
    intro g₁ hg₁ g₂ hg₂ θ₁ θ₂ hθ₁ hθ₂ hθ
    refine ⟨fun t ↦ convex_closedConvexHull (hg₁.1 t) (hg₂.1 t) hθ₁ hθ₂ hθ, fun t t' ↦ ?_⟩
    simp only [add_apply, smul_apply, dist_eq_norm]
    calc ‖θ₁ • g₁ t + θ₂ • g₂ t - (θ₁ • g₁ t' + θ₂ • g₂ t')‖
        = ‖θ₁ • (g₁ t - g₁ t') + θ₂ • (g₂ t - g₂ t')‖ := by
          congr 1
          simp only [smul_sub]
          abel
      _ ≤ θ₁ * ‖g₁ t - g₁ t'‖ + θ₂ * ‖g₂ t - g₂ t'‖ := (norm_add_le _ _).trans (by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hθ₁, Real.norm_of_nonneg hθ₂])
      _ ≤ θ₁ * ω (B * C * dist t t') + θ₂ * ω (B * C * dist t t') := by
          rw [← dist_eq_norm, ← dist_eq_norm]
          gcongr
          exacts [hg₁.2 t t', hg₂.2 t t']
      _ = ω (B * C * dist t t') := by rw [← add_mul, hθ, one_mul]
  have hΓc : IsClosed Γ := by
    simp only [Γ, ofPred_and, ofPred_forall]
    exact (isClosed_iInter fun t ↦ h𝒲.isClosed.preimage
      (continuous_eval_const t)).inter
        (isClosed_iInter fun t ↦ isClosed_iInter fun t' ↦ isClosed_le
          ((continuous_eval_const t).dist
            (continuous_eval_const t')) continuous_const)
  -- By the Arzelà–Ascoli theorem, `Γ` is compact: its curves take their values in the compact set
  -- `𝒲` and are equicontinuous, as `ω(r)` tends to `0` as `r` tends to `0`.
  have hΓK : IsCompact Γ :=
    BoundedContinuousFunction.arzela_ascoli₂ 𝒲 h𝒲 Γ hΓc (fun g t hg ↦ hg.1 t)
      (Metric.uniformEquicontinuous_iff.2 fun ε hε ↦ by
        obtain ⟨δ, hδ, h⟩ := hωsmall (B * C) hε
        exact ⟨δ, hδ, fun t t' htt' g ↦ (g.2.2 t t').trans_lt (h _ dist_nonneg htt')⟩).equicontinuous
  -- The map `G` sends `Γ` into `Γ`.
  have hGΓ : MapsTo G Γ Γ := fun g hg ↦
    ⟨fun t ↦ (hG hg.1 t).symm ▸ hF𝒲 hg.1 t, fun t t' ↦ by
      rw [hG hg.1, hG hg.1]
      exact hFpace hg.1 t t'⟩
  -- Equation (6): two close curves give close positions (Lemma 5 (iii)), and close positions give
  -- close Stein witnesses (Equation (5)).
  set c := a * C * Real.exp (B * K * a)
  have hGcont {g g' : Icc (0 : ℝ) a →ᵇ 𝓗[d, H₀]} (hg : ∀ t, g t ∈ 𝒲) (hg' : ∀ t, g' t ∈ 𝒲) :
      dist (G g) (G g') ≤ ω (c * dist g g') := by
    refine (BoundedContinuousFunction.dist_le (hω₀ _)).2 fun t ↦ ?_
    rw [hG hg, hG hg']
    refine dist_steinWitness_map_le hS (hpos hg t).1 (hpos hg' t).1 (hpos hg t).2 (hpos hg' t).2
      (.of_forall fun x ↦ ?_)
    have hpt := positions_dist_le_of_dist_le hS (hext hg).1 (hext hg).2 (hext hg').1 (hext hg').2
      (Δ := dist g g') t.2.1 (fun r hr ↦ ?_) x
    · refine hpt.trans ?_
      have ht : (t : ℝ) ≤ a := t.2.2
      have hBK : (0 : ℝ) ≤ B * K := by positivity
      calc (C : ℝ) * (t : ℝ) * Real.exp (B * K * (t : ℝ)) * dist g g'
          ≤ C * a * Real.exp (B * K * a) * dist g g' := by gcongr
        _ = c * dist g g' := by ring
    · have hra : r ∈ Icc (0 : ℝ) a := ⟨hr.1, hr.2.trans t.2.2⟩
      rw [IccExtend_of_mem ha.le _ hra, IccExtend_of_mem ha.le _ hra]
      exact BoundedContinuousFunction.dist_coe_le_dist _
  -- The map `G` is continuous on `Γ`, as `ω(r)` tends to `0` as `r` tends to `0`.
  have hGc : ContinuousOn G Γ := Metric.continuousOn_iff.2 fun g hg ε hε ↦ by
    obtain ⟨δ, hδ, h⟩ := hωsmall c hε
    exact ⟨δ, hδ, fun g' hg' hgg' ↦ (hGcont hg'.1 hg.1).trans_lt (h _ dist_nonneg hgg')⟩
  -- By Theorem 5, `G` has a fixed point in `Γ`.
  obtain ⟨⟨g, hgΓ⟩, hfix⟩ := schauder hΓK hΓconv hΓne ⟨hGΓ.restrict G Γ Γ, hGc.mapsToRestrict hGΓ⟩
  have hGg : G g = g := congrArg Subtype.val hfix
  exact ⟨g, hgΓ.1, fun t ↦ (DFunLike.congr_fun hGg t).symm.trans (hG hgΓ.1 t)⟩

/-! ### Section 6.7: From a bounded time interval to all times -/

/-- **Theorem 4 (Existence of the continuous-time dynamics).** Suppose that the standing
assumptions hold, and let `ρ₀ ∈ 𝒫(Ω)`. Then, there is a family `(T_t)_{t ≥ 0}` of maps from `ℝᵈ` to
`ℝᵈ` that solves Equation (3). -/
theorem exists_continuous_time_dynamics [CompleteSpace H₀]
    (hS : StandingAssumptions Ω π p s Φ K C) {ρ₀ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ρ₀] (hρ₀ : ∀ᵐ x ∂ρ₀, x ∈ Ω) :
    ∃ T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), IsSolution Φ s Ω ρ₀ T := by
  set 𝒲 := witnessSet Φ s Ω
  have hK := hS.kernel
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  obtain ⟨B, hB⟩ := xi_regularity_exists_bound hS
  -- Lemma 8 with `a = 1`, from every distribution of `𝒫(Ω)`.
  have hstep (ν : Measure (EuclideanSpace ℝ (Fin d))) :
      ∃ g : Icc (0 : ℝ) 1 →ᵇ 𝓗[d, H₀], IsProbabilityMeasure ν → (∀ᵐ x ∂ν, x ∈ Ω) →
        (∀ t, g t ∈ 𝒲) ∧
          ∀ t, g t = steinWitness Φ s (ν.map (trajectory Φ (IccExtend h01 ⇑g) 0 · t)) := by
    by_cases h : IsProbabilityMeasure ν ∧ ∀ᵐ x ∂ν, x ∈ Ω
    · have := h.1
      obtain ⟨g, hg⟩ := consistent_candidate_bounded_interval hS h.2 one_pos
      exact ⟨g, fun _ _ ↦ hg⟩
    · exact ⟨0, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩
  choose step hstep using hstep
  -- The distributions `ρₙ` at the integer times, and the pieces `gₙ` of the candidate.
  let ρn : ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun n ↦ Nat.rec ρ₀
    (fun _ ρk ↦ ρk.map (trajectory Φ (IccExtend h01 ⇑(step ρk)) 0 · 1)) n
  have hρsucc (n : ℕ) :
      ρn (n + 1) = (ρn n).map (trajectory Φ (IccExtend h01 ⇑(step (ρn n))) 0 · 1) :=
    rfl
  let g (n : ℕ) : ℝ → 𝓗[d, H₀] := IccExtend h01 ⇑(step (ρn n))
  have hgc (n : ℕ) : Continuous (g n) := (step (ρn n)).continuous.Icc_extend'
  have hP (n : ℕ) : IsProbabilityMeasure (ρn n) ∧ ∀ᵐ x ∂ρn n, x ∈ Ω := by
    induction n with
    | zero => exact ⟨inferInstanceAs (IsProbabilityMeasure ρ₀), hρ₀⟩
    | succ n ih =>
      have := ih.1
      have hgB (t : ℝ) : ‖g n t‖ ≤ B := witness_set_norm_le hB ((hstep _ ih.1 ih.2).1 _)
      refine ⟨by rw [hρsucc]; infer_instance, ?_⟩
      rw [hρsucc]
      exact ae_map_trajectory_mem (hgc n) hgB hK.lipschitzWith hS.isCompact.measurableSet
        hK.eq_zero_of_mem_frontier ih.2 0 1
  have hg𝒲 (n : ℕ) (t : ℝ) : g n t ∈ 𝒲 := (hstep _ (hP n).1 (hP n).2).1 _
  have hgB (n : ℕ) (t : ℝ) : ‖g n t‖ ≤ B := witness_set_norm_le hB (hg𝒲 n t)
  have hgfix (n : ℕ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
      g n r = steinWitness Φ s ((ρn n).map (trajectory Φ (g n) 0 · r)) := by
    have := (hstep _ (hP n).1 (hP n).2).2 ⟨r, hr⟩
    change IccExtend h01 ⇑(step (ρn n)) r = _
    rw [IccExtend_of_mem h01 (⇑(step (ρn n))) hr]
    exact this
  -- The pieces agree at the integer times: `gₙ(1) = φ*_{ρₙ₊₁} = gₙ₊₁(0)`.
  have hjoin (n : ℕ) : g n 1 = g (n + 1) 0 := by
    rw [hgfix n ⟨zero_le_one, le_rfl⟩, hgfix (n + 1) ⟨le_rfl, zero_le_one⟩, ← hρsucc]
    have hid : (trajectory Φ (g (n + 1)) 0 · 0) = id :=
      funext (positions_zero hS (hgc (n + 1)) (hgB (n + 1)))
    rw [hid, Measure.map_id]
  -- The glued candidate `m(t) = gₙ(t - n)` for `t ∈ [n, n + 1]`.
  let m : ℝ → 𝓗[d, H₀] := fun t ↦ g ⌊t⌋₊ (t - ⌊t⌋₊)
  have hm (n : ℕ) : EqOn m (fun t ↦ g n (t - n)) (Icc n (n + 1)) := by
    intro t ht
    rcases ht.2.lt_or_eq with hlt | heq
    · have : ⌊t⌋₊ = n := (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans ht.1)).2 ⟨ht.1, hlt⟩
      simp only [m, this]
    · have hfl : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by exact_mod_cast Nat.floor_natCast (n + 1)
      subst heq
      simp only [m, hfl]
      push_cast
      rw [sub_self, add_sub_cancel_left]
      exact (hjoin n).symm
  have hm₀ : EqOn m (fun t ↦ g 0 (t - (0 : ℕ))) (Iic 1) := by
    intro t ht
    rcases ht.lt_or_eq with hlt | heq
    · simp only [m, Nat.floor_eq_zero.2 hlt]
    · exact hm 0 ⟨by simp [heq], by simp [heq]⟩
  have hmc : Continuous m :=
    continuous_of_eqOn_Icc_nat (fun n ↦ (hgc n).comp (continuous_sub_right _)) hm₀ hm
  have hm𝒲 (t : ℝ) : m t ∈ 𝒲 := hg𝒲 _ _
  have hmB (t : ℝ) : ‖m t‖ ≤ B := witness_set_norm_le hB (hm𝒲 t)
  -- Between the times `n` and `n + 1`, the particles follow the velocity field of `gₙ`:
  -- `T^m_t = T^{gₙ}_{t - n} ∘ T^m_n`.
  have hflow (n : ℕ) {t : ℝ} (ht : t ∈ Icc (n : ℝ) (n + 1)) (x : EuclideanSpace ℝ (Fin d)) :
      trajectory Φ m 0 x t = trajectory Φ (g n) 0 (trajectory Φ m 0 x n) (t - n) := by
    have hmn : Continuous fun r ↦ m (r + n) := hmc.comp (continuous_id.add continuous_const)
    calc trajectory Φ m 0 x t = trajectory Φ m n (trajectory Φ m 0 x n) t :=
          (congrFun (trajectory_trajectory hmc hmB hK.lipschitzWith 0 n x) t).symm
      _ = trajectory Φ (fun r ↦ m (r + n)) 0 (trajectory Φ m 0 x n) (t - n) := by
          rw [trajectory_comp_add hmc hmB hK.lipschitzWith, sub_add_cancel]
      _ = trajectory Φ (g n) 0 (trajectory Φ m 0 x n) (t - n) := by
          refine trajectory_eq_of_eqOn hmn (fun r ↦ hmB _) hK.lipschitzWith (hgc n) (hgB n)
            (fun r hr ↦ ?_) _
          rw [uIcc_of_le (by linarith [ht.1])] at hr
          have hmem : r + n ∈ Icc (n : ℝ) (n + 1) := ⟨by linarith [hr.1], by linarith [hr.2, ht.2]⟩
          simpa using hm n hmem
  -- By induction, `(T^m_n)#ρ₀ = ρₙ`.
  have hρ (n : ℕ) : ρ₀.map (trajectory Φ m 0 · n) = ρn n := by
    induction n with
    | zero =>
      have hid : (trajectory Φ m 0 · ((0 : ℕ) : ℝ)) = id := funext fun x ↦ by
        rw [Nat.cast_zero]
        exact positions_zero hS hmc hmB x
      rw [hid, Measure.map_id]
      rfl
    | succ n ih =>
      have heq : (trajectory Φ m 0 · ((n + 1 : ℕ) : ℝ)) =
          (trajectory Φ (g n) 0 · 1) ∘ (trajectory Φ m 0 · (n : ℝ)) := funext fun x ↦ by
        rw [Function.comp_apply, hflow n ⟨by push_cast; linarith, by push_cast; linarith⟩ x]
        push_cast
        ring_nf
      rw [heq, ← Measure.map_map
        (continuous_trajectory_apply (hgc n) (hgB n) hK.lipschitzWith 0 1).measurable
        (continuous_trajectory_apply hmc hmB hK.lipschitzWith 0 n).measurable, ih, hρsucc]
  -- The candidate `m` is consistent, and Lemma 7 concludes.
  refine ⟨_, consistent_candidate_isSolution hS hρ₀ hmc hm𝒲 fun t ht ↦ ?_⟩
  set n := ⌊t⌋₊
  have htn : t ∈ Icc (n : ℝ) (n + 1) := ⟨Nat.floor_le ht, (Nat.lt_floor_add_one t).le⟩
  calc m t = g n (t - n) := hm n htn
    _ = steinWitness Φ s ((ρn n).map (trajectory Φ (g n) 0 · (t - n))) :=
        hgfix n ⟨by linarith [htn.1], by linarith [htn.2]⟩
    _ = fixedPointMap Φ s ρ₀ m t := by
        rw [fixedPointMap, ← hρ n, Measure.map_map
          (continuous_trajectory_apply (hgc n) (hgB n) hK.lipschitzWith 0 (t - n)).measurable
          (continuous_trajectory_apply hmc hmB hK.lipschitzWith 0 n).measurable]
        exact congrArg (fun T ↦ steinWitness Φ s (ρ₀.map T)) (funext fun x ↦ (hflow n htn x).symm)

/-! ### Section 6.8: Properties of the solutions -/

/-- The curve `m(t) = φ*_{ρ_t}` of the Stein witnesses of a family `(T_t)_{t ≥ 0}`, where
`ρ_t = (T_t)#ρ₀` (Lemma 9). It is extended to negative times by `m(0)`. -/
def witnessCurve (Φ : EuclideanSpace ℝ (Fin d) → H₀)
    (s : EuclideanSpace ℝ (Fin d) → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))
    (ρ₀ : Measure (EuclideanSpace ℝ (Fin d)))
    (T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (t : ℝ) : 𝓗[d, H₀] :=
  steinWitness Φ s (ρ₀.map (T (max t 0)))

section SolutionProperties

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
  {ρ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ρ₀]
  {T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : IsSolution Φ s Ω ρ₀ T)
include hS hT

omit [CompleteSpace H₀] in
/-- The particles of a solution move at speed at most `B C` (proof of Lemma 9). -/
private theorem IsSolution.dist_le {B : ℝ≥0} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin d)) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    dist (T t x) (T t' x) ≤ B * C * |t - t'| := by
  wlog h : t ≤ t' generalizing t t'
  · rw [dist_comm, abs_sub_comm]
    exact this ht' ht (le_of_not_ge h)
  have hd (τ : ℝ) (hτ : τ ∈ Icc t t') :
      HasDerivWithinAt (T · x) (drift Φ s (ρ₀.map (T τ)) (T τ x)) (Icc t t') τ :=
    (hT.hasDerivWithinAt x τ (ht.trans hτ.1)).mono fun r hr ↦ ht.trans hr.1
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd (fun τ hτ ↦
    norm_toVectorField_steinWitness_le hS hB (hT.ae_mem τ (ht.trans hτ.1)) _) t' ⟨h, le_rfl⟩
  rwa [dist_comm, dist_eq_norm, abs_of_nonpos (sub_nonpos.2 h), neg_sub]

/-- **Lemma 9 (Properties of the solutions)**, (i). Suppose that the standing assumptions hold,
let `ρ₀ ∈ 𝒫(Ω)`, let `(T_t)_{t ≥ 0}` solve Equation (3), and let `m(t) = φ*_{ρ_t}`. Then,
`‖m(t) - m(t')‖_𝓗 ≤ ω(B C |t - t'|)` for all `t, t' ≥ 0`. -/
theorem solution_properties_dist_le {B : ℝ≥0} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    dist (witnessCurve Φ s ρ₀ T t) (witnessCurve Φ s ρ₀ T t') ≤
      modulusOfContinuityOn (steinFeature Φ s) Ω (B * C * |t - t'|) := by
  have hΩm := hS.isCompact.measurableSet
  -- By Equation (5), as the particles move by at most `B C |t - t'|`.
  rw [witnessCurve, witnessCurve, max_eq_left ht, max_eq_left ht']
  exact dist_steinWitness_map_le hS (hT.continuous t ht).aemeasurable
    (hT.continuous t' ht').aemeasurable
    ((ae_map_iff (hT.continuous t ht).aemeasurable hΩm).1 (hT.ae_mem t ht))
    ((ae_map_iff (hT.continuous t' ht').aemeasurable hΩm).1 (hT.ae_mem t' ht'))
    (.of_forall fun x ↦ hT.dist_le hS hB x ht ht')

/-- **Lemma 9 (Properties of the solutions)**, (i). The curve `m` of the Stein witnesses of a
solution is continuous. -/
theorem solution_properties_continuous : Continuous (witnessCurve Φ s ρ₀ T) := by
  obtain ⟨B, hB⟩ := xi_regularity_exists_bound hS
  -- As `ω(r)` tends to `0` as `r` tends to `0`.
  refine Metric.continuous_iff.2 fun t ε hε ↦ ?_
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_modulusOfContinuityOn_mul_lt
    (xi_regularity_uniformContinuousOn hS) (B * C) hε
  refine ⟨δ, hδ, fun t' ht' ↦ ?_⟩
  have hmax (τ : ℝ) : witnessCurve Φ s ρ₀ T τ = witnessCurve Φ s ρ₀ T (max τ 0) := by
    simp [witnessCurve]
  have hd : |max t' 0 - max t 0| ≤ dist t' t := by
    rw [Real.dist_eq]
    exact abs_max_sub_max_le_abs t' t 0
  rw [hmax t', hmax t]
  refine (solution_properties_dist_le hS hT hB (le_max_right _ _) (le_max_right _ _)).trans_lt
    ((monotone_modulus_steinFeature hS (by gcongr)).trans_lt (h _ dist_nonneg ht'))

omit [CompleteSpace H₀] in
/-- The Stein witnesses of a solution are bounded (Section 4.3). -/
private theorem exists_norm_witnessCurve_le : ∃ B : ℝ≥0, ∀ t, ‖witnessCurve Φ s ρ₀ T t‖ ≤ B := by
  obtain ⟨B, hB⟩ := xi_regularity_exists_bound hS
  exact ⟨B, fun t ↦ norm_steinWitness_le hB (hT.ae_mem _ (le_max_right t 0))⟩

/-- **Lemma 9 (Properties of the solutions)**, (ii). For every `t ≥ 0`, `T_t = T^m_t`, the
positions of Lemma 5 for the curve `m` of the Stein witnesses. -/
theorem solution_properties_eq_positions {t : ℝ} (ht : 0 ≤ t) :
    T t = (trajectory Φ (witnessCurve Φ s ρ₀ T) 0 · t) := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  -- `t ↦ T_t(x)` solves the equation of Lemma 5 for `m`, from `x`: by uniqueness, it is `T^m_t(x)`.
  funext x
  refine positions_unique hS (solution_properties_continuous hS hT) hmB (α := (T · x))
    (congrFun hT.zero x) (fun τ hτ ↦ ?_) ht
  have hm : witnessCurve Φ s ρ₀ T τ = steinWitness Φ s (ρ₀.map (T τ)) := by
    rw [witnessCurve, max_eq_left hτ]
  rw [hm]
  exact hT.hasDerivWithinAt x τ hτ

/-- **Lemma 9 (Properties of the solutions)**, (iii). For every `t ≥ 0`, `T_t` is a homeomorphism
of `ℝᵈ`. -/
theorem solution_properties_isHomeomorph {t : ℝ} (ht : 0 ≤ t) : IsHomeomorph (T t) := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  rw [solution_properties_eq_positions hS hT ht]
  exact positions_isHomeomorph hS (solution_properties_continuous hS hT) hmB t

/-- **Lemma 9 (Properties of the solutions)**, (iii). For every `t ≥ 0`, `T_t(Ω) = Ω`. -/
theorem solution_properties_image {t : ℝ} (ht : 0 ≤ t) : T t '' Ω = Ω := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  rw [solution_properties_eq_positions hS hT ht]
  exact positions_image hS (solution_properties_continuous hS hT) hmB t

/-- **Lemma 9 (Properties of the solutions)**, (iv). The points of `∂Ω` are at rest:
`T_t(z) = z` for all `z ∈ ∂Ω` and `t ≥ 0`. -/
theorem solution_properties_boundary {z : EuclideanSpace ℝ (Fin d)} (hz : z ∈ frontier Ω)
    {t : ℝ} (ht : 0 ≤ t) : T t z = z := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  -- The constant curve equal to `z` solves the equation of Lemma 5 for `m`, from `z`.
  rw [solution_properties_eq_positions hS hT ht]
  refine (positions_unique hS (solution_properties_continuous hS hT) hmB (α := fun _ ↦ z) rfl
    (fun τ _ ↦ ?_) ht).symm
  rw [hS.kernel.toVectorField_eq_zero _ hz]
  exact hasDerivWithinAt_const _ _ _

end SolutionProperties

/-! ## Section 7: The time derivative of the KL divergence

### Section 7.1: Decrease of the Kullback–Leibler divergence

Theorem 6 (Time derivative of the KL divergence) is proved in Section 7.4
(`SVGD.time_derivative_kl`).

### Section 7.2: Strategy of the proof

The velocity field of the particles at time `t` is `v_t = b(·, ρ_t) = m(t)_Φ`, where `m` is the
curve of the Stein witnesses (`SVGD.witnessCurve`), and `J_t(x) = det DT_t(x)`.

### Section 7.3: The Jacobian of `T_t` -/

section Jacobian

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
  {ρ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ρ₀]
  {T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : IsSolution Φ s Ω ρ₀ T)
include hS hT

/-- **Lemma 10 (Jacobian of `T_t`)**, differentiability. Suppose that the standing assumptions
hold, and let `(T_t)_{t ≥ 0}` solve Equation (3). For every `t ≥ 0`, `T_t` is differentiable on
`ℝᵈ`. -/
theorem jacobian_differentiable {t : ℝ} (ht : 0 ≤ t) : Differentiable ℝ (T t) := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  rw [solution_properties_eq_positions hS hT ht]
  exact differentiable_trajectory_apply hS.kernel.contDiff hS.kernel.lipschitzWith
    (solution_properties_continuous hS hT) hmB t

/-- **Lemma 10 (Jacobian of `T_t`)**, (i). `J_t(x) > 0`. -/
theorem jacobian_pos (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    0 < (fderiv ℝ (T t) x).det := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  rw [solution_properties_eq_positions hS hT ht]
  exact det_fderiv_trajectory_pos hS.kernel.contDiff hS.kernel.lipschitzWith
    (solution_properties_continuous hS hT) hmB x t

/-- **Lemma 10 (Jacobian of `T_t`)**, (ii). `∂ₜ log J_t(x) = ∇ · v_t(T_t(x))`, with a right
derivative at `t = 0`. -/
theorem jacobian_hasDerivWithinAt (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ Real.log (fderiv ℝ (T t) x).det)
      (divergence ℝ (drift Φ s (ρ₀.map (T t))) (T t x)) (Ici 0) t := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  have h := hasDerivAt_log_det_fderiv_trajectory hS.kernel.contDiff hS.kernel.lipschitzWith
    (solution_properties_continuous hS hT) hmB x t
  have hm : witnessCurve Φ s ρ₀ T t = steinWitness Φ s (ρ₀.map (T t)) := by
    rw [witnessCurve, max_eq_left ht]
  have hTt : T t x = trajectory Φ (witnessCurve Φ s ρ₀ T) 0 x t :=
    congrFun (solution_properties_eq_positions hS hT ht) x
  rw [hm, ← hTt] at h
  exact h.hasDerivWithinAt.congr
    (fun τ hτ ↦ by simp only [solution_properties_eq_positions hS hT hτ])
    (by simp only [solution_properties_eq_positions hS hT ht])

/-- **Lemma 10 (Jacobian of `T_t`)**, (iii). `|log J_t(x)| ≤ d B K t`, where `B` bounds `‖ξ_x‖_𝓗`
on `Ω`. -/
theorem jacobian_abs_log_le {B : ℝ≥0} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    |Real.log (fderiv ℝ (T t) x).det| ≤ d * B * K * t := by
  have hmB (τ : ℝ) : ‖witnessCurve Φ s ρ₀ T τ‖ ≤ B :=
    norm_steinWitness_le hB (hT.ae_mem _ (le_max_right τ 0))
  rw [solution_properties_eq_positions hS hT ht]
  have := abs_log_det_fderiv_trajectory_le hS.kernel.contDiff hS.kernel.lipschitzWith
    (solution_properties_continuous hS hT) hmB x t
  rwa [abs_of_nonneg ht, ← mul_assoc] at this

end Jacobian

/-! ### Section 7.4: Differentiation of the KL divergence -/

section TimeDerivativeKL

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
  {ρ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ρ₀] (hKL : klDiv ρ₀ π ≠ ∞)
  {T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : IsSolution Φ s Ω ρ₀ T)
include hS hKL hT

/-- **Theorem 6 (Time derivative of the KL divergence)**, finiteness. Suppose that the standing
assumptions hold. Let `ρ₀` be a probability measure with `KL(ρ₀ ‖ π) < ∞`, let `(T_t)_{t ≥ 0}`
solve Equation (3), and let `ρ_t = (T_t)#ρ₀`. Then, `KL(ρ_t ‖ π) < ∞` for every `t ≥ 0`. -/
theorem time_derivative_kl_ne_top {t : ℝ} (ht : 0 ≤ t) : klDiv (ρ₀.map (T t)) π ≠ ∞ := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  obtain ⟨hπ, -, hp, hpc, hp₀, -, -⟩ := hS.target
  -- By Lemma 9 (ii), Lemma 10 and Lemma 2.
  rw [solution_properties_eq_positions hS hT ht]
  subst hπ
  exact klDiv_map_trajectory_ne_top hS.isCompact hp hpc hp₀ hS.kernel.contDiff
    hS.kernel.lipschitzWith hS.kernel.eq_zero_of_mem_frontier
    (solution_properties_continuous hS hT) hmB hKL t

/-- **Theorem 6 (Time derivative of the KL divergence).** Under the same assumptions,
`t ↦ KL(ρ_t ‖ π)` is differentiable on `[0, ∞)`, with a right derivative at `0`, and
`d/dt KL(ρ_t ‖ π) = -𝔎(ρ_t ∣ π)`. -/
theorem time_derivative_kl {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ (klDiv (ρ₀.map (T t)) π).toReal) (-𝔎[Φ, s] (ρ₀.map (T t)))
      (Ici 0) t := by
  obtain ⟨B, hmB⟩ := exists_norm_witnessCurve_le hS hT
  obtain ⟨hπ, -, hp, hpc, hp₀, hs, hsc⟩ := hS.target
  -- Lemma 2 with `Ψ = T_t = T^m_t` (Lemma 9 (ii)), Lemma 10, and the Leibniz integral rule give
  -- `d/dt KL(ρ_t ‖ π) = -E_{y ∼ ρ_t}[𝒜_s v_t(y)]`.
  have h := hasDerivAt_toReal_klDiv_map_trajectory hS.isCompact hp hpc hp₀ hS.kernel.contDiff
    hS.kernel.lipschitzWith hS.kernel.eq_zero_of_mem_frontier
    (solution_properties_continuous hS hT) hmB (hπ ▸ hKL) hs hsc t
  rw [← hπ] at h
  refine (h.hasDerivWithinAt.congr
    (fun τ hτ ↦ by simp only [solution_properties_eq_positions hS hT hτ])
    (by simp only [solution_properties_eq_positions hS hT ht])).congr_deriv ?_
  -- As `v_t` is the vector field of the Stein witness of `ρ_t`, Theorem 2 (ii) gives
  -- `E_{y ∼ ρ_t}[𝒜_s v_t(y)] = 𝔎(ρ_t ∣ π)`.
  have hm : witnessCurve Φ s ρ₀ T t = steinWitness Φ s (ρ₀.map (T t)) := by
    rw [witnessCurve, max_eq_left ht]
  rw [← solution_properties_eq_positions hS hT ht, hm,
    stein_witness_ksd_eq_integral hS (hT.ae_mem t ht)]
  rfl

/-- **Theorem 6 (Time derivative of the KL divergence)**, monotonicity. `t ↦ KL(ρ_t ‖ π)` is
nonincreasing on `[0, ∞)`. -/
theorem time_derivative_kl_antitoneOn :
    AntitoneOn (fun t ↦ (klDiv (ρ₀.map (T t)) π).toReal) (Ici 0) := by
  -- As `𝔎(ρ_t ∣ π) ≥ 0`, by the mean value theorem.
  have hderiv {t : ℝ} (ht : 0 < t) := (time_derivative_kl hS hKL hT ht.le).hasDerivAt
    (Ici_mem_nhds ht)
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun t ht ↦ (time_derivative_kl hS hKL hT ht).continuousWithinAt)
    (fun t ht ↦ (hderiv (by simpa using ht)).differentiableAt.differentiableWithinAt)
    fun t ht ↦ ?_
  rw [(hderiv (by simpa using ht)).deriv, neg_nonpos]
  exact ksd_nonneg _

end TimeDerivativeKL

/-! ## Section 8: Convergence

### Section 8.1: Weak convergence and Stein-universal kernels

A sequence `(ρ_n)` of `𝒫(Ω)` converges weakly to `ρ ∈ 𝒫(Ω)` if `E_{x ∼ ρ_n}[g(x)] → E_{x ∼ ρ}[g(x)]`
for every `g ∈ C⁰(Ω)`. Here, `g ∈ C⁰(Ω)` is a function `g : ℝᵈ → ℝ` continuous on `Ω`, whose values
outside `Ω` do not matter, and the restriction `ρ|_Ω` of `ρ` to `Ω` is the measure
`ρ.comap ((↑) : Ω → ℝᵈ)` on the subtype `Ω`. -/

section KSDZero

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C) [IsProbabilityMeasure ρ]
  (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
include hS hρ

/-- **Equation (8)**, first equivalence. For `ρ ∈ 𝒫(Ω)`, `𝔎(ρ ∣ π) = 0 ⟺ φ*_ρ = 0`. -/
theorem ksd_eq_zero_iff : 𝔎[Φ, s] ρ = 0 ↔ steinWitness Φ s ρ = 0 := by
  rw [stein_witness_ksd hS hρ, sq_eq_zero_iff, norm_eq_zero]

/-- **Equation (8)**, second equivalence. For `ρ ∈ 𝒫(Ω)`,
`φ*_ρ = 0 ⟺ ∀ f ∈ 𝓗, E_{x ∼ ρ}[𝒜_s f_Φ(x)] = 0`. -/
theorem steinWitness_eq_zero_iff :
    steinWitness Φ s ρ = 0 ↔ ∀ f, ∫ x, steinOperator s (toVectorField Φ f) x ∂ρ = 0 := by
  simp_rw [stein_witness hS hρ]
  -- The converse implication follows by taking `f = φ*_ρ`.
  exact ⟨fun h f ↦ by rw [h, inner_zero_right], fun h ↦ by
    simpa [real_inner_self_eq_norm_sq] using h (steinWitness Φ s ρ)⟩

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

/-- The extension by `0` of a function of `C(Ω, ℝ)` is continuous on `Ω`. -/
private theorem continuousOn_dite (g : C(Ω, ℝ)) :
    ContinuousOn (fun x ↦ if hx : x ∈ Ω then g ⟨x, hx⟩ else 0) Ω := by
  rw [continuousOn_iff_continuous_restrict]
  convert g.continuous with x
  simp

/-- **Definition 3 (Stein-universal kernel)**, unfolded. Suppose that the standing assumptions
hold. The kernel is Stein-universal if and only if, for every `g ∈ C⁰(Ω)` and every `η > 0`, there
are `f ∈ 𝓗` and `c ∈ ℝ` such that `sup_{x ∈ Ω} |g(x) - 𝒜_s f_Φ(x) - c| ≤ η`. -/
theorem isSteinUniversal_iff (hS : StandingAssumptions Ω π p s Φ K C) :
    IsSteinUniversal Φ s Ω ↔ ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω → ∀ η > 0,
      ∃ f : 𝓗[d, H₀], ∃ c : ℝ, ∀ x ∈ Ω, |g x - steinOperator s (toVectorField Φ f) x - c| ≤ η := by
  refine ⟨fun hU g hg η hη ↦ ?_, fun h g ↦ Metric.mem_closure_iff.2 fun η hη ↦ ?_⟩
  · obtain ⟨_, ⟨f, c, hfc⟩, hdist⟩ := Metric.mem_closure_iff.1 (hU ⟨Ω.restrict g, hg.restrict⟩) η hη
    refine ⟨f, c, fun x hx ↦ ?_⟩
    have := (ContinuousMap.dist_apply_le_dist ⟨x, hx⟩).trans hdist.le
    simpa [hfc, Real.dist_eq, sub_add_eq_sub_sub] using this
  · obtain ⟨f, c, hfc⟩ := h _ (continuousOn_dite g) (η / 2) (half_pos hη)
    refine ⟨⟨fun x ↦ steinOperator s (toVectorField Φ f) x + c,
      ((continuousOn_steinOperator hS f).add continuousOn_const).restrict⟩, ⟨f, c, fun _ ↦ rfl⟩,
      ((ContinuousMap.dist_le (half_pos hη).le).2 fun x ↦ ?_).trans_lt (half_lt_self hη)⟩
    have := hfc x x.2
    simpa [Real.dist_eq, sub_add_eq_sub_sub] using this

/-- **Equation (9).** Suppose that the standing assumptions hold. The kernel is Stein-universal if
and only if, for every `g ∈ C⁰(Ω)` and every `η > 0`, there is `f ∈ 𝓗` such that
`sup_{x ∈ Ω} |g(x) - E_{y ∼ π}[g(y)] - 𝒜_s f_Φ(x)| ≤ η`. -/
theorem isSteinUniversal_iff_mean (hS : StandingAssumptions Ω π p s Φ K C) :
    IsSteinUniversal Φ s Ω ↔ ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω → ∀ η > 0,
      ∃ f : 𝓗[d, H₀], ∀ x ∈ Ω,
        |g x - ∫ y, g y ∂π - steinOperator s (toVectorField Φ f) x| ≤ η := by
  have := hS.target.isProbabilityMeasure
  have hπ := hS.target.ae_mem hS.isCompact
  rw [isSteinUniversal_iff hS]
  refine ⟨fun h g hg η hη ↦ ?_, fun h g hg η hη ↦ ?_⟩
  · -- Apply Definition 3 with `η / 2`. Integrating against `π`, `|E_π[g] - c| ≤ η / 2`, as
    -- `E_π[𝒜_s f_Φ] = 0` (Corollary 1).
    obtain ⟨f, c, hfc⟩ := h g hg (η / 2) (half_pos hη)
    have hA := stein_identity hS.isCompact hS.target (hS.kernel.contDiff_toVectorField f)
      (hS.kernel.lipschitzWith_toVectorField f) fun _ hy ↦ hS.kernel.toVectorField_eq_zero f hy
    have hAi := stein_identity_integrable hS.isCompact hS.target
      (hS.kernel.contDiff_toVectorField f) (hS.kernel.lipschitzWith_toVectorField f)
      fun _ hy ↦ hS.kernel.toVectorField_eq_zero f hy
    have hgi : Integrable g π := hg.integrable_of_ae_mem hS.isCompact hπ
    have hc : |∫ y, g y ∂π - c| ≤ η / 2 := by
      have hsub : ∫ y, g y ∂π - c =
          ∫ y, (g y - steinOperator s (toVectorField Φ f) y - c) ∂π := by
        rw [integral_sub (hgi.sub hAi) (integrable_const c), integral_sub hgi hAi, hA,
          integral_const]
        simp
      rw [hsub, ← Real.norm_eq_abs]
      exact (norm_integral_le_of_norm_le_const (C := η / 2)
        (hπ.mono fun x hx ↦ by simpa [Real.norm_eq_abs] using hfc x hx)).trans_eq (by simp)
    -- By the triangle inequality.
    refine ⟨f, fun x hx ↦ ?_⟩
    calc |g x - ∫ y, g y ∂π - steinOperator s (toVectorField Φ f) x|
        = |(g x - steinOperator s (toVectorField Φ f) x - c) - (∫ y, g y ∂π - c)| := by ring_nf
      _ ≤ |g x - steinOperator s (toVectorField Φ f) x - c| + |∫ y, g y ∂π - c| := abs_sub _ _
      _ ≤ η / 2 + η / 2 := add_le_add (hfc x hx) hc
      _ = η := add_halves η
  · -- Definition 3 holds with `c = E_π[g]`.
    obtain ⟨f, hf⟩ := h g hg η hη
    exact ⟨f, ∫ y, g y ∂π, fun x hx ↦ by simpa [sub_sub, add_comm] using hf x hx⟩

/-- **Proposition 1 (The KSD vanishes only at `π`).** Suppose that the standing assumptions hold,
and that the kernel is Stein-universal. Then, `𝔎(ρ ∣ π) = 0 ⟺ ρ = π` for every `ρ ∈ 𝒫(Ω)`. -/
theorem ksd_vanishes_only_at_target [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
    (hU : IsSteinUniversal Φ s Ω) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, x ∈ Ω) :
    𝔎[Φ, s] ρ = 0 ↔ ρ = π := by
  have := hS.target.isProbabilityMeasure
  have hπ := hS.target.ae_mem hS.isCompact
  refine ⟨fun hK ↦ ?_, fun h ↦ h ▸ ksd_target_eq_zero hS⟩
  -- By Equation (8), `E_ρ[𝒜_s f_Φ] = 0` for every `f ∈ 𝓗`.
  have h₀ := (steinWitness_eq_zero_iff hS hρ).1 ((ksd_eq_zero_iff hS hρ).1 hK)
  -- By Equation (9), `E_ρ[g] = E_π[g]` for every `g ∈ C⁰(Ω)`.
  have hg (g : EuclideanSpace ℝ (Fin d) → ℝ) (hgc : ContinuousOn g Ω) :
      ∫ x, g x ∂ρ = ∫ x, g x ∂π := eq_of_forall_dist_le fun η hη ↦ by
    obtain ⟨f, hf⟩ := (isSteinUniversal_iff_mean hS).1 hU g hgc η hη
    have hgi : Integrable g ρ := hgc.integrable_of_ae_mem hS.isCompact hρ
    have hAi : Integrable (steinOperator s (toVectorField Φ f)) ρ :=
      (continuousOn_steinOperator hS f).integrable_of_ae_mem hS.isCompact hρ
    have hsub : ∫ x, g x ∂ρ - ∫ y, g y ∂π =
        ∫ x, (g x - ∫ y, g y ∂π - steinOperator s (toVectorField Φ f) x) ∂ρ := by
      rw [integral_sub (hgi.sub (integrable_const _)) hAi, integral_sub hgi (integrable_const _),
        h₀ f, integral_const]
      simp
    rw [Real.dist_eq, hsub, ← Real.norm_eq_abs]
    exact (norm_integral_le_of_norm_le_const (C := η)
      (hρ.mono fun x hx ↦ by simpa [Real.norm_eq_abs] using hf x hx)).trans_eq (by simp)
  -- Thus, `ρ|_Ω` and `π|_Ω` are two probability measures on the metric space `Ω` that give the
  -- same integral to every bounded continuous function, hence are equal.
  have hΩm := hS.isCompact.measurableSet
  have hι := MeasurableEmbedding.subtypeVal hΩm
  have : IsProbabilityMeasure (ρ.comap ((↑) : Ω → EuclideanSpace ℝ (Fin d))) :=
    hι.isProbabilityMeasure_comap (by rwa [Subtype.range_coe])
  have : IsProbabilityMeasure (π.comap ((↑) : Ω → EuclideanSpace ℝ (Fin d))) :=
    hι.isProbabilityMeasure_comap (by rwa [Subtype.range_coe])
  have hres : ρ.comap ((↑) : Ω → EuclideanSpace ℝ (Fin d)) = π.comap (↑) :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure fun h ↦ by
      have := hg (fun x ↦ if hx : x ∈ Ω then h ⟨x, hx⟩ else 0) (continuousOn_dite h.toContinuousMap)
      rwa [← Measure.restrict_eq_self_of_ae_mem hρ, ← Measure.restrict_eq_self_of_ae_mem hπ,
        ← map_comap_subtypeVal hΩm, ← map_comap_subtypeVal hΩm, hι.integral_map,
        hι.integral_map] at this
  -- As `ρ` and `π` are determined by their restrictions to `Ω`, `ρ = π`.
  rw [← Measure.restrict_eq_self_of_ae_mem hρ, ← Measure.restrict_eq_self_of_ae_mem hπ,
    ← map_comap_subtypeVal hΩm, ← map_comap_subtypeVal hΩm, hres]

/-! ### Section 8.2: Convergence to the target distribution

Theorem 7 (Convergence to the target distribution) is proved in Section 8.6
(`SVGD.convergence_to_target`).

### Section 8.4: The KSD tends to zero -/

/-- **Lemma 11 (Barbalat).** Let `u : [0, ∞) → [0, ∞)` be uniformly continuous, and let `M` be such
that `∫₀ᵃ u(t) dt ≤ M` for every `a ≥ 0`. Then, `u(t) → 0` as `t → ∞`. -/
theorem barbalat {u : ℝ → ℝ} (hu : UniformContinuousOn u (Ici 0))
    (hu₀ : ∀ t ∈ Ici (0 : ℝ), 0 ≤ u t) {M : ℝ} (hM : ∀ a ∈ Ici (0 : ℝ), ∫ t in 0..a, u t ≤ M) :
    Tendsto u atTop (𝓝 0) :=
  tendsto_zero_of_uniformContinuousOn_of_integral_le hu hu₀ hM

section KSDConvergence

variable [CompleteSpace H₀] (hS : StandingAssumptions Ω π p s Φ K C)
  {ρ₀ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ρ₀]
  {T : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hT : IsSolution Φ s Ω ρ₀ T)
include hS hT

/-- **Lemma 12 (Uniform continuity of the KSD)**, bound. Suppose that the standing assumptions
hold, let `ρ₀ ∈ 𝒫(Ω)`, let `(T_t)_{t ≥ 0}` solve Equation (3), and let `ρ_t = (T_t)#ρ₀`. Then,
`|𝔎(ρ_t ∣ π) - 𝔎(ρ_{t'} ∣ π)| ≤ 2 B ω(B C |t - t'|)` for all `t, t' ≥ 0`. -/
theorem ksd_uniform_continuity_le {B : ℝ≥0} (hB : ∀ x ∈ Ω, ‖steinFeature Φ s x‖ ≤ B) {t t' : ℝ}
    (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    |𝔎[Φ, s] (ρ₀.map (T t)) - 𝔎[Φ, s] (ρ₀.map (T t'))| ≤
      2 * B * modulusOfContinuityOn (steinFeature Φ s) Ω (B * C * |t - t'|) := by
  -- `𝔎(ρ_t ∣ π) = ‖φ*_{ρ_t}‖²` (Theorem 2 (ii)), and every Stein witness has norm at most `B`.
  have h₁ := norm_steinWitness_le hB (hT.ae_mem t ht)
  have h₂ := norm_steinWitness_le hB (hT.ae_mem t' ht')
  have hd := solution_properties_dist_le hS hT hB ht ht'
  rw [witnessCurve, witnessCurve, max_eq_left ht, max_eq_left ht', dist_eq_norm] at hd
  rw [stein_witness_ksd hS (hT.ae_mem t ht), stein_witness_ksd hS (hT.ae_mem t' ht'), sq_sub_sq,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖steinWitness Φ s (ρ₀.map (T t))‖ +
      ‖steinWitness Φ s (ρ₀.map (T t'))‖)]
  calc (‖steinWitness Φ s (ρ₀.map (T t))‖ + ‖steinWitness Φ s (ρ₀.map (T t'))‖) *
        |‖steinWitness Φ s (ρ₀.map (T t))‖ - ‖steinWitness Φ s (ρ₀.map (T t'))‖|
      ≤ (2 * B) * ‖steinWitness Φ s (ρ₀.map (T t)) - steinWitness Φ s (ρ₀.map (T t'))‖ :=
        mul_le_mul (by linarith) (abs_norm_sub_norm_le _ _) (abs_nonneg _) (by positivity)
    _ ≤ 2 * B * modulusOfContinuityOn (steinFeature Φ s) Ω (B * C * |t - t'|) := by gcongr

/-- **Lemma 12 (Uniform continuity of the KSD).** `t ↦ 𝔎(ρ_t ∣ π)` is uniformly continuous on
`[0, ∞)`. -/
theorem ksd_uniform_continuity :
    UniformContinuousOn (fun t ↦ 𝔎[Φ, s] (ρ₀.map (T t))) (Ici 0) := by
  obtain ⟨B, hB⟩ := xi_regularity_exists_bound hS
  -- As `ω(r)` tends to `0` as `r` tends to `0`.
  refine Metric.uniformContinuousOn_iff.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, h⟩ := exists_pos_forall_modulusOfContinuityOn_mul_lt
    (xi_regularity_uniformContinuousOn hS) (B * C) (by positivity : 0 < ε / (2 * B + 1))
  refine ⟨δ, hδ, fun t ht t' ht' htt' ↦ ?_⟩
  have hω := h _ dist_nonneg htt'
  rw [Real.dist_eq] at hω ⊢
  calc |𝔎[Φ, s] (ρ₀.map (T t)) - 𝔎[Φ, s] (ρ₀.map (T t'))|
      ≤ 2 * B * modulusOfContinuityOn (steinFeature Φ s) Ω (B * C * |t - t'|) :=
        ksd_uniform_continuity_le hS hT hB ht ht'
    _ ≤ (2 * B + 1) * modulusOfContinuityOn (steinFeature Φ s) Ω (B * C * |t - t'|) := by
        gcongr
        · exact modulusOfContinuityOn_nonneg _ _ _
        · linarith
    _ < (2 * B + 1) * (ε / (2 * B + 1)) := by gcongr
    _ = ε := by field_simp

/-- **Corollary 2 (Convergence of the KSD).** Suppose that the standing assumptions hold. Let `ρ₀`
be a probability measure with `KL(ρ₀ ‖ π) < ∞`, let `(T_t)_{t ≥ 0}` solve Equation (3), and let
`ρ_t = (T_t)#ρ₀`. Then, `𝔎(ρ_t ∣ π) → 0` as `t → ∞`. -/
theorem ksd_convergence (hKL : klDiv ρ₀ π ≠ ∞) :
    Tendsto (fun t ↦ 𝔎[Φ, s] (ρ₀.map (T t))) atTop (𝓝 0) := by
  -- Let `F(t) = KL(ρ_t ‖ π)` and `u(t) = 𝔎(ρ_t ∣ π)`. By Theorem 6, `F' = -u`.
  have hF {t : ℝ} (ht : 0 ≤ t) := time_derivative_kl hS hKL hT ht
  have hu := ksd_uniform_continuity hS hT
  -- By the fundamental theorem of calculus, `∫₀ᵃ u = F(0) - F(a) ≤ F(0)`, and Lemma 11 applies.
  refine barbalat hu (fun _ _ ↦ ksd_nonneg _) (M := (klDiv (ρ₀.map (T 0)) π).toReal)
    fun a ha ↦ ?_
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (f := fun t ↦
    (klDiv (ρ₀.map (T t)) π).toReal) ha
    (fun t ht ↦ (hF ht.1).continuousWithinAt.mono Icc_subset_Ici_self)
    (fun t ht ↦ (hF ht.1.le).mono (Ioi_subset_Ici ht.1.le))
    ((hu.continuousOn.mono (uIcc_of_le ha ▸ Icc_subset_Ici_self)).intervalIntegrable.neg)
  rw [intervalIntegral.integral_neg] at hFTC
  linarith [ENNReal.toReal_nonneg (a := klDiv (ρ₀.map (T a)) π)]

/-! ### Section 8.5: Limit points of the dynamics -/

/-- **Lemma 13 (Limit points have a zero KSD).** Suppose that the standing assumptions hold. Let `ρ₀`
be a probability measure with `KL(ρ₀ ‖ π) < ∞`, let `(T_t)_{t ≥ 0}` solve Equation (3), and let
`ρ_t = (T_t)#ρ₀`. Let `t_n → ∞` and `ρ_∞ ∈ 𝒫(Ω)` be such that `ρ_{t_n} ⇀ ρ_∞`. Then,
`𝔎(ρ_∞ ∣ π) = 0`. -/
theorem limit_points_ksd_eq_zero (hKL : klDiv ρ₀ π ≠ ∞) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) {ρ_lim : Measure (EuclideanSpace ℝ (Fin d))}
    [IsProbabilityMeasure ρ_lim] (hρ_lim : ∀ᵐ x ∂ρ_lim, x ∈ Ω)
    (hconv : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn g Ω →
      Tendsto (fun n ↦ ∫ x, g x ∂ρ₀.map (T (t n))) atTop (𝓝 (∫ x, g x ∂ρ_lim))) :
    𝔎[Φ, s] ρ_lim = 0 := by
  -- For `f` in the closed unit ball of `𝓗`, `E_{ρ_∞}[𝒜_s f_Φ]² = lim E_{ρ_{t_n}}[𝒜_s f_Φ]²`, and
  -- `E_{ρ_{t_n}}[𝒜_s f_Φ]² ≤ 𝔎(ρ_{t_n} ∣ π) → 0` (Definition 2 and Corollary 2).
  have hterm (f : closedBall (0 : 𝓗[d, H₀]) 1) :
      (∫ x, steinOperator s (toVectorField Φ f) x ∂ρ_lim) ^ 2 = 0 := by
    have hlim := (hconv _ (continuousOn_steinOperator hS f)).pow 2
    refine le_antisymm (le_of_tendsto_of_tendsto hlim ((ksd_convergence hS hT hKL).comp ht) ?_)
      (sq_nonneg _)
    filter_upwards [ht.eventually_ge_atTop 0] with n hn
    exact sq_integral_steinOperator_le_ksd hS (hT.ae_mem _ hn) (mem_closedBall_zero_iff.1 f.2)
  -- Thus, every term of the supremum of Definition 2 vanishes.
  simp [kernelSteinDiscrepancy, hterm]

/-! ### Section 8.6: Identification of the limit -/

/-- **Theorem 7 (Convergence to the target distribution).** Suppose that the standing assumptions
hold, and that the kernel is Stein-universal. Let `ρ₀` be a probability measure with
`KL(ρ₀ ‖ π) < ∞`, let `(T_t)_{t ≥ 0}` solve Equation (3), and let `ρ_t = (T_t)#ρ₀`. Then, `ρ_t`
converges weakly to `π`: `E_{x ∼ ρ_t}[g(x)] → E_{x ∼ π}[g(x)]` for every `g ∈ C⁰(Ω)`. -/
theorem convergence_to_target (hU : IsSteinUniversal Φ s Ω) (hKL : klDiv ρ₀ π ≠ ∞)
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : ContinuousOn g Ω) :
    Tendsto (fun t ↦ ∫ x, g x ∂ρ₀.map (T t)) atTop (𝓝 (∫ x, g x ∂π)) := by
  have : CompactSpace Ω := isCompact_iff_compactSpace.1 hS.isCompact
  have hΩm := hS.isCompact.measurableSet
  have hι := MeasurableEmbedding.subtypeVal hΩm
  -- The restriction `ρ_t|_Ω` of `ρ_t`, a probability measure on `Ω` (extended by `ρ₀` before `0`).
  let u (t : ℝ) : ProbabilityMeasure Ω :=
    ⟨(ρ₀.map (T (max t 0))).comap (↑), hι.isProbabilityMeasure_comap (by
      rw [Subtype.range_coe]
      exact hT.ae_mem _ (le_max_right t 0))⟩
  have hu {t : ℝ} (ht : 0 ≤ t) : (u t : Measure Ω).map (↑) = ρ₀.map (T t) := by
    rw [ProbabilityMeasure.coe_mk, map_comap_subtypeVal hΩm, max_eq_left ht,
      Measure.restrict_eq_self_of_ae_mem (hT.ae_mem t ht)]
  -- Weak convergence in `𝒫(Ω)` gives the convergence of `E[g]` for every `g ∈ C⁰(Ω)`.
  have hweak {ν : ℕ → ProbabilityMeasure Ω} {ν' : ProbabilityMeasure Ω}
      (hν : Tendsto ν atTop (𝓝 ν')) (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : ContinuousOn g Ω) :
      Tendsto (fun n ↦ ∫ x, g x ∂(ν n : Measure Ω).map (↑)) atTop
        (𝓝 (∫ x, g x ∂(ν' : Measure Ω).map (↑))) := by
    have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν
      (BoundedContinuousFunction.mkOfCompact ⟨Ω.restrict g, hg.restrict⟩)
    simp only [hι.integral_map]
    exact this
  -- It is enough that every sequence `t_n → ∞` has a subsequence along which `E_{ρ_t}[g]` tends
  -- to `E_π[g]`.
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  -- By Prokhorov's theorem, `(ρ_{t_n}|_Ω)` has a weakly convergent subsequence, with limit `ρ_∞`.
  obtain ⟨ρ_lim, -, ψ, hψ, hlim⟩ := isCompact_univ.tendsto_subseq (x := fun n ↦ u (ns n))
    fun _ ↦ mem_univ _
  have hτ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
  have hev : ∀ᶠ k in atTop, ((u (ns (ψ k)) : Measure Ω).map (↑)) = ρ₀.map (T ((ns ∘ ψ) k)) :=
    (hτ.eventually_ge_atTop 0).mono fun k hk ↦ hu hk
  -- Its limit has a zero KSD (Lemma 13), hence is `π` (Proposition 1).
  have hlim' (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : ContinuousOn g Ω) :
      Tendsto (fun k ↦ ∫ x, g x ∂ρ₀.map (T ((ns ∘ ψ) k))) atTop
        (𝓝 (∫ x, g x ∂(ρ_lim : Measure Ω).map (↑))) :=
    (hweak hlim g hg).congr' (hev.mono fun k hk ↦ by rw [Function.comp_apply, hk])
  have hπ : (ρ_lim : Measure Ω).map (↑) = π :=
    (ksd_vanishes_only_at_target hS hU (ae_map_subtypeVal_mem hΩm)).1
      (limit_points_ksd_eq_zero hS hT hKL hτ (ae_map_subtypeVal_mem hΩm) hlim')
  exact ⟨ψ, by simpa only [hπ] using hlim' g hg⟩

end KSDConvergence

end SVGD
