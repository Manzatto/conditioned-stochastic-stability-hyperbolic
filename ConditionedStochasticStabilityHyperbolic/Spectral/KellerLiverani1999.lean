module

public import LeanShared.Analysis.TwoNormNormalization
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Semicontinuity.Defs

/-! # Precise deferred Keller--Liverani 1999 contract

Source: Keller--Liverani, *Stability of the spectrum for transfer operators*,
Ann. Scuola Norm. Sup. Pisa 28 (1999), 141--152, Theorem 1 and Corollary 1:
https://www.numdam.org/item/ASNSP_1999_4_28_1_141_0.pdf

The source uses a no-residual-spectrum premise above the contraction rate.
Relative compactness of the weak inclusion is recorded separately from this
premise; it is not silently substituted for compactness of the image of the
strong closed unit ball. The output records spectral confinement, weak
projector convergence, range coercivity and preservation of rank one. Its
rank-one identities include ordinary Riesz-projector calculus. No noisy
spectral dominance, peripheral exclusion or stochastic conclusion is a
hypothesis or output of the source contract below.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology NNReal

namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Residual spectrum means an injective spectral shift with nondense range.
The primary theorem excludes this above `alpha`. -/
def NoResidualAbove (P : E →L[ℂ] E) (alpha : ℝ) : Prop :=
  ∀ z : ℂ, alpha < ‖z‖ →
    Function.Injective (z • (1 : E →L[ℂ] E) - P) →
      DenseRange (z • (1 : E →L[ℂ] E) - P)

/-- The primary theorem's four hypotheses on a genuine normalized family.
All growth constants and the local parameter window are explicit. -/
structure Hypotheses (P : ℝ≥0 → E →L[ℂ] E) (i : E →L[ℂ] W) where
  window : ℝ≥0
  window_pos : 0 < window
  weak_injective : Function.Injective i
  weak_le_strong : ∀ x, ‖i x‖ ≤ ‖x‖
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1
  weakRate : ℝ
  alpha_lt_weakRate : alpha < weakRate
  weakConstant : ℝ
  weakConstant_pos : 0 < weakConstant
  strongConstant : ℝ
  strongConstant_pos : 0 < strongConstant
  errorConstant : ℝ
  errorConstant_pos : 0 < errorConstant
  weak_growth : ∀ ε ≤ window, ∀ n x,
    ‖i ((P ε ^ n) x)‖ ≤ weakConstant * weakRate ^ n * ‖i x‖
  twoNorm_growth : ∀ ε ≤ window, ∀ n x,
    ‖(P ε ^ n) x‖ ≤ strongConstant * alpha ^ n * ‖x‖ +
      errorConstant * weakRate ^ n * ‖i x‖
  no_residual : ∀ ε ≤ window, NoResidualAbove (P ε) alpha
  modulus : ℝ≥0 → ℝ≥0
  modulus_monotone : Monotone modulus
  modulus_upperSemicontinuous : UpperSemicontinuous modulus
  modulus_pos : ∀ ε : ℝ≥0, 0 < ε → 0 < modulus ε
  modulus_zero : Tendsto modulus (𝓝 0) (𝓝 0)
  perturbation : ∀ ε ≤ window, ‖i.comp (P ε - P 0)‖ ≤ (modulus ε : ℝ)

/-- A separated rank-one deterministic leading projection, prior to noise. -/
structure DeterministicLeading (P : E →L[ℂ] E) where
  rate : ℝ
  rate_pos : 0 < rate
  subordinate : ℝ
  subordinate_nonneg : 0 ≤ subordinate
  subordinate_lt_rate : subordinate < rate
  vector : E
  mean : E →L[ℂ] ℂ
  normalization : mean vector = 1
  right_equation : P vector = (rate : ℂ) • vector
  left_equation : ∀ x, mean (P x) = (rate : ℂ) * mean x
  complementary_radius : spectralRadius ℂ (P - mean.smulRight ((rate : ℂ) • vector)) ≤
    ENNReal.ofReal subordinate
  spectral_separation : ∀ z ∈ spectrum ℂ P, z = (rate : ℂ) ∨ ‖z‖ ≤ subordinate
  leading_simple : ∀ x, P x = (rate : ℂ) • x → ∃ c : ℂ, x = c • vector

/-- Classical perturbative projection outputs, before deducing dominance.
`project_eigenvector` is the usual Riesz projection identity inside its disk.
`remainder_spectrum` is the classical complementary Riesz spectral splitting,
including exclusion of continuous spectrum from that disk.
Projection rank one is expressed by a normalized factorization. -/
structure ProjectorOutputs (P : ℝ≥0 → E →L[ℂ] E) (i : E →L[ℂ] W)
    (d : DeterministicLeading (P 0)) (q δ : ℝ) where
  window : ℝ≥0
  window_pos : 0 < window
  eigenvalue : ℝ≥0 → ℂ
  projection : ℝ≥0 → E →L[ℂ] E
  vector : ℝ≥0 → E
  mean : ℝ≥0 → E →L[ℂ] ℂ
  eigenvalue_near : ∀ ε ≤ window, dist (eigenvalue ε) (d.rate : ℂ) < δ
  rank_one : ∀ ε ≤ window, projection ε = (mean ε).smulRight (vector ε)
  normalization : ∀ ε ≤ window, mean ε (vector ε) = 1
  eigen_action : ∀ ε ≤ window, P ε * projection ε = eigenvalue ε • projection ε
  projection_commutes : ∀ ε ≤ window, P ε * projection ε = projection ε * P ε
  project_eigenvector : ∀ ε ≤ window, ∀ z : ℂ,
    dist z (d.rate : ℂ) ≤ δ → ∀ x, P ε x = z • x → projection ε x = x
  spectral_confinement : ∀ ε ≤ window, ∀ z ∈ spectrum ℂ (P ε),
    ‖z‖ ≤ q ∨ ∃ w ∈ spectrum ℂ (P 0), dist z w ≤ δ
  remainder_spectrum : ∀ ε ≤ window, ∀ z ∈ spectrum ℂ
    (P ε - eigenvalue ε • projection ε),
    z = 0 ∨ (z ∈ spectrum ℂ (P ε) ∧ δ < dist z (d.rate : ℂ))
  projection_zero : projection 0 = d.mean.smulRight d.vector
  eigenvalue_convergence : Tendsto eigenvalue (𝓝 0) (𝓝 (d.rate : ℂ))
  projector_convergence : Tendsto (fun ε => i.comp (projection ε - projection 0)) (𝓝 0) (𝓝 0)
  coercivityConstant : ℝ
  coercivityConstant_nonneg : 0 ≤ coercivityConstant
  range_coercivity : ∀ ε ≤ window, ∀ x,
    ‖projection ε x‖ ≤ coercivityConstant * ‖i (projection ε x)‖

/-- Named, deferred classical theorem: primary spectral confinement and
Corollary 1 projector estimates/rank stability, restricted to a simple
isolated deterministic eigenvalue. All source analytic hypotheses are
arguments. The theorem is supplied as a parameter, never a global axiom. -/
def ClassicalContract [CompleteSpace E] : Prop :=
  ∀ (P : ℝ≥0 → E →L[ℂ] E) (i : E →L[ℂ] W) (h : Hypotheses P i)
    (d : DeterministicLeading (P 0)) (q δ : ℝ),
    h.alpha < q → q < d.rate → q < h.weakRate →
    d.subordinate < q → 0 < δ → δ < q - d.subordinate → δ < d.rate - q →
      Nonempty (ProjectorOutputs P i d q δ)

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
