module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalSpectralWitness
public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalChainGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.QuasiErgodic

/-! Attach the full spectral witness to the weakly convergent QEM family.
The actual positive leading gap and positivity on its core identify any
supported QEM with the canonical product, without changing the family. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def SpectralWitness.of_core_positive_rankOne
    (C : AbsorbingMarkovChains.CanonicalChain X) (R : ℝ) (hR : 0 < R)
    (sf : HasStrongFellerKernel C)
    (d : RankOneSpectralData (R • strongFellerTransferOperator C sf) (1 : X →ᵇ ℝ))
    (positive : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ (R • strongFellerTransferOperator C sf) f x)
    (core : Set X) (hne : core.Nonempty) (hpos : ∀ x ∈ core, 0 < d.eigenvector x)
    (ν : ProbabilityMeasure X) (hqem : C.IsQuasiErgodic (ν : Measure X))
    (hsupport : core ⊆ (ν : Measure X).support) : SpectralWitness C R ν := by
  let dn : RankOneSpectralData (strongFellerTransferOperator C sf) (1 : X →ᵇ ℝ) :=
    d.ofRawNormalization R hR (by rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul])
  let μ := d.eigenmeasure positive
  have hmean (f : X →ᵇ ℝ) : dn.mean f = ∫ x, f x ∂μ := by
    change (d.ofRawNormalization R hR _).mean f = _
    rw [RankOneSpectralData.ofRawNormalization_mean]
    exact d.eigenmeasure_represents positive f
  have hvector : dn.eigenvector = d.eigenvector := d.ofRawNormalization_eigenvector _ _ _
  have hproduct : (ν : Measure X) = eigenvectorMeasure μ d.eigenvector := by
    rw [← hvector]
    exact QuasiErgodic.eq_eigenvectorMeasure_of_basicSet_support C _
      (strongFellerTransferOperator_represents C sf) dn μ hmean
      (fun x => by rw [hvector]; exact d.eigenvector_nonneg_of_positive positive x)
      core hne (fun x hx => by rw [hvector]; exact hpos x hx) _ hqem hsupport
  exact SpectralWitness.of_rankOne C R sf d positive ν hproduct

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
