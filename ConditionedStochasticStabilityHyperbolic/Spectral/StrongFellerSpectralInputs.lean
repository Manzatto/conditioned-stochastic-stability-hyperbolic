module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniStrongFellerGap

/-! # Explicit KL and physical source inputs for the produced continuous gap

Every field concerns the two-norm analytic source, actual strong-Feller kernel,
classical cross-space correspondence or geometric restriction. Actual physical
spectral pairs, their normalization and the raw gap are constructed outputs.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W Z Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

structure StrongFellerSpectralInputs (C : AbsorbingMarkovChains.CanonicalChain Y)
    (hSF : HasStrongFellerKernel C) (R : ℝ) where
  rawScale_pos : 0 < R
  analytic : ℝ≥0 → E →L[ℂ] E
  weak : E →L[ℂ] W
  deterministic : DeterministicLeading (analytic 0)
  cutoff : ℝ
  contour : ℝ
  outputs : ProjectorOutputs analytic weak deterministic cutoff contour
  contour_subordinate : contour < cutoff - deterministic.subordinate
  contour_leading : contour < deterministic.rate - cutoff
  cutoff_pos : 0 < cutoff
  noiseParameter : ℝ≥0
  parameter_small : noiseParameter ≤ outputs.window
  conjugation : RealOperatorConjugation (analytic noiseParameter)
  analyticScale : ℝ
  analyticScale_pos : 0 < analyticScale
  ultraFeller : StrongFellerSquareCompact.UltraFellerContract (X := Y)
  squareFredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ)
  analyticAmbient : E →L[ℂ] Z
  physicalAmbient : (Y →ᵇ ℂ) →L[ℂ] Z
  compactRiesz : PowerCompactRealLeadingPair.ClassicalContract (X := Y)
  ordinaryComparison : ComparedSpectralGap.EigenvectorComparison
    ((analyticScale : ℂ) • analytic noiseParameter)
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
    analyticAmbient physicalAmbient (analyticScale * cutoff)
  generalizedComparison : GeneralizedSpectralComparison.Comparison
    ((analyticScale : ℂ) • analytic noiseParameter)
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
    analyticAmbient physicalAmbient
    ((analyticScale * (outputs.eigenvalue noiseParameter).re : ℝ) : ℂ)
  generalizedSeparator : GeneralizedSpectralComparison.Separates
    ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) physicalAmbient
    ((analyticScale * (outputs.eigenvalue noiseParameter).re : ℝ) : ℂ)
  physicalLift : Y →ᵇ ℂ
  physicalLift_ne : physicalLift ≠ 0
  physicalLift_match : physicalAmbient physicalLift = analyticAmbient (outputs.vector noiseParameter)
  physicalLift_eigen : ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) physicalLift =
    ((analyticScale * (outputs.eigenvalue noiseParameter).re : ℝ) : ℂ) • physicalLift

/-- The physical real normalized gap is an output of the source packet. -/
theorem StrongFellerSpectralInputs.exists_gap
    {C : AbsorbingMarkovChains.CanonicalChain Y} {hSF : HasStrongFellerKernel C} {R : ℝ}
    (I : StrongFellerSpectralInputs (E := E) (W := W) (Z := Z) C hSF R) :
    ∃ d : RankOneSpectralData (R • strongFellerTransferOperator C hSF) (1 : Y →ᵇ ℝ),
      d.rate = I.analyticScale * (I.outputs.eigenvalue I.noiseParameter).re ∧ d.mean 1 = 1 := by
  exact I.outputs.exists_canonicalRawGap_of_strongFeller_and_generalized_lifting
    I.contour_subordinate I.contour_leading I.cutoff_pos I.noiseParameter I.parameter_small
    I.conjugation I.analyticScale I.analyticScale_pos C hSF R I.rawScale_pos
    I.analyticAmbient I.physicalAmbient I.ultraFeller I.squareFredholm I.ordinaryComparison
    I.compactRiesz I.generalizedComparison
    I.generalizedSeparator I.physicalLift I.physicalLift_ne I.physicalLift_match I.physicalLift_eigen

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
