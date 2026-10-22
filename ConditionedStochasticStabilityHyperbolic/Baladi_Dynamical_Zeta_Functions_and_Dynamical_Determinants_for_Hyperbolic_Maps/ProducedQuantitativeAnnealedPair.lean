module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedPair

/-! A pair of produced analytic models carries the exact common weak target
and proved actual-average intertwining required by the local theorem. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
open KellerLiverani1999

variable {S H W Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [MeasurableSpace Z]

structure QuantitativeData (i : S →L[ℂ] H) (j : H →L[ℂ] W)
    (law : ℝ≥0 → Measure Z) (probability : ∀ ε, IsProbabilityMeasure (law ε))
    (genS : ℝ≥0 → Z → S →L[ℂ] S) (genH : ℝ≥0 → Z → H →L[ℂ] H)
    (R principalS principalH weakRateS weakRateH : ℝ) where
  pair : Data i j law probability genS genH R
  principalS_eq : pair.strong.principal = principalS
  principalH_eq : pair.intermediate.principal = principalH
  weakRateS_eq : pair.strong.weakRate = weakRateS
  weakRateH_eq : pair.intermediate.weakRate = weakRateH

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
