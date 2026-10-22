module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedModel
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedCompatibility
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedEmbeddingEquality
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedWeakTransport

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

structure Data (i : S →L[ℂ] H) (j : H →L[ℂ] W)
    (law : ℝ≥0 → Measure Z) (probability : ∀ ε, IsProbabilityMeasure (law ε))
    (genS : ℝ≥0 → Z → S →L[ℂ] S) (genH : ℝ≥0 → Z → H →L[ℂ] H) (R : ℝ) where
  compactS : IsCompactOperator i
  injectiveS : Function.Injective i
  denseS : DenseRange i
  compactH : IsCompactOperator j
  injectiveH : Function.Injective j
  strong : ActualAnnealedInputs law probability (j.comp i) R
  intermediate : ActualAnnealedInputs law probability j R
  strong_generator : ∀ ε z, strong.generator ε z = genS ε z
  intermediate_generator : ∀ ε z, intermediate.generator ε z = genH ε z
  compatible : ∀ ε, i.comp (strong.operator ε) = (intermediate.operator ε).comp i

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
