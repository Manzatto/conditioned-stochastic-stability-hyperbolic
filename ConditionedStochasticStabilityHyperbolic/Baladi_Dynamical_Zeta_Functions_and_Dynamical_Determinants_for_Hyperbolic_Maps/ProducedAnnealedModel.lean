module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL

/-! A constructed analytic model carries its proved inclusion properties.
This generic output record has no physical-norm assumptions or source contracts.
It lets consumers use produced compactness and exact generator identity without
re-exposing the large canonical physical inclusion proof terms. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProducedAnnealedModel

variable {S H W Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [MeasurableSpace Z]

structure Data (i : S →L[ℂ] H) (j : S →L[ℂ] W)
    (law : ℝ≥0 → Measure Z) (probability : ∀ ε, IsProbabilityMeasure (law ε))
    (generator : ℝ≥0 → Z → S →L[ℂ] S) (scale : ℝ) where
  compactH : IsCompactOperator i
  injectiveH : Function.Injective i
  denseH : DenseRange i
  compactW : IsCompactOperator j
  injectiveW : Function.Injective j
  denseW : DenseRange j
  inputs : KellerLiverani1999.ActualAnnealedInputs law probability j scale
  generator_eq : ∀ ε z, inputs.generator ε z = generator ε z

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedModel
