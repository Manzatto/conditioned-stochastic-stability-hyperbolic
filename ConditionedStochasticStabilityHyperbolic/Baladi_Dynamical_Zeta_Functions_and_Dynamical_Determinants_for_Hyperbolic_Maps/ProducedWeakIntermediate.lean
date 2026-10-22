module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedModel

/-! Prefix gap construction needs one compact inclusion, whereas local weak
stability uses two genuinely different weaker norms. Reuse the already
constructed weak inclusion in both prefix slots without changing any operator,
noise law or norm. This is a derived model operation, not a classical source. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProducedAnnealedModel
variable {S H W Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [MeasurableSpace Z]
  {i : S →L[ℂ] H} {j : S →L[ℂ] W}
  {law : ℝ≥0 → Measure Z} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
  {generator : ℝ≥0 → Z → S →L[ℂ] S} {scale : ℝ}

@[expose] def Data.weakIntermediate (m : Data i j law probability generator scale) :
    Data j j law probability generator scale where
  compactH := m.compactW
  injectiveH := m.injectiveW
  denseH := m.denseW
  compactW := m.compactW
  injectiveW := m.injectiveW
  denseW := m.denseW
  inputs := m.inputs
  generator_eq := m.generator_eq

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedModel
