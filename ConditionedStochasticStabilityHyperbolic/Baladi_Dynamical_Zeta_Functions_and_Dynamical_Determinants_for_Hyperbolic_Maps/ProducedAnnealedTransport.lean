module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedModel
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedWeakTransport

/-! A produced physical model transports to isometric, fresh physical weak
completions, retaining all proved compactness and perturbation conclusions. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProducedAnnealedModel

variable {S H W H' W' Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup H'] [NormedSpace ℂ H']
  [NormedAddCommGroup W'] [NormedSpace ℂ W'] [CompleteSpace W']
  [MeasurableSpace Z]

def Data.transport
    {i : S →L[ℂ] H} {j : S →L[ℂ] W}
    {law : ℝ≥0 → Measure Z} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {generator : ℝ≥0 → Z → S →L[ℂ] S} {scale : ℝ}
    (m : Data i j law probability generator scale)
    (eH : H ≃ₗᵢ[ℂ] H') (eW : W ≃ₗᵢ[ℂ] W') :
    Data (eH.toLinearIsometry.toContinuousLinearMap.comp i)
      (eW.toLinearIsometry.toContinuousLinearMap.comp j)
      law probability generator scale where
  compactH := m.compactH.clm_comp eH.toLinearIsometry.toContinuousLinearMap
  injectiveH := eH.injective.comp m.injectiveH
  denseH := eH.surjective.denseRange.comp m.denseH eH.continuous
  compactW := m.compactW.clm_comp eW.toLinearIsometry.toContinuousLinearMap
  injectiveW := eW.injective.comp m.injectiveW
  denseW := eW.surjective.denseRange.comp m.denseW eW.continuous
  inputs := m.inputs.transportWeak eW
  generator_eq := by
    simpa only [KellerLiverani1999.ActualAnnealedInputs.transportWeak_generator] using m.generator_eq

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedModel
