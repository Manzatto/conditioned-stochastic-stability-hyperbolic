module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedModel
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedRateTransport

/-! Exact intrinsic pressure and growth constants are conclusions of the
concrete model producer. Isometric weak-space transport preserves them. -/

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

structure QuantitativeData (i : S →L[ℂ] H) (j : S →L[ℂ] W)
    (law : ℝ≥0 → Measure Z) (probability : ∀ ε, IsProbabilityMeasure (law ε))
    (generator : ℝ≥0 → Z → S →L[ℂ] S) (scale principal weakRate weakOneStep operatorBound : ℝ) where
  model : Data i j law probability generator scale
  principal_eq : model.inputs.principal = principal
  weakRate_eq : model.inputs.weakRate = weakRate
  weakOneStep_eq : model.inputs.weakOneStep = weakOneStep
  operatorBound_eq : model.inputs.operatorBound = operatorBound

def QuantitativeData.transport
    {i : S →L[ℂ] H} {j : S →L[ℂ] W}
    {law : ℝ≥0 → Measure Z} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {generator : ℝ≥0 → Z → S →L[ℂ] S} {scale principal weakRate weakOneStep operatorBound : ℝ}
    (m : QuantitativeData i j law probability generator scale principal weakRate weakOneStep operatorBound)
    (eH : H ≃ₗᵢ[ℂ] H') (eW : W ≃ₗᵢ[ℂ] W') :
    QuantitativeData (eH.toLinearIsometry.toContinuousLinearMap.comp i)
      (eW.toLinearIsometry.toContinuousLinearMap.comp j) law probability generator
      scale principal weakRate weakOneStep operatorBound where
  model := {
    compactH := m.model.compactH.clm_comp eH.toLinearIsometry.toContinuousLinearMap
    injectiveH := eH.injective.comp m.model.injectiveH
    denseH := eH.surjective.denseRange.comp m.model.denseH eH.continuous
    compactW := m.model.compactW.clm_comp eW.toLinearIsometry.toContinuousLinearMap
    injectiveW := eW.injective.comp m.model.injectiveW
    denseW := eW.surjective.denseRange.comp m.model.denseW eW.continuous
    inputs := m.model.inputs.transportWeak eW
    generator_eq := by
      simpa only [KellerLiverani1999.ActualAnnealedInputs.transportWeak_generator]
        using m.model.generator_eq }
  principal_eq := (m.model.inputs.transportWeak_principal eW).trans m.principal_eq
  weakRate_eq := (m.model.inputs.transportWeak_weakRate eW).trans m.weakRate_eq
  weakOneStep_eq := m.weakOneStep_eq
  operatorBound_eq := m.operatorBound_eq

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedModel
