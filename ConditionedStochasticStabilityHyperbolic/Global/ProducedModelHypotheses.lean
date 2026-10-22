module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedModel

/-! # Primary KL hypotheses from the actual produced model

The compact inclusion, finite-block bounds, weak power bounds, perturbation
modulus and residual condition are produced internally. This bridge is used
for subordinate global layers, where no rank-one or mixing hypothesis is valid.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.Global.ProducedModelHypotheses
open KellerLiverani1999 LeanShared.TwoNormNormalization
variable {E H W Ξ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [MeasurableSpace Ξ]

theorem exists_actual_hypotheses
    (iH : E →L[ℂ] H) (iW : E →L[ℂ] W)
    (law : NNReal → Measure Ξ) (prob : ∀ ε, IsProbabilityMeasure (law ε))
    (generator : NNReal → Ξ → E →L[ℂ] E) (scale : ℝ)
    (m : ProducedAnnealedModel.Data iH iW law prob generator scale)
    (essential : EssentialRadiusContract (E := E) (W := W)) :
    ∃ h : Hypotheses m.inputs.operator (weakEmbedding iW),
      h.alpha = m.inputs.principal / scale ∧ h.weakRate = m.inputs.weakRate / scale := by
  obtain ⟨h, hα, hweak, _⟩ := exists_hypotheses_of_varying_noise_classical_radius
    essential law prob m.inputs.generator m.inputs.measurable iW m.injectiveW m.compactW
    m.inputs.window m.inputs.window_pos m.inputs.blockLength m.inputs.blockLength_pos
    m.inputs.principal m.inputs.weakRate m.inputs.weakOneStep m.inputs.operatorBound m.inputs.remainder scale
    m.inputs.principal_pos m.inputs.principal_weak m.inputs.weakOneStep_nonneg m.inputs.weakOneStep_rate
    m.inputs.operatorBound_nonneg m.inputs.remainder_nonneg m.inputs.scale_ge_one m.inputs.principal_scale
    m.inputs.generator_bound m.inputs.weak_bound m.inputs.block_bound m.inputs.perturbation
  exact ⟨h, hα, hweak⟩

end ConditionedStochasticStabilityHyperbolic.Global.ProducedModelHypotheses
