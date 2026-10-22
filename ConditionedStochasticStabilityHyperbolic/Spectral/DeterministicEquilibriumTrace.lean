module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniMeasureStability

/-! The equilibrium identification used by local weak stability concerns only
the two deterministic leading pairs, independent of noisy KL choices. -/

@[expose] public noncomputable section
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability
open KellerLiverani1999

variable {S H W V : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {Ps : ℝ≥0 → S →L[ℂ] S} {Pm : ℝ≥0 → H →L[ℂ] H}
  {i : S →L[ℂ] H} {j : H →L[ℂ] W} {jm : H →L[ℂ] V}
  {ds : DeterministicLeading (Ps 0)} {dm : DeterministicLeading (Pm 0)}
  {qs δs qm δm : ℝ}

theorem realLeftTrace_zero
    (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm) (φ : W →L[ℂ] ℂ) (f : H) :
    realLeftTrace os om φ 0 f =
      ((φ (j (i ds.vector)))⁻¹ * φ (j (dm.mean f • dm.vector))).re := by
  change ((φ (j (i (os.projection 0 ds.vector))))⁻¹ *
    φ (j (om.projection 0 f))).re = _
  rw [os.projection_zero, om.projection_zero,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply,
    ds.normalization, one_smul]

end ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability
