module

public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicEquilibriumTrace

/-! The deterministic equilibrium identification is needed on the intermediate
leading pair only. Intertwining and simplicity derive the cross-space quotient
used by noisy projector stability; it is not a further thermodynamic input. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability
open KellerLiverani1999
variable {S H : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  {Ps : S →L[ℂ] S} {Ph : H →L[ℂ] H}

 theorem deterministic_multiplier_ratio
    (ds : DeterministicLeading Ps) (dh : DeterministicLeading Ph)
    (i : S →L[ℂ] H) (hi : Function.Injective i)
    (commutes : i.comp Ps = Ph.comp i) (rate : ds.rate = dh.rate)
    (M : H →L[ℂ] H) :
    dh.mean (M (i ds.vector)) / dh.mean (i ds.vector) = dh.mean (M dh.vector) := by
  have hright := congrArg (fun Q : S →L[ℂ] H => Q ds.vector) commutes
  simp only [ContinuousLinearMap.comp_apply] at hright
  rw [ds.right_equation, map_smul, rate] at hright
  obtain ⟨c, hc⟩ := dh.leading_simple (i ds.vector) hright.symm
  have hv : ds.vector ≠ 0 := by
    intro hz
    have hn := ds.normalization
    rw [hz, map_zero] at hn
    exact zero_ne_one hn
  have hc0 : c ≠ 0 := by
    intro hz
    have hzv : i ds.vector = 0 := by rw [hc, hz, zero_smul]
    exact hv (hi (hzv.trans (map_zero i).symm))
  rw [hc, map_smul, map_smul, map_smul, dh.normalization]
  simp only [smul_eq_mul, mul_one]
  exact mul_div_cancel_left₀ _ hc0

end ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability
