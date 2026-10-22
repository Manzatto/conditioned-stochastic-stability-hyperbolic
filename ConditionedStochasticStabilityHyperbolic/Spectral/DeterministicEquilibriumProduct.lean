module

public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicEquilibriumTrace

/-! The local weak-limit identification reduces to the classical deterministic
product functional, independently of the auxiliary distribution test used to
orient the noisy projector. -/

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

/-- The normalization denominator is intrinsic to the deterministic pair.
No noisy choice or auxiliary ambient test occurs in the resulting formula. -/
theorem realLeftTrace_zero_eq_normalized_product
    (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm)
    (hagree0 : (om.projection 0).comp i = i.comp (os.projection 0))
    (φ : W →L[ℂ] ℂ) (hφ : φ (j (i ds.vector)) ≠ 0) (f : H) :
    realLeftTrace os om φ 0 f =
      (dm.mean f / dm.mean (i ds.vector)).re := by
  have hg : dm.mean (i ds.vector) • dm.vector = i ds.vector := by
    have hh := congrArg (fun L : S →L[ℂ] H => L ds.vector) hagree0
    simpa only [ContinuousLinearMap.comp_apply, os.projection_zero, om.projection_zero,
      ContinuousLinearMap.smulRight_apply, ds.normalization, one_smul, map_smul] using hh
  have hscalar : φ (j (i ds.vector)) = dm.mean (i ds.vector) * φ (j dm.vector) := by
    simpa only [map_smul, smul_eq_mul] using
      (congrArg (fun v : H => φ (j v)) hg).symm
  have hs : dm.mean (i ds.vector) ≠ 0 := by
    intro hs
    apply hφ
    rw [hscalar, hs, zero_mul]
  have ht : φ (j dm.vector) ≠ 0 := by
    intro ht
    apply hφ
    rw [hscalar, ht, mul_zero]
  rw [realLeftTrace_zero, map_smul, map_smul, smul_eq_mul, hscalar]
  congr 1
  field_simp

end ConditionedStochasticStabilityHyperbolic.KellerLiveraniMeasureStability
