module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingSimplicity

/-! # Choice independence of the produced normalized spectral pair

The actual operator determines its positive leading rate. The normalized power
limit determines its rank-one projector; left mass one then determines both
right and left vectors. Independent local and weak-stability constructions can
therefore use the same canonical pair without a new matching assumption.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {P : E →L[ℝ] E} {one : E}

/-- Canonical pair choices for the same actual operator agree. -/
theorem canonical_pair_eq
    (d e : RankOneSpectralData P one) (hd : d.mean one = 1) (he : e.mean one = 1) :
    d.rate = e.rate ∧ d.eigenvector = e.eigenvector ∧ d.mean = e.mean := by
  have hr : d.rate = e.rate := by
    have h := d.spectralRadius_eq_rate.symm.trans e.spectralRadius_eq_rate
    have ht := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_ofReal d.rate_pos.le,
      ENNReal.toReal_ofReal e.rate_pos.le] using ht
  have hnorm : d.normalizedOperator = e.normalizedOperator := by
    simp only [normalizedOperator, hr]
  have hp : d.projection = e.projection := by
    apply tendsto_nhds_unique d.tendsto_powers
    simpa only [hnorm] using e.tendsto_powers
  have hg : d.eigenvector = e.eigenvector := by
    have h := congrArg (fun A : E →L[ℝ] E => A one) hp
    simpa only [projection, ContinuousLinearMap.smulRight_apply, hd, he, one_smul] using h
  refine ⟨hr, hg, ?_⟩
  ext x
  have h := congrArg (fun A : E →L[ℝ] E => A x) hp
  simp only [projection, ContinuousLinearMap.smulRight_apply, hg] at h
  exact (smul_left_injective ℝ e.eigenvector_ne_zero) h

end ConditionedStochasticStabilityHyperbolic.RankOneSpectralData
