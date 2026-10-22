module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingSimplicity

/-! Constant survival determines the leading rate and provides a canonical
constant eigenvector. This applies to the unabsorbed auxiliary factor even
when its actual killed kernel is probability-normalized by a scalar. -/

@[expose] public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one)

/-- The positive leading functional identifies a constant-survival rate
without a separate spectral-radius argument. -/
theorem rate_eq_of_constant_survival (c : ℝ) (hone : P one = c • one) : d.rate = c := by
  have h := d.left_eigenfunctional one
  rw [hone, map_smul, smul_eq_mul] at h
  nlinarith [d.mean_one_pos]

/-- Constant survival makes the original normalized leading vector a
positive scalar multiple of the constant observable. -/
theorem eigenvector_eq_inv_mean_one (c : ℝ) (hone : P one = c • one) :
    d.eigenvector = (d.mean one)⁻¹ • one := by
  have h := d.leading_eigenvector_eq one (by rw [hone, d.rate_eq_of_constant_survival c hone])
  calc
    d.eigenvector = (d.mean one)⁻¹ • (d.mean one • d.eigenvector) := by
      rw [smul_smul, inv_mul_cancel₀ d.mean_one_pos.ne', one_smul]
    _ = (d.mean one)⁻¹ • one := congrArg ((d.mean one)⁻¹ • ·) h.symm

/-- Reorienting the pair to the constant vector preserves the actual gap,
its leading rate and its geometric constants. -/
def normalizeOne (c : ℝ) (hone : P one = c • one) : RankOneSpectralData P one where
  rate := d.rate
  rate_pos := d.rate_pos
  mean := (d.mean one)⁻¹ • d.mean
  eigenvector := one
  mean_eigenvector := by
    change (d.mean one)⁻¹ * d.mean one = 1
    exact inv_mul_cancel₀ d.mean_one_pos.ne'
  mean_one_pos := by
    change 0 < (d.mean one)⁻¹ * d.mean one
    rw [inv_mul_cancel₀ d.mean_one_pos.ne']
    exact zero_lt_one
  right_eigenvector := by rw [hone, d.rate_eq_of_constant_survival c hone]
  errorConstant := d.errorConstant
  errorConstant_nonneg := d.errorConstant_nonneg
  decay := d.decay
  decay_nonneg := d.decay_nonneg
  decay_lt_one := d.decay_lt_one
  power_gap := by
    intro n
    have hproj : ((d.mean one)⁻¹ • d.mean).smulRight one = d.mean.smulRight d.eigenvector := by
      rw [d.eigenvector_eq_inv_mean_one c hone]
      ext x
      simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, smul_smul]
      rw [mul_comm]
    rw [hproj]
    exact d.power_gap n

@[simp] theorem normalizeOne_eigenvector (c : ℝ) (hone : P one = c • one) :
    (d.normalizeOne c hone).eigenvector = one := rfl

@[simp] theorem normalizeOne_rate (c : ℝ) (hone : P one = c • one) :
    (d.normalizeOne c hone).rate = c := d.rate_eq_of_constant_survival c hone

@[simp] theorem normalizeOne_mean_one (c : ℝ) (hone : P one = c • one) :
    (d.normalizeOne c hone).mean one = 1 := (d.normalizeOne c hone).mean_eigenvector

end ConditionedStochasticStabilityHyperbolic.RankOneSpectralData
