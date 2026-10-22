module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedLeadingData

/-!
# Inverse flattening of actual nested leading data

Closed-layer conull-stratum data live on a nested subtype. The inverse of the
proved actual-kernel coordinates transports them to the direct ambient
stratum, preserving rate, vector, mean and every gap constant.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NestedDirectLeadingData
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (U V : Set X) (hUV : U ⊆ V)
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (hU : MeasurableSet U) (hV : MeasurableSet V)
local notation "Q" => transferOperator (𝕜 := ℝ)
  (chain (chain C V hV) (innerLevel U V) (hU.preimage measurable_subtype_coe))
  (strongFeller (chain C V hV) (strongFeller C hSF V hV) (innerLevel U V) (hU.preimage measurable_subtype_coe))
local notation "P" => transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU)

/-- Direct actual-stratum spectral data obtained from the nested data,
with no new gap hypothesis or weakening of geometric constants. -/
def directData (d : RankOneSpectralData Q (1 : innerLevel U V →ᵇ ℝ)) :
    RankOneSpectralData P (1 : U →ᵇ ℝ) where
  rate := d.rate
  rate_pos := d.rate_pos
  mean := d.mean.comp (pullback U V hUV)
  eigenvector := pullbackInv U V hUV d.eigenvector
  mean_eigenvector := by
    change d.mean (pullback U V hUV (pullbackInv U V hUV d.eigenvector)) = 1
    rw [pullback_apply_inv]
    exact d.mean_eigenvector
  mean_one_pos := by
    change 0 < d.mean (pullback U V hUV (1 : U →ᵇ ℝ))
    have h1 : pullback U V hUV (1 : U →ᵇ ℝ) = 1 := by ext x; rfl
    rw [h1]
    exact d.mean_one_pos
  right_eigenvector := by
    have he := transfer_nested_pullback U V hUV C hSF hU hV (pullbackInv U V hUV d.eigenvector)
    rw [pullback_apply_inv, d.right_eigenvector] at he
    have hh := congrArg (pullbackInv U V hUV) he
    rw [map_smul, pullback_inv_apply] at hh
    exact hh.symm
  errorConstant := d.errorConstant
  errorConstant_nonneg := d.errorConstant_nonneg
  decay := d.decay
  decay_nonneg := d.decay_nonneg
  decay_lt_one := d.decay_lt_one
  power_gap := by
    intro n
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg d.errorConstant_nonneg (pow_nonneg d.decay_nonneg n))
    intro f
    have he := powers_nested_pullback U V hUV C hSF hU hV d.rate⁻¹ n f
    have hh := congrArg (pullbackInv U V hUV) he
    rw [pullback_inv_apply] at hh
    have ha : ((d.rate⁻¹ • P) ^ n -
        (d.mean.comp (pullback U V hUV)).smulRight (pullbackInv U V hUV d.eigenvector)) f =
        pullbackInv U V hUV (((d.rate⁻¹ • Q) ^ n - d.mean.smulRight d.eigenvector)
          (pullback U V hUV f)) := by
      change ((d.rate⁻¹ • P) ^ n) f - d.mean (pullback U V hUV f) •
        pullbackInv U V hUV d.eigenvector = _
      rw [← hh, ← map_smul, ← map_sub]
      rfl
    rw [ha, pullbackInv_norm]
    calc
      _ ≤ ‖(d.rate⁻¹ • Q) ^ n - d.mean.smulRight d.eigenvector‖ *
          ‖pullback U V hUV f‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (d.errorConstant * d.decay ^ n) * ‖f‖ := by
        rw [pullback_norm]
        exact mul_le_mul_of_nonneg_right (d.power_gap n) (norm_nonneg f)

@[simp] theorem directData_rate (d : RankOneSpectralData Q (1 : innerLevel U V →ᵇ ℝ)) :
    (directData U V hUV C hSF hU hV d).rate = d.rate := rfl

@[simp] theorem directData_vector (d : RankOneSpectralData Q (1 : innerLevel U V →ᵇ ℝ)) (x : U) :
    (directData U V hUV C hSF hU hV d).eigenvector x =
      d.eigenvector ((flatten U V hUV).symm x) := rfl

/-- Actual representing measure in direct ambient-stratum coordinates. -/
theorem directData_represents
    (d : RankOneSpectralData Q (1 : innerLevel U V →ᵇ ℝ)) (μ : Measure (innerLevel U V))
    (hmean : ∀ f : innerLevel U V →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) (f : U →ᵇ ℝ) :
    (directData U V hUV C hSF hU hV d).mean f = ∫ y, f y ∂μ.map (flatten U V hUV) := by
  change d.mean (pullback U V hUV f) = _
  rw [hmean, (flatten U V hUV).measurableEmbedding.integral_map]
  rfl

end ConditionedStochasticStabilityHyperbolic.Global.NestedDirectLeadingData
