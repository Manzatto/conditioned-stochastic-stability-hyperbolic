module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedLayerKernel
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConditionedAverages

/-!
# Leading data under exact nested actual-kernel coordinates

The constructed isometric subtype flattening transports the actual rank-one
gap, rate, right vector and left measure to a prefix's dominant diagonal.
All gap constants are preserved. No new spectral comparison or local gap
assumption is introduced by this state-space identification.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NestedLeadingData
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (U V : Set X) (hUV : U ⊆ V)
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (hU : MeasurableSet U) (hV : MeasurableSet V)

local notation "Q" => transferOperator (𝕜 := ℝ)
  (chain (chain C V hV) (innerLevel U V) (hU.preimage measurable_subtype_coe))
  (strongFeller (chain C V hV) (strongFeller C hSF V hV) (innerLevel U V) (hU.preimage measurable_subtype_coe))
local notation "P" => transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU)

/-- Exact actual nested-kernel leading data with the original normalized
rate, mean, vector and geometric gap constants. -/
def nestedData (d : RankOneSpectralData P (1 : U →ᵇ ℝ)) :
    RankOneSpectralData Q (1 : innerLevel U V →ᵇ ℝ) where
  rate := d.rate
  rate_pos := d.rate_pos
  mean := d.mean.comp (pullbackInv U V hUV)
  eigenvector := pullback U V hUV d.eigenvector
  mean_eigenvector := by
    change d.mean (pullbackInv U V hUV (pullback U V hUV d.eigenvector)) = 1
    rw [pullback_inv_apply]
    exact d.mean_eigenvector
  mean_one_pos := by
    change 0 < d.mean (pullbackInv U V hUV (1 : innerLevel U V →ᵇ ℝ))
    have h1 : pullbackInv U V hUV (1 : innerLevel U V →ᵇ ℝ) = 1 := by ext x; rfl
    rw [h1]
    exact d.mean_one_pos
  right_eigenvector := by
    rw [transfer_nested_pullback U V hUV C hSF hU hV, d.right_eigenvector, map_smul]
  errorConstant := d.errorConstant
  errorConstant_nonneg := d.errorConstant_nonneg
  decay := d.decay
  decay_nonneg := d.decay_nonneg
  decay_lt_one := d.decay_lt_one
  power_gap := by
    intro n
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg d.errorConstant_nonneg (pow_nonneg d.decay_nonneg n))
    intro f
    have he := powers_nested_pullback U V hUV C hSF hU hV d.rate⁻¹ n (pullbackInv U V hUV f)
    rw [pullback_apply_inv] at he
    have ha : ((d.rate⁻¹ • Q) ^ n -
        (d.mean.comp (pullbackInv U V hUV)).smulRight (pullback U V hUV d.eigenvector)) f =
        pullback U V hUV (((d.rate⁻¹ • P) ^ n - d.mean.smulRight d.eigenvector)
          (pullbackInv U V hUV f)) := by
      change ((d.rate⁻¹ • Q) ^ n) f - d.mean (pullbackInv U V hUV f) •
        pullback U V hUV d.eigenvector = _
      rw [he, ← map_smul, ← map_sub]
      rfl
    rw [ha, pullback_norm]
    calc
      _ ≤ ‖(d.rate⁻¹ • P) ^ n - d.mean.smulRight d.eigenvector‖ *
          ‖pullbackInv U V hUV f‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (d.errorConstant * d.decay ^ n) * ‖f‖ := by
        rw [pullbackInv_norm]
        exact mul_le_mul_of_nonneg_right (d.power_gap n) (norm_nonneg f)

@[simp] theorem nestedData_rate (d : RankOneSpectralData P (1 : U →ᵇ ℝ)) :
    (nestedData U V hUV C hSF hU hV d).rate = d.rate := rfl

@[simp] theorem nestedData_vector (d : RankOneSpectralData P (1 : U →ᵇ ℝ))
    (x : innerLevel U V) :
    (nestedData U V hUV C hSF hU hV d).eigenvector x = d.eigenvector (flatten U V hUV x) := rfl

/-- The direct stratum representing measure transports under the actual
flattening inverse, without a new Riesz or spectral assumption. -/
theorem nestedData_represents
    (d : RankOneSpectralData P (1 : U →ᵇ ℝ)) (μ : Measure U)
    (hmean : ∀ f : U →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) (f : innerLevel U V →ᵇ ℝ) :
    (nestedData U V hUV C hSF hU hV d).mean f =
      ∫ y, f y ∂μ.map (flatten U V hUV).symm := by
  change d.mean (pullbackInv U V hUV f) = _
  rw [hmean, (flatten U V hUV).symm.measurableEmbedding.integral_map]
  rfl

end ConditionedStochasticStabilityHyperbolic.Global.NestedLeadingData
