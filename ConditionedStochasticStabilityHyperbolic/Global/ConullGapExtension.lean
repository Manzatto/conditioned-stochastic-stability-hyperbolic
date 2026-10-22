module

public import ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryLayer
public import ConditionedStochasticStabilityHyperbolic.Global.LayerNormalizedGap
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! A gap already derived on the live part extends to its compact prefix.
The actual smoothing/restriction factors construct the ambient gap, and
its Riesz product is exactly the pushed live probability. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ConullGapExtension
open LeanShared ComplexStrongFeller LayerOperators LayerRankOne LayerQuasiErgodic
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (sf : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U) (hz : ∀ x, C.killedTransition x Uᶜ = 0)
local notation "CL" => RestrictedLayerChain.chain C U hU
local notation "sL" => RestrictedLayerChain.strongFeller C sf U hU
local notation "S" => extensionOperator (𝕜 := ℝ) C sf U hU
local notation "R" => restrictOperator (𝕜 := ℝ) U

include hz in
/-- The reverse actual factorization extends the live gap, with constant
one normalization restored by positivity of the integral transfer. -/
def data (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CL sL) (1 : U →ᵇ ℝ)) :
    RankOneSpectralData (transferOperator (𝕜 := ℝ) C sf) (1 : X →ᵇ ℝ) := by
  have hp := NullBoundaryLayer.transfer_eq_extension_restriction (𝕜 := ℝ) C sf U hU hz
  have hb : transferOperator (𝕜 := ℝ) CL sL = (R).comp S :=
    RestrictedLayerChain.transferOperator_eq_lower C sf U hU
  let d0 := liftedData S R hp hb d
  apply withConstantOne d0 (actual_transfer_positive C sf)
  intro x
  change 0 ≤ extensionOperator (𝕜 := ℝ) C sf U hU 1 x
  rw [extensionOperator_apply]
  apply integral_nonneg
  intro y
  by_cases hy : y ∈ U
  · rw [zeroExtend_coe U (1 : U →ᵇ ℝ) ⟨y, hy⟩]
    exact zero_le_one
  · rw [zeroExtend_of_not_mem U (1 : U →ᵇ ℝ) y hy]
    change (0 : ℝ) ≤ 0
    exact le_rfl

@[simp] theorem data_mean
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CL sL) (1 : U →ᵇ ℝ))
    (f : X →ᵇ ℝ) : (data C sf U hU hz d).mean f = d.mean (R f) := rfl

@[simp] theorem data_rate
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CL sL) (1 : U →ᵇ ℝ)) :
    (data C sf U hU hz d).rate = d.rate := rfl

 theorem data_vector_on_live
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CL sL) (1 : U →ᵇ ℝ)) (x : U) :
    (data C sf U hU hz d).eigenvector x.val = d.eigenvector x := by
  change d.rate⁻¹ * (extensionOperator (𝕜 := ℝ) C sf U hU d.eigenvector x.val) = _
  have he : extensionOperator (𝕜 := ℝ) C sf U hU d.eigenvector x.val =
      d.rate * d.eigenvector x := by
    rw [← RestrictedLayerChain.integral_chain C sf U hU d.eigenvector x]
    have hd := congrArg (fun f : U →ᵇ ℝ => f x) d.right_eigenvector
    simpa only [transferOperator_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul] using hd
  rw [he, ← mul_assoc, inv_mul_cancel₀ d.rate_pos.ne', one_mul]

variable [CompactSpace X] [CompactSpace U]

 theorem leadingMeasure_eq_map
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CL sL) (1 : U →ᵇ ℝ)) :
    leadingMeasure C sf (data C sf U hU hz d) = (leadingMeasure CL sL d).map Subtype.val := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable measurable_subtype_coe f.continuous.measurable.stronglyMeasurable]
  change (∫ x, f x ∂(data C sf U hU hz d).eigenmeasure (actual_transfer_positive C sf)) = _
  rw [← (data C sf U hU hz d).eigenmeasure_represents (actual_transfer_positive C sf)]
  change d.mean (R f) = ∫ x, (R f) x ∂leadingMeasure CL sL d
  exact d.eigenmeasure_represents (actual_transfer_positive CL sL) _

/-- The product used by all-prefix conclusions is exactly the live product pushed through the
literal inclusion. -/
theorem productMeasure_eq_map
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) CL sL) (1 : U →ᵇ ℝ)) :
    productMeasure C sf (data C sf U hU hz d) = (productMeasure CL sL d).map Subtype.val := by
  let : IsProbabilityMeasure (productMeasure C sf (data C sf U hU hz d)) :=
    (productMeasure_isQuasiErgodic C sf (data C sf U hU hz d)).1
  let : IsProbabilityMeasure (productMeasure CL sL d) := (productMeasure_isQuasiErgodic CL sL d).1
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable measurable_subtype_coe f.continuous.measurable.stronglyMeasurable]
  change (∫ x, f x ∂eigenvectorMeasure (leadingMeasure C sf (data C sf U hU hz d))
    (data C sf U hU hz d).eigenvector) =
    ∫ x, f x.val ∂eigenvectorMeasure (leadingMeasure CL sL d) d.eigenvector
  rw [integral_eigenvectorMeasure _ _ (data C sf U hU hz d).eigenvector.continuous.measurable
      ((data C sf U hU hz d).eigenvector_nonneg_of_positive (actual_transfer_positive C sf)),
    integral_eigenvectorMeasure _ _ d.eigenvector.continuous.measurable
      (d.eigenvector_nonneg_of_positive (actual_transfer_positive CL sL)), leadingMeasure_eq_map]
  rw [integral_map_of_stronglyMeasurable (f := fun x => f x * (data C sf U hU hz d).eigenvector x)
    measurable_subtype_coe (f.continuous.mul (data C sf U hU hz d).eigenvector.continuous).measurable.stronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change f x.val * (data C sf U hU hz d).eigenvector x.val = f x.val * d.eigenvector x
    rw [data_vector_on_live]

end ConditionedStochasticStabilityHyperbolic.Global.ConullGapExtension
