module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Spectral.WeightedKernel

/-! Different strata may choose different positive normalizing bounds. Their
raw transfer is independent of that choice; strong Feller regularity also
transports by the exact scalar identity. Thus heterogeneous layer factories
need not rebuild all analytic models at one artificially common scale. -/

public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.RawNormalizationIndependence
open LeanShared.WeightedConditioning ComplexStrongFeller
variable {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]

theorem integral_normalized (K : Kernel X X) (w : X → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (f : X → 𝕜) (x : X) :
    (∫ y, f y ∂normalizedKernel K w R hw x) =
      R⁻¹ • ∫ y, f y ∂realWeightedKernel K w hw x := by
  rw [normalizedKernel_apply_eq K w R hw hR, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hR.le)]

theorem strongFeller (K : Kernel X X) (w : X → ℝ) (hw : Measurable w)
    (mass : ∀ x, K x univ ≤ 1) [TopologicalSpace X]
    (R S : ℝ) (hR : 0 < R) (hS : 0 < S)
    (hwR : ∀ x, w x ≤ R) (hwS : ∀ x, w x ≤ S)
    (sf : HasStrongFellerKernel (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass)) :
    HasStrongFellerKernel (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass) := by
  intro f hf hb
  have cont := (sf f hf hb).const_smul (S⁻¹ * R)
  convert cont using 1
  funext x
  change (∫ y, f y ∂(WeightedKernel.ofBoundedWeight K w S hw hS hwS mass).killedTransition x) =
    (S⁻¹ * R) • ∫ y, f y ∂(WeightedKernel.ofBoundedWeight K w R hw hR hwR mass).killedTransition x
  rw [WeightedKernel.ofBoundedWeight_killedTransition,
    WeightedKernel.ofBoundedWeight_killedTransition,
    integral_normalized K w hw S hS, integral_normalized K w hw R hR]
  rw [smul_smul]
  congr 1
  rw [mul_assoc, mul_inv_cancel₀ hR.ne', mul_one]

theorem raw_transfer_eq (K : Kernel X X) (w : X → ℝ) (hw : Measurable w)
    (mass : ∀ x, K x univ ≤ 1) [TopologicalSpace X] [OpensMeasurableSpace X]
    (R S : ℝ) (hR : 0 < R) (hS : 0 < S)
    (hwR : ∀ x, w x ≤ R) (hwS : ∀ x, w x ≤ S)
    (sfR : HasStrongFellerKernel (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass))
    (sfS : HasStrongFellerKernel (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass)) :
    R • transferOperator (𝕜 := 𝕜) (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass) sfR =
      S • transferOperator (𝕜 := 𝕜) (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass) sfS := by
  ext f x
  change R • (∫ y, f y ∂(WeightedKernel.ofBoundedWeight K w R hw hR hwR mass).killedTransition x) =
    S • (∫ y, f y ∂(WeightedKernel.ofBoundedWeight K w S hw hS hwS mass).killedTransition x)
  rw [WeightedKernel.ofBoundedWeight_killedTransition,
    WeightedKernel.ofBoundedWeight_killedTransition,
    integral_normalized K w hw R hR, integral_normalized K w hw S hS,
    smul_smul, smul_smul, mul_inv_cancel₀ hR.ne', mul_inv_cancel₀ hS.ne']

end ConditionedStochasticStabilityHyperbolic.RawNormalizationIndependence
