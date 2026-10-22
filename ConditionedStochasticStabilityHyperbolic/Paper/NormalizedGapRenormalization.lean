module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow
public import ConditionedStochasticStabilityHyperbolic.Spectral.Normalization
public import ConditionedStochasticStabilityHyperbolic.Spectral.RawNormalizationIndependence
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Independently constructed analytic models may choose different positive
normalizers. The full normalized gap transports between those choices while
the probability, eigenvector and represented left measure stay the same. -/
public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NormalizedGapRenormalization
open LeanShared

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A change of normalizing bound needs no new spectral construction and
preserves the exact probability already produced by the physical theorem. -/
theorem normalizedGap (K : Kernel X X) (w : X → ℝ) (hw : Measurable w)
    (mass : ∀ x, K x univ ≤ 1) (R S : ℝ) (hR : 0 < R) (hS : 0 < S)
    (hwR : ∀ x, w x ≤ R) (hwS : ∀ x, w x ≤ S)
    (core : Set X) (ν : ProbabilityMeasure X)
    (gap : LocalConclusions.NormalizedGap
      (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass) core ν) :
    LocalConclusions.NormalizedGap
      (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass) core ν := by
  obtain ⟨sfR, d, hproduct, hpositive⟩ := gap
  let CR := WeightedKernel.ofBoundedWeight K w R hw hR hwR mass
  let CS := WeightedKernel.ofBoundedWeight K w S hw hS hwS mass
  let sfS : HasStrongFellerKernel CS :=
    RawNormalizationIndependence.strongFeller K w hw mass R S hR hS hwR hwS sfR
  have hoperator : S⁻¹ • (R • strongFellerTransferOperator CR sfR) =
      strongFellerTransferOperator CS sfS := by
    ext f x
    change S⁻¹ * (R * (strongFellerTransferOperator CR sfR f x)) =
      strongFellerTransferOperator CS sfS f x
    rw [strongFellerTransferOperator_represents, strongFellerTransferOperator_represents,
      WeightedKernel.ofBoundedWeight_killedTransition,
      WeightedKernel.ofBoundedWeight_killedTransition,
      RawNormalizationIndependence.integral_normalized K w hw R hR,
      RawNormalizationIndependence.integral_normalized K w hw S hS]
    simp only [smul_eq_mul]
    rw [← mul_assoc R, mul_inv_cancel₀ hR.ne', one_mul]
  let raw := d.rescale R hR
  let ds := raw.ofRawNormalization S hS hoperator
  have hmean : ds.mean = d.mean := by
    simp only [ds, RankOneSpectralData.ofRawNormalization_mean, raw,
      RankOneSpectralData.rescale_mean]
  have hvector : ds.eigenvector = d.eigenvector := by
    simp only [ds, RankOneSpectralData.ofRawNormalization_eigenvector, raw,
      RankOneSpectralData.rescale_eigenvector]
  let posR : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ strongFellerTransferOperator CR sfR f x := by
    intro f hf x
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  let posS : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ strongFellerTransferOperator CS sfS f x := by
    intro f hf x
    rw [strongFellerTransferOperator_represents]
    exact integral_nonneg hf
  have hmeasure : ds.eigenmeasure posS = d.eigenmeasure posR := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [← ds.eigenmeasure_represents posS, ← d.eigenmeasure_represents posR, hmean]
  refine ⟨sfS, ds, ?_, ?_⟩
  · rw [hmeasure, hvector]
    exact hproduct
  · intro x hx
    rw [hvector]
    exact hpositive x hx

/-- The same result for the literal live-state noisy process. -/
theorem restrictedNoise {Y Ω : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : Y × Ω → Y) (hF : Measurable F)
    (U : Set Y) (hU : MeasurableSet U) [CompactSpace U]
    (w : U → ℝ) (hw : Measurable w) (R S : ℝ) (hR : 0 < R) (hS : 0 < S)
    (hwR : ∀ x, w x ≤ R) (hwS : ∀ x, w x ≤ S)
    (core : Set U) (ν : ProbabilityMeasure U)
    (gap : LocalConclusions.NormalizedGap
      (RestrictedNoise.chain ρ F hF U hU w hw R hR hwR) core ν) :
    LocalConclusions.NormalizedGap
      (RestrictedNoise.chain ρ F hF U hU w hw S hS hwS) core ν :=
  normalizedGap (RestrictedNoise.liveKernel ρ F hF U hU) w hw
    (RestrictedNoise.liveKernel_mass_le_one ρ F hF U hU) R S hR hS hwR hwS core ν gap

end ConditionedStochasticStabilityHyperbolic.Paper.NormalizedGapRenormalization
