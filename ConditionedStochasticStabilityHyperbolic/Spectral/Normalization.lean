module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ConditionedAverages
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedQuasiErgodic
import Mathlib.Tactic.FieldSimp

/-!
# Constant weight normalization preserves the spectral data

Raw manuscript transfers and probability-normalized killed transfers differ
by a positive scalar. The leading eigenvalue rescales; the eigenvector,
functional, projection and normalized power gap stay the same. This supplies
the spectral side of the already checked exact conditioned-law cancellation.
-/

@[expose] public noncomputable section

namespace ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one)

/-- Positive scalar rescaling constructs the corresponding leading data. -/
def rescale (c : ℝ) (hc : 0 < c) : RankOneSpectralData (c • P) one where
  rate := c * d.rate
  rate_pos := mul_pos hc d.rate_pos
  mean := d.mean
  eigenvector := d.eigenvector
  mean_eigenvector := d.mean_eigenvector
  mean_one_pos := d.mean_one_pos
  right_eigenvector := by rw [smul_apply, d.right_eigenvector, smul_smul]
  errorConstant := d.errorConstant
  errorConstant_nonneg := d.errorConstant_nonneg
  decay := d.decay
  decay_nonneg := d.decay_nonneg
  decay_lt_one := d.decay_lt_one
  power_gap := by
    have hn : (c * d.rate)⁻¹ • (c • P) = d.rate⁻¹ • P := by
      rw [smul_smul]
      congr 1
      field_simp
    intro n
    rw [hn]
    exact d.power_gap n

@[simp] theorem rescale_rate (c : ℝ) (hc : 0 < c) : (d.rescale c hc).rate = c * d.rate := rfl

@[simp] theorem rescale_mean (c : ℝ) (hc : 0 < c) : (d.rescale c hc).mean = d.mean := rfl

@[simp] theorem rescale_eigenvector (c : ℝ) (hc : 0 < c) :
    (d.rescale c hc).eigenvector = d.eigenvector := rfl

theorem rescale_normalizedOperator (c : ℝ) (hc : 0 < c) :
    (d.rescale c hc).normalizedOperator = d.normalizedOperator := by
  change (c * d.rate)⁻¹ • (c • P) = d.rate⁻¹ • P
  rw [smul_smul]
  congr 1
  field_simp

theorem rescale_projection (c : ℝ) (hc : 0 < c) :
    (d.rescale c hc).projection = d.projection := rfl

/-- Convert raw spectral data using the actual normalization identity. -/
def ofRawNormalization (R : ℝ) (hR : 0 < R) {Q : E →L[ℝ] E}
    (hQ : R⁻¹ • P = Q) : RankOneSpectralData Q one :=
  hQ ▸ d.rescale R⁻¹ (inv_pos.mpr hR)

@[simp] theorem ofRawNormalization_mean (R : ℝ) (hR : 0 < R) {Q : E →L[ℝ] E}
    (hQ : R⁻¹ • P = Q) : (d.ofRawNormalization R hR hQ).mean = d.mean := by
  subst Q
  rfl

@[simp] theorem ofRawNormalization_eigenvector (R : ℝ) (hR : 0 < R) {Q : E →L[ℝ] E}
    (hQ : R⁻¹ • P = Q) : (d.ofRawNormalization R hR hQ).eigenvector = d.eigenvector := by
  subst Q
  rfl

end ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.RestrictedQuasiErgodic

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
  (F : X × Ω → X) (hF : Measurable F) (U : Set X) (hU : MeasurableSet U)
  (w : U → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (hSF : RestrictedStrongFeller.HasStrongFellerNoise ρ F hF)
  (d : RankOneSpectralData
    (RestrictedStrongFeller.rawTransferOperator ρ F hF U hU w hw hw0 R hR hwR hSF)
    (1 : U →ᵇ ℝ))
  (μ : Measure U) [IsFiniteMeasure μ]
  (hmean : ∀ f : U →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)

include hmean in
/-- Raw manuscript spectral data give the same actual quasi-ergodic product
for the probability-normalized live-state chain. -/
theorem raw_eigenvectorMeasure_isQuasiErgodic :
    (RestrictedNoise.chain ρ F hF U hU w hw.measurable R hR hwR).IsQuasiErgodic
      (LeanShared.eigenvectorMeasure μ d.eigenvector) := by
  let dn := d.ofRawNormalization R hR
    (RestrictedStrongFeller.inv_smul_rawTransferOperator ρ F hF U hU w hw hw0 R hR hwR hSF)
  have hnmean (f : U →ᵇ ℝ) : dn.mean f = ∫ y, f y ∂μ := by
    simpa only [dn, RankOneSpectralData.ofRawNormalization_mean] using hmean f
  have hq := eigenvectorMeasure_isQuasiErgodic ρ F hF U hU w hw hw0 R hR hwR hSF dn μ hnmean
  simpa only [dn, RankOneSpectralData.ofRawNormalization_eigenvector] using hq

end ConditionedStochasticStabilityHyperbolic.RestrictedQuasiErgodic
