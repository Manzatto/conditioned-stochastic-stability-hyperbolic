module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedPairLeading
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingUniqueness

/-! The consumer ratio of a produced analytic pair from the raw product value. If every leading
record of the raw zero-noise intermediate generator at rate `λ` has product value `I`, then for
any leading records of the normalized zero-noise operators at the common rate `λ / R` the
consumer ratio has real part `I`. -/
public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
open KellerLiverani1999

variable {S H W Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [MeasurableSpace Z]

omit [CompleteSpace W] in
theorem QuantitativeData.identified_ratio {i : S →L[ℂ] H} {j : H →L[ℂ] W}
    {law : ℝ≥0 → Measure Z} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {genS : ℝ≥0 → Z → S →L[ℂ] S} {genH : ℝ≥0 → Z → H →L[ℂ] H}
    {R ρ₀ ρ₁ weak₀ weak₁ : ℝ}
    (q : QuantitativeData i j law probability genS genH R ρ₀ ρ₁ weak₀ weak₁)
    (PH : H →L[ℂ] H) (hH : ∀ z, genH 0 z = PH)
    (ds : DeterministicLeading (q.pair.strong.operator 0))
    (dm : DeterministicLeading (q.pair.intermediate.operator 0)) (hrate : ds.rate = dm.rate)
    (lam : ℝ) (hdm : dm.rate = R⁻¹ * lam) (M : H →L[ℂ] H) (value : ℝ)
    (identified : ∀ d : DeterministicLeading PH, d.rate = lam → (d.mean (M d.vector)).re = value) :
    (dm.mean (M (i ds.vector)) / dm.mean (i ds.vector)).re = value := by
  have hzeroH : ∀ z, q.pair.intermediate.generator 0 z = PH := fun z =>
    (q.pair.intermediate_generator 0 z).trans (hH z)
  have scalePos : 0 < R := zero_lt_one.trans_le q.pair.strong.scale_ge_one
  have raw := q.pair.intermediate.raw_zero_of_constant_generators scalePos.ne' _ hzeroH
  have hdraw : ((dm.rescale R scalePos).transport raw).rate = lam := by
    rw [DeterministicLeading.transport_rate, DeterministicLeading.rescale_rate, hdm, ← mul_assoc,
      mul_inv_cancel₀ scalePos.ne', one_mul]
  exact DeterministicLeading.ratio_of_raw ((dm.rescale R scalePos).transport raw) R scalePos _ raw
    i q.pair.injectiveS _ (q.pair.compatible 0) ds dm hrate M value (identified _ hdraw)

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
