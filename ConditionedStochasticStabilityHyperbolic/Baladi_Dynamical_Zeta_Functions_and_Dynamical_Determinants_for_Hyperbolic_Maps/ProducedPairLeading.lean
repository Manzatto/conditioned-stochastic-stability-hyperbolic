module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedQuantitativeAnnealedPair
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedRawTwoNorm
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingRescale
public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusSource

/-! The deterministic leading records of a produced analytic pair. The zero-noise generators of both
strong records are fixed operators; each record carries their raw compact two-norm estimate with
the principal rate, so a raw leading theorem for each operator gives leading records of the
normalized zero-noise operators at rate `λ / R`. -/
public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
open KellerLiverani1999 LeanShared.TwoNormNormalization

variable {S H W Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [MeasurableSpace Z]

theorem QuantitativeData.leading {i : S →L[ℂ] H} {j : H →L[ℂ] W}
    {law : ℝ≥0 → Measure Z} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {genS : ℝ≥0 → Z → S →L[ℂ] S} {genH : ℝ≥0 → Z → H →L[ℂ] H}
    {R ρ₀ ρ₁ weak₀ weak₁ : ℝ}
    (q : QuantitativeData i j law probability genS genH R ρ₀ ρ₁ weak₀ weak₁)
    (PS : S →L[ℂ] S) (PH : H →L[ℂ] H) (hS : ∀ z, genS 0 z = PS) (hH : ∀ z, genH 0 z = PH)
    (lam : ℝ) (gap₀ : ρ₀ < lam) (gap₁ : ρ₁ < lam)
    (lead₀ : ∀ (k : S →L[ℂ] W), IsCompactOperator k →
      ∀ α R' C D : ℝ, 0 ≤ α → 0 ≤ R' → 0 ≤ C → 0 ≤ D →
      (∀ n x, ‖(PS ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R' ^ n * ‖k x‖) → α < lam →
      ∃ d : DeterministicLeading PS, d.rate = lam)
    (lead₁ : ∀ (k : H →L[ℂ] W), IsCompactOperator k →
      ∀ α R' C D : ℝ, 0 ≤ α → 0 ≤ R' → 0 ≤ C → 0 ≤ D →
      (∀ n x, ‖(PH ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R' ^ n * ‖k x‖) → α < lam →
      ∃ d : DeterministicLeading PH, d.rate = lam) :
    ∃ ds : DeterministicLeading (q.pair.strong.operator 0),
    ∃ dm : DeterministicLeading (q.pair.intermediate.operator 0),
      ds.rate = R⁻¹ * lam ∧ dm.rate = R⁻¹ * lam := by
  have hzeroS : ∀ z, q.pair.strong.generator 0 z = PS := fun z =>
    (q.pair.strong_generator 0 z).trans (hS z)
  have hzeroH : ∀ z, q.pair.intermediate.generator 0 z = PH := fun z =>
    (q.pair.intermediate_generator 0 z).trans (hH z)
  have scalePos : 0 < R := zero_lt_one.trans_le q.pair.strong.scale_ge_one
  obtain ⟨CS, DS, RS, hCS, hDS, hRS, compactS, twoNormS⟩ := q.pair.strong.raw_two_norm
    essentialRadiusContract (q.pair.injectiveH.comp q.pair.injectiveS)
    (q.pair.compactS.clm_comp j) PS hzeroS
  obtain ⟨CH, DH, RH, hCH, hDH, hRH, compactH, twoNormH⟩ := q.pair.intermediate.raw_two_norm
    essentialRadiusContract q.pair.injectiveH q.pair.compactH PH hzeroH
  rw [q.principalS_eq] at twoNormS
  rw [q.principalH_eq] at twoNormH
  have ρ₀pos : 0 ≤ ρ₀ := q.principalS_eq ▸ q.pair.strong.principal_pos.le
  have ρ₁pos : 0 ≤ ρ₁ := q.principalH_eq ▸ q.pair.intermediate.principal_pos.le
  obtain ⟨d₀, rate₀⟩ := lead₀ _ compactS ρ₀ RS CS DS ρ₀pos hRS hCS hDS twoNormS gap₀
  obtain ⟨d₁, rate₁⟩ := lead₁ _ compactH ρ₁ RH CH DH ρ₁pos hRH hCH hDH twoNormH gap₁
  refine ⟨d₀.normalizeOfRaw R scalePos
      (q.pair.strong.raw_zero_of_constant_generators scalePos.ne' _ hzeroS),
    d₁.normalizeOfRaw R scalePos
      (q.pair.intermediate.raw_zero_of_constant_generators scalePos.ne' _ hzeroH), ?_, ?_⟩
  · rw [DeterministicLeading.normalizeOfRaw_rate, rate₀]
  · rw [DeterministicLeading.normalizeOfRaw_rate, rate₁]

end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
