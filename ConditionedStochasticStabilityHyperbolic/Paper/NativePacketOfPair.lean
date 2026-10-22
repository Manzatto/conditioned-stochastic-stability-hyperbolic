module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeNullPrefixSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedQuantitativeAnnealedPair
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedZero
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedRawTwoNorm
public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniConfinementSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniProjectorSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniParameters

/-! A native closed-layer packet from a produced analytic pair (global route, subordinate and
selected layers alike). The packet lives on the intermediate stage: its operators are the
normalized averaged intermediate operators, its radius bound is the deterministic radius bound of
the raw zero-noise generator at the pressure, and its spectrum comparison is the local
comparison of the live chain. Everything is generic in the Banach spaces. -/

public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeNullPrefixSources
open LeanShared KellerLiverani1999 ComplexStrongFeller

variable {S H W Ξ X : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [MeasurableSpace Ξ] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The native packet of a produced pair on its intermediate stage. -/
def packetOfPair (K : Set X) [CompactSpace K] (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K)
    {i : S →L[ℂ] H} {j : H →L[ℂ] W}
    {law : ℝ≥0 → Measure Ξ} {prob : ∀ ε, IsProbabilityMeasure (law ε)}
    {genS : ℝ≥0 → Ξ → S →L[ℂ] S} {genH : ℝ≥0 → Ξ → H →L[ℂ] H}
    {R ρ₀ ρ₁ weak₀ weak₁ : ℝ}
    (q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R ρ₀ ρ₁ weak₀ weak₁)
    (denseJ : DenseRange j) (pressure : ℝ) (PH : H →L[ℂ] H) (hH : ∀ z, genH 0 z = PH)
    (radius : spectralRadius ℂ PH ≤ ENNReal.ofReal (Real.exp pressure))
    (principal : ρ₁ ≤ Real.exp pressure)
    (comparison : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel (C ε), ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • transferOperator (𝕜 := ℂ) (C ε) sf) f = z • f →
        q.pair.intermediate.principal < ‖z‖ →
        z ∈ spectrum ℂ ((R : ℂ) • q.pair.intermediate.operator ε)) :
    NativePacket K C law prob R pressure where
  Strong := H
  Weak := W
  inclusion := j
  generator := genH
  model := {
    compactH := q.pair.compactH
    injectiveH := q.pair.injectiveH
    denseH := denseJ
    compactW := q.pair.compactH
    injectiveW := q.pair.injectiveH
    denseW := denseJ
    inputs := q.pair.intermediate
    generator_eq := q.pair.intermediate_generator }
  essential := essentialRadiusContract
  confinement := classicalConfinementContract
  radius_le := by
    have scalePos : 0 < R := zero_lt_one.trans_le q.pair.strong.scale_ge_one
    have hzero : ∀ z, q.pair.intermediate.generator 0 z = PH := fun z =>
      (q.pair.intermediate_generator 0 z).trans (hH z)
    change spectralRadius ℂ ((R : ℂ) • q.pair.intermediate.operator 0) ≤ _
    rw [q.pair.intermediate.raw_zero_of_constant_generators scalePos.ne' PH hzero]
    exact radius
  principal_le := by
    change q.pair.intermediate.principal ≤ _
    rw [q.principalH_eq]
    exact principal
  spectrumComparison := comparison

omit [CompleteSpace S] [Nontrivial H] in
/-- The deterministic radius bound of the raw zero-noise intermediate generator from any raw
upper-radius theorem: the intermediate record carries a compact two-norm estimate of the raw
generator at the principal rate. -/
theorem radius_of_raw {i : S →L[ℂ] H} {j : H →L[ℂ] W}
    {law : ℝ≥0 → Measure Ξ} {prob : ∀ ε, IsProbabilityMeasure (law ε)}
    {genS : ℝ≥0 → Ξ → S →L[ℂ] S} {genH : ℝ≥0 → Ξ → H →L[ℂ] H}
    {R ρ₀ ρ₁ weak₀ weak₁ : ℝ}
    (q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R ρ₀ ρ₁ weak₀ weak₁)
    (PH : H →L[ℂ] H) (hH : ∀ z, genH 0 z = PH) (pressure : ℝ)
    (upper : ∀ (k : H →L[ℂ] W), IsCompactOperator k →
      ∀ α R' C D : ℝ, 0 ≤ α → 0 ≤ R' → 0 ≤ C → 0 ≤ D →
      (∀ n x, ‖(PH ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R' ^ n * ‖k x‖) → α ≤ Real.exp pressure →
      spectralRadius ℂ PH ≤ ENNReal.ofReal (Real.exp pressure))
    (principal : ρ₁ ≤ Real.exp pressure) :
    spectralRadius ℂ PH ≤ ENNReal.ofReal (Real.exp pressure) := by
  have hzeroH : ∀ z, q.pair.intermediate.generator 0 z = PH := fun z =>
    (q.pair.intermediate_generator 0 z).trans (hH z)
  obtain ⟨CH, DH, RH, hCH, hDH, hRH, compactH, twoNormH⟩ := q.pair.intermediate.raw_two_norm
    essentialRadiusContract q.pair.injectiveH q.pair.compactH PH hzeroH
  rw [q.principalH_eq] at twoNormH
  have ρ₁pos : 0 ≤ ρ₁ := q.principalH_eq ▸ q.pair.intermediate.principal_pos.le
  exact upper _ compactH ρ₁ RH CH DH ρ₁pos hRH hCH hDH twoNormH principal

omit [CompleteSpace S] [CompleteSpace H] [Nontrivial H] [CompleteSpace W] in
/-- The contour of the selected layer: principal and weak rates of the intermediate record against
the normalized leading rate `e^P / R`. -/
theorem selected_rates {i : S →L[ℂ] H} {j : H →L[ℂ] W}
    {law : ℝ≥0 → Measure Ξ} {prob : ∀ ε, IsProbabilityMeasure (law ε)}
    {genS : ℝ≥0 → Ξ → S →L[ℂ] S} {genH : ℝ≥0 → Ξ → H →L[ℂ] H}
    {R ρ₀ ρ₁ weak₀ weak₁ : ℝ}
    (q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R ρ₀ ρ₁ weak₀ weak₁)
    (dm : DeterministicLeading (q.pair.intermediate.operator 0)) (P : ℝ)
    (rate : dm.rate = R⁻¹ * Real.exp P) (below : ρ₁ < Real.exp P) (weak : Real.exp P ≤ weak₁) :
    q.pair.intermediate.principal / R < dm.rate ∧ dm.rate ≤ q.pair.intermediate.weakRate / R ∧
      R * dm.rate = Real.exp P := by
  have hR : 0 < R := zero_lt_one.trans_le q.pair.strong.scale_ge_one
  rw [q.principalH_eq, q.weakRateH_eq, rate, div_eq_inv_mul, div_eq_inv_mul]
  refine ⟨mul_lt_mul_of_pos_left below (inv_pos.mpr hR),
    mul_le_mul_of_nonneg_left weak (inv_nonneg.mpr hR.le), ?_⟩
  rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

/-- The selected-layer extension of the native packet of a produced pair. -/
def selectionOfPair {Ω : Type*} [CompactSpace X] [SecondCountableTopology X]
    [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    (K : Set X) [CompactSpace K] (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K)
    {i : S →L[ℂ] H} {j : H →L[ℂ] W}
    {law : ℝ≥0 → Measure Ξ} {prob : ∀ ε, IsProbabilityMeasure (law ε)}
    {genS : ℝ≥0 → Ξ → S →L[ℂ] S} {genH : ℝ≥0 → Ξ → H →L[ℂ] H}
    {R ρ₀ ρ₁ weak₀ weak₁ : ℝ}
    (q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R ρ₀ ρ₁ weak₀ weak₁)
    (denseJ : DenseRange j) (pressure : ℝ) (PH : H →L[ℂ] H) (hH : ∀ z, genH 0 z = PH)
    (radius : spectralRadius ℂ PH ≤ ENNReal.ofReal (Real.exp pressure))
    (principal : ρ₁ ≤ Real.exp pressure)
    (comparison : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel (C ε), ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • transferOperator (𝕜 := ℂ) (C ε) sf) f = z • f →
        q.pair.intermediate.principal < ‖z‖ →
        z ∈ spectrum ℂ ((R : ℂ) • q.pair.intermediate.operator ε))
    (T : X ≃ₜ X) (V G : Set X) (hK : IsCompact K)
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w wc : K → ℝ) (hw : Continuous w) (hwc : Measurable wc)
    (hscale : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (dm : DeterministicLeading (q.pair.intermediate.operator 0))
    (hp : q.pair.intermediate.principal / R < dm.rate)
    (hw' : dm.rate ≤ q.pair.intermediate.weakRate / R)
    (ratePressure : R * dm.rate = Real.exp pressure)
    {Z Zret Core : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [NormedAddCommGroup Zret] [NormedSpace ℂ Zret] [NormedAddCommGroup Core] [NormedSpace ℂ Core]
    (tests : Set (K →ᵇ ℝ)) (multipliers : tests → H →L[ℂ] H)
    (physicalSources : ∀ outputs : ProjectorOutputs q.pair.intermediate.operator
        (TwoNormNormalization.weakEmbedding j) dm
        (contourParameters dm _ _ hp hw').cutoff (contourParameters dm _ _ hp hw').radius,
      ∀ η : ℝ, 0 < η → ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
        Nonempty (Global.NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
          T V K G hK (ρ ε) (F ε) (hF ε) w hw wc hwc R hscale hwR hwcR
          outputs ε η tests multipliers)) :
    NativeSelection (packetOfPair K C q denseJ pressure PH hH radius principal comparison)
      T V G hK ρ F hF w wc hw hwc hscale hwR hwcR where
  Z := Z
  Zret := Zret
  Core := Core
  kl := classicalContract
  det := dm
  cutoff := (contourParameters dm _ _ hp hw').cutoff
  margin := (contourParameters dm _ _ hp hw').radius
  principal_lt := (contourParameters dm _ _ hp hw').principal_lt
  cutoff_lt_rate := (contourParameters dm _ _ hp hw').cutoff_lt_rate
  cutoff_lt_weak := (contourParameters dm _ _ hp hw').cutoff_lt_weak
  subordinate_lt := (contourParameters dm _ _ hp hw').subordinate_lt
  margin_positive := (contourParameters dm _ _ hp hw').radius_pos
  margin_subordinate := (contourParameters dm _ _ hp hw').radius_subordinate
  margin_leading := (contourParameters dm _ _ hp hw').radius_leading
  cutoff_positive := (contourParameters dm _ _ hp hw').cutoff_pos
  rate_pressure := ratePressure
  tests := tests
  multipliers := multipliers
  physicalSources := physicalSources

end ConditionedStochasticStabilityHyperbolic.Paper.NativeNullPrefixSources
