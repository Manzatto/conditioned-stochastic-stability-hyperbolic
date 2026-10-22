module

public import ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerAnalyticPacket
public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLFamily

/-! Derived selected-layer data, constructed from ordinary deterministic
leading data and the actual physical source factory. This record is an output
interface; its spectral projectors and quasi-ergodic conclusions are not fields. -/
public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerAnalyticPacket
open LeanShared KellerLiverani1999
universe uZ uZret uCore

structure Selection
    {X Ξ Ω : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace Ξ] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    {K : Set X} [CompactSpace K]
    {C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K}
    {law : ℝ≥0 → Measure Ξ} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {scale pressure : ℝ} (d : Data K C law probability scale pressure)
    (T : X ≃ₜ X) (V G : Set X) (hK : IsCompact K)
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w wc : K → ℝ) (hw : Continuous w) (hwc : Measurable wc)
    (hscale : 0 < scale) (hwR : ∀ x, w x ≤ scale) (hwcR : ∀ x, wc x ≤ scale) where
  Z : Type uZ
  [zNormed : NormedAddCommGroup Z]
  [zScalar : NormedSpace ℂ Z]
  Zret : Type uZret
  [retNormed : NormedAddCommGroup Zret]
  [retScalar : NormedSpace ℂ Zret]
  Core : Type uCore
  [coreNormed : NormedAddCommGroup Core]
  [coreScalar : NormedSpace ℂ Core]
  kl : ClassicalContract (E := d.Strong) (W := d.Weak)
  det : DeterministicLeading (d.model.inputs.operator 0)
  cutoff : ℝ
  margin : ℝ
  principal_lt : d.model.inputs.principal / scale < cutoff
  cutoff_lt_rate : cutoff < det.rate
  cutoff_lt_weak : cutoff < d.model.inputs.weakRate / scale
  subordinate_lt : det.subordinate < cutoff
  margin_positive : 0 < margin
  margin_subordinate : margin < cutoff - det.subordinate
  margin_leading : margin < det.rate - cutoff
  cutoff_positive : 0 < cutoff
  rate_pressure : scale * det.rate = Real.exp pressure
  tests : Set (K →ᵇ ℝ)
  multipliers : tests → d.Strong →L[ℂ] d.Strong
  physicalSources : ∀ outputs : ProjectorOutputs d.model.inputs.operator
      (TwoNormNormalization.weakEmbedding d.inclusion) det cutoff margin,
    ∀ η : ℝ, 0 < η → ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      Nonempty (Global.NoFullSupportKLFamily.ScaleSources
        (Z := Z) (Zret := Zret) (Core := Core)
        T V K G hK (ρ ε) (F ε) (hF ε) w hw wc hwc scale hscale hwR hwcR
        outputs ε η tests multipliers)

attribute [instance] Selection.zNormed Selection.zScalar Selection.retNormed
  Selection.retScalar Selection.coreNormed Selection.coreScalar

end ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerAnalyticPacket
