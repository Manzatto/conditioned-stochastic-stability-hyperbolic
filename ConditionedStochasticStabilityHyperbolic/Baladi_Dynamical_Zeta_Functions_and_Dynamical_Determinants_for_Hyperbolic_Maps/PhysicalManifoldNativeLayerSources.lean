module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNoFullSupportScaleSourcesNative
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.LayerNoiseClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusSource
meta import Lean.LibrarySuggestions.Basic

/-! The native eventual source packet from one ordinary layer record. The noise, plaque,
smoothing, density, inverse-action and Jacobian inputs of
`PhysicalManifoldNoFullSupportScaleSourcesNative.eventual_sources` are exactly the fields of a
`LayerNoiseClassicalSources.Data` for the model's literal noisy maps. -/
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalManifoldNativeLayerSources"

public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped Topology
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoFullSupportScaleSourcesNative
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999

theorem eventual_sources_of_layer
    {E U M AtlasIndex Reg A Ω : Type*}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
      [MeasurableSpace U] [BorelSpace U]
      [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
      [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
      [T2Space M] [CompactSpace M]
      [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
      {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
      [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
    {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
      (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
        (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
    [MetricSpace Ω]
    {Test TestCore : Type*}
      [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
      [AddCommGroup TestCore] [Module ℂ TestCore]
    {Lrows : ℝ} (analytic : PhysicalModelAnalytic.AnalyticBound m Lrows)
    (n : PhysicalManifoldNoiseSources.Data m)
    {Noise W : Type*} [TopologicalSpace Noise] [MeasurableSpace Noise]
    [OpensMeasurableSpace Noise] [SecondCountableTopology Noise] [CompactSpace Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise : ℝ≥0 → Noise → Ω) (hnoise : ∀ ε, Continuous (noise ε))
    (j : m.StrongSpace →L[ℂ] W) (R : ℝ)
    (inputs : ActualAnnealedInputs law (fun _ => inferInstance) j R)
    (hgenerator : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    (T : M ≃ₜ M) (K G B : Set M) [CompactSpace K] (hK : IsCompact K)
    (hF : ∀ ε, Measurable (fun z : M × Noise => m.maps (noise ε z.2) z.1))
    (w : K → ℝ) (hw : Continuous w) (wc : K → ℝ) (hwc : Measurable wc)
    (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (hweight : ∀ x : K, m.weight x.val = wc x)
    (Tests : Set (K →ᵇ ℝ)) (σ : Measure K) [IsFiniteMeasure σ]
    (testView : Test →ₗ[ℂ] (M → ℂ)) (testView_injective : Function.Injective testView)
    (qt : TestCore →ₗ[ℂ] Test)
    (layer : LayerNoiseClassicalSources.Data T V K G B hK law
      (fun ε (z : M × Noise) => m.maps (noise ε z.2) z.1) hF w hw wc hwc R hR hwR hwcR σ
      testView testView_injective qt)
    (p : PhysicalManifoldSupportedCore.CoreData (K := K) (Tests := Tests) (σ := σ)
      m.regularCore (coreLift m.qa))
    (r t sn u : ℝ) (margins : RegularCoreApproximation.RegularityMargins r t sn u)
    (globalPhysical : Test →L[ℂ] (K →ᵇ ℂ))
    (includeReg : Reg →L[ℂ] Test)
    (include_view : ∀ v, globalPhysical (includeReg v) = physicalRealization V K m.regularCore v)
    (denseTest : DenseRange qt)
    (aFull : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (haFull : Function.Injective aFull)
    (smoothFull : ∀ c d, aFull (coreLift m.qa c) (qt d) =
      ∫ x, physicalCore V K c x * globalPhysical (qt d) x ∂σ)
    (smoothRestriction : ∀ c d, aFull (coreLift m.qa c) (includeReg (m.regularCore d)) =
      p.embedding (coreLift m.qa c) (m.regularCore d))
    (injectivej : Function.Injective j) (compactj : IsCompactOperator j)
    {det : DeterministicLeading (inputs.operator 0)} {q δ : ℝ}
    (o : ProjectorOutputs inputs.operator (TwoNormNormalization.weakEmbedding j) det q δ)
    (hδsub : δ < q - det.subordinate) (hδlead : δ < det.rate - q) (hq : 0 < q)
    (hprincipal : inputs.principal / R < q)
    (conjugation : ∀ ε, RealOperatorConjugation (inputs.operator ε))
    (physical_eq : ∀ v x, globalPhysical v x = testView v x.val)
    (classical : CommonAmbientClassicalComparison.ClassicalContract (A := m.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K m.regularCore))
      (Z := Test →L[ℂ] ℂ) (Reg := Reg) (W := W)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Nonempty (Global.NoFullSupportKLFamily.ScaleSources (Z := Reg →L[ℂ] ℂ)
        (Zret := (RetainedRegularTests.space (⟨B, layer.retained_open⟩ : TopologicalSpace.Opens M) V
          m.regularCore (subset_closure.trans layer.retained_live) →L[ℂ] ℂ)) (Core := Reg)
        T V K G hK (law ε) (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε)
        w hw wc hwc R hR hwR hwcR o ε η Tests
        (fun t => ConstructedRegularMultipliers.analyticMultiplier (coreLift m.qa)
          (SmoothSupportedManifoldCore.multiplier V (p.test t) (p.test_smooth t)))) :=
  eventual_sources m analytic n law noise hnoise j R inputs hgenerator T K G B hK
    layer.live_open layer.live_subset layer.retained_open layer.core_retained layer.retained_live
    layer.no_return hF layer.close layer.plaques w hw wc hwc layer.cutoff_nonnegative hR hwR hwcR
    hweight layer.weight_agreement layer.smoothingWindow layer.smoothingWindow_positive
    layer.originalSF layer.cutoffSF layer.inverse_density Tests σ p r t sn u margins
    layer.reference_positive layer.cutoff_support globalPhysical includeReg include_view qt
    denseTest aFull haFull smoothFull smoothRestriction essentialRadiusContract injectivej
    compactj o hδsub hδlead hq hprincipal conjugation testView testView_injective physical_eq
    layer.inverseMap layer.inverseWeight layer.inverseWindow layer.inverseWindow_positive
    layer.inverseRegular layer.inverse_joint layer.inverse_weight_joint layer.smooth_continuous
    layer.inverseExponent layer.inverseExponent_positive layer.inverseInterpolationConstant
    layer.inverse_interpolation layer.jacobian layer.ultra layer.fredholm layer.riesz classical

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoFullSupportScaleSourcesNative
