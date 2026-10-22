module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNativeLayerComparison
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldCoreNontrivial
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeCorePacket
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProvedCommonAmbientComparison
public import LeanShared.Geometry.NativeFullTestPhysical

/-! Native spectrum comparison and nontriviality while the model and test space remain abstract.
The core packet, its restriction identity and the classical comparison are constructed before
specialization to a concrete carrier, exactly as for the scale sources. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory Filter IsManifold Bundle
open scoped Topology Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoFullSupportScaleSourcesNative
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999

theorem spectrum_from_packet
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
    (ν : Measure M) [IsFiniteMeasure (ν.comap (Subtype.val : K → M))]
    (testView : Test →ₗ[ℂ] (M → ℂ)) (testView_injective : Function.Injective testView)
    (qt : TestCore →ₗ[ℂ] Test)
    (layer : LayerNoiseClassicalSources.Data T V K G B hK law
      (fun ε (z : M × Noise) => m.maps (noise ε z.2) z.1) hF w hw wc hwc R hR hwR hwcR (ν.comap (Subtype.val : K → M))
      testView testView_injective qt)
    (globalPhysical : Test →L[ℂ] (K →ᵇ ℂ))
    (includeReg : Reg →L[ℂ] Test)
    (include_view : ∀ v, globalPhysical (includeReg v) = physicalRealization V K m.regularCore v)
    (denseTest : DenseRange qt)
    (aFull : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (haFull : Function.Injective aFull)
    (core : ∀ c t, aFull (coreLift m.qa c) t =
      ∫ x, functions V c x * testView t x ∂ν)
    (incView : ∀ v x, testView (includeReg v) x = m.view v x)
    (C : ℝ) (uniform : ∀ c, ‖physicalCore V K c‖ ≤ C * ‖m.regularCore c‖)
    (regularBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖m.regularCore (multiplier V ψ hψ c)‖ ≤ B * ‖m.regularCore c‖)
    (analyticBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖coreLift m.qa (multiplier V ψ hψ c)‖ ≤ B * ‖coreLift m.qa c‖)
    (injectivej : Function.Injective j) (compactj : IsCompactOperator j)
    (physical_eq : ∀ v x, globalPhysical v x = testView v x.val)
    (x₀ : M) (hx₀ : x₀ ∈ V) :
    Nontrivial m.StrongSpace ∧ Paper.NativeLayerComparison.SpectrumComparison
      (fun ε => RestrictedNoise.chain (law ε)
        (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet w hw.measurable
          R hR hwR) R inputs.principal inputs.operator := by
  let p := PhysicalModelNativeCorePacket.coreData m ν aFull testView core includeReg incView K
    hK.isClosed layer.live_subset C uniform regularBound analyticBound
  refine ⟨p.nontrivial (SmoothSupportedManifoldCore.physicalRealization V K m.regularCore)
    (fun c => SmoothSupportedManifoldCore.physicalRealization_core V K m.regularCore
      m.regularCore_dense p.uniformConstant p.uniformBound c)
    m.regularCore_dense hK.isClosed layer.live_open ⟨x₀, layer.live_subset hx₀⟩ hx₀
    layer.reference_positive, ?_⟩
  exact spectrum_of_layer m analytic n law noise hnoise j R inputs hgenerator T K G B hK
    hF w hw wc hwc hR hwR hwcR hweight (SmoothPhysicalTests.tests (E := E) K)
    (ν.comap (Subtype.val : K → M)) testView testView_injective qt layer p
    globalPhysical includeReg include_view denseTest aFull haFull
    (fun c d => PhysicalModelNativeCoreData.smoothFull m ν aFull testView core K hK.isClosed
      layer.live_subset globalPhysical physical_eq c (qt d))
    (fun c d => (PhysicalModelNativeCorePacket.coreData_embedding m ν aFull testView core
      includeReg incView K hK.isClosed layer.live_subset C uniform regularBound analyticBound
      (coreLift m.qa c) (m.regularCore d)).symm)
    injectivej compactj physical_eq CommonAmbientClassicalComparison.classicalContract

set_option maxHeartbeats 2000000 in
/-- Native full-test spectrum comparison with the distribution constructed internally. -/
theorem native_spectrum_of_layer
    {E U M AtlasIndex Reg A Ω : Type*}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
      [MeasurableSpace U] [BorelSpace U]
      [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
      [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
      [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
      [T2Space M] [CompactSpace M]
      [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
      {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
      [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
    {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
      (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
        (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
    [MetricSpace Ω]
    (refData : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (bt : ℝ) (hbt : 0 < bt) (hbt1 : bt ≤ 1)
    (localBound : PhysicalModelFullTestPairing.LocalPairing m bt)
    {TestCore : Type*}
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
    [IsFiniteMeasure ((refData.measure volume).comap (Subtype.val : K → M))]
    (qt : TestCore →ₗ[ℂ] (NativeFullHolderTests.Full (E := E) (M := M) bt hbt1))
    (layer : LayerNoiseClassicalSources.Data T V K G B hK law
      (fun ε (z : M × Noise) => m.maps (noise ε z.2) z.1) hF w hw wc hwc R hR hwR hwcR ((refData.measure volume).comap (Subtype.val : K → M))
      (NativeFullHolderTests.view (E := E) (M := M) bt hbt1) (NativeFullHolderTests.view_injective (E := E) (M := M) bt hbt1) qt)
    (includeReg : Reg →L[ℂ] (NativeFullHolderTests.Full (E := E) (M := M) bt hbt1))
    (include_view : ∀ v, (NativeFullHolderTests.globalPhysical (E := E) (M := M) bt hbt1 K) (includeReg v) = physicalRealization V K m.regularCore v)
    (denseTest : DenseRange qt)
    (incView : ∀ v x, (NativeFullHolderTests.view (E := E) (M := M) bt hbt1) (includeReg v) x = m.view v x)
    (C : ℝ) (uniform : ∀ c, ‖physicalCore V K c‖ ≤ C * ‖m.regularCore c‖)
    (regularBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖m.regularCore (multiplier V ψ hψ c)‖ ≤ B * ‖m.regularCore c‖)
    (analyticBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖coreLift m.qa (multiplier V ψ hψ c)‖ ≤ B * ‖coreLift m.qa c‖)
    (injectivej : Function.Injective j) (compactj : IsCompactOperator j)
    (x₀ : M) (hx₀ : x₀ ∈ V) :
    Nontrivial m.StrongSpace ∧ Paper.NativeLayerComparison.SpectrumComparison
      (fun ε => RestrictedNoise.chain (law ε)
        (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet w hw.measurable
          R hR hwR) R inputs.principal inputs.operator := by
  let aFull := PhysicalModelFullTestDistribution.aFull m refData hbt hbt1 localBound
  let n0 := spectrum_from_packet (Test := NativeFullHolderTests.Full (E := E) (M := M) bt hbt1) m analytic n law noise hnoise j R inputs hgenerator T K G B hK
    hF w hw wc hwc hR hwR hwcR hweight (refData.measure volume)
    (NativeFullHolderTests.view (E := E) (M := M) bt hbt1) (NativeFullHolderTests.view_injective (E := E) (M := M) bt hbt1) qt layer

  let n1 := n0 (NativeFullHolderTests.globalPhysical (E := E) (M := M) bt hbt1 K) includeReg include_view denseTest

  let n2 := n1 aFull (PhysicalModelFullTestDistribution.aFull_injective m refData hbt hbt1 localBound)
    (fun c t => PhysicalModelFullTestDistribution.aFull_core m refData hbt hbt1 localBound c t)

  let n3 := n2 incView C uniform regularBound analyticBound injectivej compactj
    (NativeFullHolderTests.globalPhysical_apply (E := E) (M := M) bt hbt1 K) x₀ hx₀

  exact n3

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoFullSupportScaleSourcesNative
