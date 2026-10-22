module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNoFullSupportScaleSourcesNative
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldSubordinateComparisonNative
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.LayerNoiseClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLayerComparison
public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusSource
meta import Lean.LibrarySuggestions.Basic

/-! The native individual eigencomparison of a model from one ordinary layer record. The inverse
test action, its measurability, its bound and its change of variables are the projections of the
layer's ordinary inverse sources, exactly as inside the eventual source packet. -/
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalManifoldNativeLayerComparison"

public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped Topology
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoFullSupportScaleSourcesNative
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999

theorem comparison_of_layer
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
    (physical_eq : ∀ v x, globalPhysical v x = testView v x.val)
    (classical : CommonAmbientClassicalComparison.ClassicalContract (A := m.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K m.regularCore))
      (Z := Test →L[ℂ] ℂ) (Reg := Reg) (W := W)) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel (RestrictedNoise.chain (law ε)
        (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet wc hwc R hR hwcR),
      ∀ (f : K →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
        (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ)
          (RestrictedNoise.chain (law ε)
            (fun p : M × Noise => m.maps (noise ε p.2) p.1) (hF ε) K hK.measurableSet wc hwc R hR
              hwcR) sf) f = z • f →
        inputs.principal < ‖z‖ → ∃ v : m.StrongSpace, v ≠ 0 ∧ ((R : ℂ) • inputs.operator ε) v = z • v :=
  PhysicalManifoldSubordinateComparisonNative.eventually_individual_eigencomparison m analytic n law
    noise hnoise j R inputs hgenerator K p.uniformConstant p.uniformBound layer.live_subset
    hK.measurableSet hF wc hwc layer.cutoff_nonnegative hR hwcR hweight hK.isClosed layer.live_open
    layer.cutoff_support σ layer.reference_positive globalPhysical includeReg include_view qt
    denseTest aFull haFull smoothFull p.embedding smoothRestriction essentialRadiusContract
    injectivej compactj layer.inverseWindow layer.inverseWindow_positive
    (fun ε hp hw => (layer.inverseRegular ε hp hw).operator testView_injective)
    (fun ε hp hw => InverseRegularTransfer.operator_aestronglyMeasurable testView_injective
      (layer.inverseRegular ε hp hw) (law ε) qt denseTest (fun c =>
        (InverseRegularTransfer.continuous_operator_core testView_injective
          (layer.inverseRegular ε hp hw) qt (layer.inverse_joint ε hp hw)
          (layer.inverse_weight_joint ε hp hw) layer.smooth_continuous layer.inverseExponent
          layer.inverseExponent_positive (layer.inverseInterpolationConstant ε)
          (layer.inverse_interpolation ε hp hw) c).aestronglyMeasurable))
    (fun ε hp hw => (layer.inverseRegular ε hp hw).bound)
    (fun ε hp hw => (layer.inverseRegular ε hp hw).operator_norm_le testView_injective)
    (fun ε hp hw => InverseRegularTransfer.changeVariables_of_jacobian testView_injective
      (layer.inverseRegular ε hp hw) K (fun z : M × Noise => m.maps (noise ε z.2) z.1) wc σ
      globalPhysical physical_eq (layer.jacobian ε hp hw))
    layer.ultra classical


/-- The original-weight spectrum comparison of a model on one ordinary layer: every eigenvalue of
the live physical-weight chain above the principal rate is in the spectrum of the scaled annealed
operator. The cutoff and the physical weight agree on the separating retained collar. -/
theorem spectrum_of_layer
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
    (physical_eq : ∀ v x, globalPhysical v x = testView v x.val)
    (classical : CommonAmbientClassicalComparison.ClassicalContract (A := m.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K m.regularCore))
      (Z := Test →L[ℂ] ℂ) (Reg := Reg) (W := W)) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel (RestrictedNoise.chain (law ε)
        (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet w hw.measurable
          R hR hwR),
      ∀ (f : K →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
        (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) _ sf) f = z • f →
        inputs.principal < ‖z‖ → z ∈ spectrum ℂ ((R : ℂ) • inputs.operator ε) := by
  have cut := comparison_of_layer m analytic n law noise hnoise j R inputs hgenerator T K G B hK
    hF w hw wc hwc hR hwR hwcR hweight Tests σ testView testView_injective qt layer p
    globalPhysical includeReg include_view denseTest aFull haFull smoothFull smoothRestriction
    injectivej compactj physical_eq classical
  have sfCut : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel (RestrictedNoise.chain (law ε)
      (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet wc hwc R hR
        hwcR) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (eventually_le_nhds layer.smoothingWindow_positive)] with ε he hs
    exact layer.cutoffSF ε he hs
  exact Paper.NativeLayerComparison.original_spectrum_of_cutoff_eigenvectors T K B hK
    layer.retained_open layer.core_retained (layer.retained_live.trans layer.live_subset)
    layer.no_return law (fun ε (z : M × Noise) => m.maps (noise ε z.2) z.1) hF w wc
    hw.measurable hwc R hR hwR hwcR (fun x hx => (layer.weight_agreement x hx).symm)
    (fun ε => (R : ℂ) • inputs.operator ε) inputs.principal inputs.principal_pos.le layer.close
    sfCut cut

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoFullSupportScaleSourcesNative
