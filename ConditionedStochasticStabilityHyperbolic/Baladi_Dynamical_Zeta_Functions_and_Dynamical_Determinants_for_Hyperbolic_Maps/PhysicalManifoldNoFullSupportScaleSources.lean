module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldCommonCoreComparison
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldScalarNormalization
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldSupportedCore
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualInverseAdjointSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.InverseRegularNoiseContinuity
public import LeanShared.Geometry.RetainedClosedPairing
public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLFamily
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualCutoffCommonCoreFacts
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualCutoffAdjoint
public import ConditionedStochasticStabilityHyperbolic.Spectral.SupportedCommonCoreFacts

/-! The actual physical model produces the eventual closed-layer source packet.
Reference positivity is required only on the open live region; no equality
σ.support = K is imposed on closed layers with null dangling boundary pieces.
Common-core spectral comparisons, geometric restriction/lifting, and the
physical invariant multiplier core are constructed inside the proof.

The ordinary full-test inverse family is for the RAW CUTOFF operator.
The independent volume/plaque certificate concerns the NORMALIZED ORIGINAL
killed chain; its inverse weight therefore includes the same factor 1/R.
These operators need not have identical inverse weights off the retained
region. Strong-Feller sources are required only at positive scales within
one ordinary perturbation window, never for the deterministic scale zero.
-/
public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped Topology
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoFullSupportScaleSources
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999

private theorem genericScalar_eq {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ℂ) (P : H →L[ℂ] H) : PhysicalManifoldModel.genericScalar c P = c • P := rfl

theorem eventual_sources
    {E U M AtlasIndex Reg A Ω : Type*}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
      [MeasurableSpace U] [BorelSpace U]
      [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
      [T2Space M] [CompactSpace M]
      [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
      {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
      [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
    
    {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
      (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
    
    
    [MetricSpace Ω]
    
    {Test TestCore : Type*}
      [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
      [AddCommGroup TestCore] [Module ℂ TestCore]
    (rows : PhysicalManifoldRowSources.Data m) (n : PhysicalManifoldNoiseSources.Data m)
    {Noise W : Type*} [TopologicalSpace Noise] [MeasurableSpace Noise]
    [OpensMeasurableSpace Noise] [SecondCountableTopology Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise : ℝ≥0 → Noise → Ω) (hnoise : ∀ ε, Continuous (noise ε))
    (j : m.StrongSpace →L[ℂ] W) (R : ℝ)
    (inputs : ActualAnnealedInputs law (fun _ => inferInstance) j R)
    (hgenerator : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    (T : M ≃ₜ M) (K G B : Set M) [CompactSpace K]
    (hK : IsCompact K) (hV : IsOpen V) (hVK : V ⊆ K) (hB : IsOpen B)
    (hcore : isolatedCore T K ⊆ B) (hBV : closure B ⊆ V)
    (hsep : (T '' closure B) ∩ forwardTrapped T K ⊆ B)
    (hF : ∀ ε, Measurable (fun z : M × Noise => m.maps (noise ε z.2) z.1))
    (close : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      ∀ x ∈ K, ∀ z, dist (m.maps (noise ε z) x) (T x) < η)
    (plaques : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Nonempty (LocalPositiveCollar.ForwardCollarPlaqueInputs T
        (fun z : M × Noise => m.maps (noise ε z.2) z.1) V K G))
    (w : K → ℝ) (hw : Continuous w) (wc : K → ℝ) (hwc : Measurable wc)
    (hwc0 : ∀ x, 0 ≤ wc x) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (hweight : ∀ x : K, m.weight x.val = wc x)
    (heq : ∀ x : K, x.val ∈ closure B → wc x = w x)
    (smoothingWindow : ℝ≥0) (smoothingWindow_positive : 0 < smoothingWindow)
    (originalSF : ∀ ε : ℝ≥0, 0 < ε → ε ≤ smoothingWindow → HasStrongFellerKernel (RestrictedNoise.chain (law ε)
      (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet
      w hw.measurable R hR hwR))
    (cutoffSF : ∀ ε : ℝ≥0, 0 < ε → ε ≤ smoothingWindow → HasStrongFellerKernel (RestrictedNoise.chain (law ε)
      (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet
      wc hwc R hR hwcR))
    (inverse : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Nonempty (Global.NoFullSupportCollarDensityCertificate.Inputs T V K G hK (law ε)
        (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) w hw.measurable R η))
    (Tests : Set (K →ᵇ ℝ)) (σ : Measure K) [IsFiniteMeasure σ]
    (p : PhysicalManifoldSupportedCore.CoreData (K := K) (Tests := Tests) (σ := σ)
      m.regularCore (coreLift m.qa))
    (r t sn u : ℝ) (margins : RegularCoreApproximation.RegularityMargins r t sn u)
    (hpositive : {x : K | x.val ∈ V} ⊆ σ.support)
    (hwSupport : tsupport wc ⊆ {x : K | x.val ∈ V})
    (globalPhysical : Test →L[ℂ] (K →ᵇ ℂ))
    (includeReg : Reg →L[ℂ] Test)
    (include_view : ∀ v, globalPhysical (includeReg v) = physicalRealization V K m.regularCore v)
    (qt : TestCore →ₗ[ℂ] Test) (denseTest : DenseRange qt)
    (aFull : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (haFull : Function.Injective aFull)
    (smoothFull : ∀ c d, aFull (coreLift m.qa c) (qt d) =
      ∫ x, physicalCore V K c x * globalPhysical (qt d) x ∂σ)
    (smoothRestriction : ∀ c d, aFull (coreLift m.qa c) (includeReg (m.regularCore d)) =
      p.embedding (coreLift m.qa c) (m.regularCore d))
    (essential : EssentialRadiusContract (E := m.StrongSpace) (W := W))
    (injectivej : Function.Injective j) (compactj : IsCompactOperator j)
    {det : DeterministicLeading (inputs.operator 0)} {q δ : ℝ}
    (o : ProjectorOutputs inputs.operator (TwoNormNormalization.weakEmbedding j) det q δ)
    (hδsub : δ < q - det.subordinate) (hδlead : δ < det.rate - q) (hq : 0 < q)
    (hprincipal : inputs.principal / R < q)
    (conjugation : ∀ ε, RealOperatorConjugation (inputs.operator ε))
    (testView : Test →ₗ[ℂ] (M → ℂ)) (testView_injective : Function.Injective testView)
    (physical_eq : ∀ v x, globalPhysical v x = testView v x.val)
    (H : ℝ≥0 → Noise → M → M) (weight : ℝ≥0 → M × Noise → ℝ)
    (inverseWindow : ℝ≥0) (inverseWindow_positive : 0 < inverseWindow)
    (inverseOrdinary : ∀ ε, 0 < ε → ε ≤ inverseWindow → InverseRegularTransfer.OrdinarySources testView (H ε) (weight ε))
    (inverse_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : Noise × M => H ε z.1 z.2))
    (inverse_weight_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : Noise × M => weight ε (z.2, z.1)))
    (test_core_continuous : ∀ c, Continuous (testView (qt c)))
    (inverseExponent : ℝ) (inverseExponent_positive : 0 < inverseExponent)
    (inverseInterpolationConstant : ℝ≥0 → TestCore → Noise → ℝ)
    (inverseInterpolation : ∀ ε (hp : 0 < ε) (hw : ε ≤ inverseWindow) c a₀ a e, 0 ≤ e →
      (∀ x, ‖testView ((inverseOrdinary ε hp hw).operator testView_injective a (qt c)) x -
        testView ((inverseOrdinary ε hp hw).operator testView_injective a₀ (qt c)) x‖ ≤ e) →
      dist ((inverseOrdinary ε hp hw).operator testView_injective a (qt c))
        ((inverseOrdinary ε hp hw).operator testView_injective a₀ (qt c)) ≤
          inverseInterpolationConstant ε c a₀ * e ^ inverseExponent)
    (jacobian : ∀ ε, 0 < ε → ε ≤ inverseWindow → ∀ z (f : K →ᵇ ℂ) v,
      (∫ x, ActualCutoffAdjoint.raw K
        (fun y : M × Noise => m.maps (noise ε y.2) y.1) wc z f x * testView v x.val ∂σ) =
        ∫ x, f x * ((weight ε (x.val, z) : ℂ) * testView v (H ε z x.val)) ∂σ)
    (ultra : StrongFellerSquareCompact.UltraFellerContract (X := K))
    (fredholm : PowerCompactGap.SquareCompactFredholm (F := K →ᵇ ℂ))
    (riesz : PowerCompactRealLeadingPair.ClassicalContract (X := K))
    (classical : CommonAmbientClassicalComparison.ClassicalContract (A := m.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K m.regularCore))
      (Z := Test →L[ℂ] ℂ) (Reg := Reg) (W := W)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Nonempty (Global.NoFullSupportKLFamily.ScaleSources (Z := Reg →L[ℂ] ℂ) (Zret := (RetainedRegularTests.space (⟨B, hB⟩ : TopologicalSpace.Opens M) V
        m.regularCore (subset_closure.trans hBV) →L[ℂ] ℂ)) (Core := Reg)
        T V K G hK (law ε) (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε)
        w hw wc hwc R hR hwR hwcR o ε η Tests
        (fun t => ConstructedRegularMultipliers.analyticMultiplier (coreLift m.qa)
          (SmoothSupportedManifoldCore.multiplier V (p.test t) (p.test_smooth t)))) := by
  have hypothesesExistence := exists_hypotheses_of_varying_noise_classical_radius
    essential law (fun _ => inferInstance) inputs.generator inputs.measurable j injectivej compactj
    inputs.window inputs.window_pos inputs.blockLength inputs.blockLength_pos
    inputs.principal inputs.weakRate inputs.weakOneStep inputs.operatorBound inputs.remainder R
    inputs.principal_pos inputs.principal_weak inputs.weakOneStep_nonneg inputs.weakOneStep_rate
    inputs.operatorBound_nonneg inputs.remainder_nonneg inputs.scale_ge_one inputs.principal_scale
    inputs.generator_bound inputs.weak_bound inputs.block_bound inputs.perturbation
  let h := Classical.choose hypothesesExistence
  have hα := (Classical.choose_spec hypothesesExistence).1
  have hcutoff : h.alpha < q := hα.symm ▸ hprincipal
  let openB : TopologicalSpace.Opens M := ⟨B, hB⟩
  let physical := physicalRealization V K m.regularCore
  have physical_core : ∀ c, physical (m.regularCore c) = physicalCore V K c :=
    physicalRealization_core V K m.regularCore m.regularCore_dense p.uniformConstant p.uniformBound
  let restriction := RetainedRegularTests.restriction openB V m.regularCore (subset_closure.trans hBV)
  let retained := RetainedRegularTests.closedRetainedEmbedding openB V K m.regularCore
    (subset_closure.trans hBV) (hBV.trans hVK) physical σ
  have hretained : Function.Injective retained :=
    RetainedRegularTests.closedRetainedEmbedding_injective openB V K m.regularCore
      (subset_closure.trans hBV) (hBV.trans hVK) physical σ physical_core
      (fun x hx => hpositive ((subset_closure.trans hBV) hx))
  have restriction_identity : restriction.comp (SupportedRegularPairing.embedding σ physical) =
      retained.comp (Restriction.restrictObservable (Restriction.retainedRegion K B)) :=
    RetainedRegularTests.closed_pairing_restriction openB V K m.regularCore
      (subset_closure.trans hBV) (hBV.trans hVK) physical σ physical_core
  have geometricExistence := exists_uniform_same_cutoff_sources
    (E := m.StrongSpace) (W := W) (Z := Reg →L[ℂ] ℂ) (Zret := (RetainedRegularTests.space (⟨B, hB⟩ : TopologicalSpace.Opens M) V
        m.regularCore (subset_closure.trans hBV) →L[ℂ] ℂ)) (Ω := Noise) (P := inputs.operator) (i := TwoNormNormalization.weakEmbedding j)
    (d := det) (q := q) (δ := δ)
    T K B hK hB hcore (hBV.trans hVK) hsep
  let ηg := Classical.choose geometricExistence
  have hηg := (Classical.choose_spec geometricExistence).1
  have geometric := (Classical.choose_spec geometricExistence).2
  intro η hη
  filter_upwards [self_mem_nhdsWithin,
    (((gt_mem_nhds smoothingWindow_positive) : {ε : ℝ≥0 | ε < smoothingWindow} ∈ 𝓝 0).mono (fun _ he => he.le)).filter_mono nhdsWithin_le_nhds, close η hη, close ηg hηg, plaques, inverse η hη,
    (((gt_mem_nhds h.window_pos) : {ε : ℝ≥0 | ε < h.window} ∈ 𝓝 0).mono (fun _ he => he.le)).filter_mono nhdsWithin_le_nhds,
    (((gt_mem_nhds inverseWindow_positive) : {ε : ℝ≥0 | ε < inverseWindow} ∈ 𝓝 0).mono (fun _ he => he.le)).filter_mono nhdsWithin_le_nhds,
    (((gt_mem_nhds o.window_pos) : {ε : ℝ≥0 | ε < o.window} ∈ 𝓝 0).mono (fun _ he => he.le)).filter_mono nhdsWithin_le_nhds] with ε hε hsmooth hc hcg hp hin he hiw ho
  let C := RestrictedNoise.chain (law ε)
    (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet w hw.measurable R hR hwR
  let D := RestrictedNoise.chain (law ε)
    (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK.measurableSet wc hwc R hR hwcR
  let J := (inverseOrdinary ε hε hiw).operator testView_injective
  have inverseCoreMeasurable (c : TestCore) : AEStronglyMeasurable
      (fun z => J z (qt c)) (law ε) :=
    (InverseRegularTransfer.continuous_operator_core testView_injective (inverseOrdinary ε hε hiw)
      qt (inverse_joint ε hε hiw) (inverse_weight_joint ε hε hiw) test_core_continuous
      inverseExponent inverseExponent_positive (inverseInterpolationConstant ε)
      (inverseInterpolation ε hε hiw) c).aestronglyMeasurable
  have measJ := InverseRegularTransfer.operator_aestronglyMeasurable testView_injective
    (inverseOrdinary ε hε hiw) (law ε) qt denseTest inverseCoreMeasurable
  have cv := InverseRegularTransfer.changeVariables_of_jacobian testView_injective
    (inverseOrdinary ε hε hiw) K (fun z : M × Noise => m.maps (noise ε z.2) z.1) wc σ
    globalPhysical physical_eq (jacobian ε hε hiw)
  have facts := PhysicalManifoldCommonCoreComparison.common_core_facts m rows n law noise hnoise j R inputs
    hgenerator K p.uniformConstant p.uniformBound hVK hK.measurableSet ε (hF ε) wc hwc hwc0
    hR hwcR hweight (cutoffSF ε hε hsmooth) hK.isClosed hV hwSupport σ hpositive globalPhysical includeReg
    include_view qt denseTest aFull haFull smoothFull p.embedding smoothRestriction h compactj he J
    measJ (inverseOrdinary ε hε hiw).bound ((inverseOrdinary ε hε hiw).operator_norm_le testView_injective) cv q hcutoff ultra classical
  let comparison := ClassicalSameCutoffComparisons.ofCommonCoreFacts
    (Z := Reg →L[ℂ] ℂ)
    (Zret := RetainedRegularTests.space openB V m.regularCore (subset_closure.trans hBV) →L[ℂ] ℂ) o hδlead hq ε ho
    (conjugation ε) D (cutoffSF ε hε hsmooth) R hR (Restriction.retainedRegion K B) p.embedding
    (SupportedRegularPairing.embedding σ physical) restriction retained
    hretained restriction_identity facts ultra fredholm riesz
  have sameExistence := geometric (law ε)
    (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) hcg w wc hw.measurable hwc R hR
    hwR hwcR heq (originalSF ε hε hsmooth) (cutoffSF ε hε hsmooth) o ε comparison
  let same := Classical.choice sameExistence
  let plaque := Classical.choice hp
  let hinv := Classical.choice hin
  refine ⟨{
    close := hc
    plaques := plaque
    originalSF := originalSF ε hε hsmooth
    cutoffSF := cutoffSF ε hε hsmooth
    sameCutoff := same
    inverse := hinv
    core := ?_ }⟩
  intro dc μcut _ hμ
  have supported := PhysicalManifoldSupportedCore.Data.source
    (Noise := Noise) (W := W)
    (Zret := RetainedRegularTests.space openB V m.regularCore (subset_closure.trans hBV) →L[ℂ] ℂ)
    m K Tests σ p rows n law noise hnoise j R inputs
    hgenerator o hδsub hδlead hq ε C
    (RestrictedNoise.chain (law ε) (fun z : M × Noise => m.maps (noise ε z.2) z.1)
      (hF ε) K hK.measurableSet wc hwc R hR hwcR) (originalSF ε hε hsmooth) (cutoffSF ε hε hsmooth) hR same dc μcut hμ hVK
    hK.isClosed hV hpositive (hF ε) wc hwc hwc0 hwcR hweight rfl hwSupport
    r t sn u margins
  rw [← PhysicalManifoldModel.Data.scalar_normalization m (((o.eigenvalue ε).re : ℂ)⁻¹)
    (inputs.operator ε)] at supported
  rw [← genericScalar_eq (((o.eigenvalue ε).re : ℂ)⁻¹) (inputs.operator ε)]
  exact ⟨supported⟩

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldNoFullSupportScaleSources
