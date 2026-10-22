module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierComplete
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNativePacketSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierPairing
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierMultiplier
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestDistribution
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeCorePacket
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNativeLayerSources
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalComputedLayerClassicalInputs
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseNativeTestActionInputs
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImageRepresentation
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImageClipped
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalControlSubmersionSources
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProvedCommonAmbientComparison
public import LeanShared.Geometry.NativeFullTestPhysical
public import LeanShared.Geometry.ManifoldSmoothHolderCoreBounds
public import LeanShared.Geometry.FractionalLinearRechartRegularity
public import LeanShared.Geometry.FractionalScalarLinearRechart
public import LeanShared.Dynamics.HyperbolicLinearRechartPotential
public import LeanShared.Dynamics.HyperbolicLinearRechartPeriodic
meta import Lean.LibrarySuggestions.Basic

/-! The physical source packet of the adapted tube carrier (local stability). On a compact live
collar `K ⊇ V` with isolated core `Λ`, a positive collar `G` and a separating retained collar
`B`, the carrier with weight `g` (equal to the physical weight `w` on `closure B`) produces, for
every actual annealed record of its literal noise and every projector output, the eventual
no-full-support scale sources. The order-`b` native full tests, their distribution, the regular
inclusion, the supported-core packet and the ordinary layer record (plaques, densities, inverse
actions, Jacobians) are all constructed here; nothing besides geometry and weights is assumed.
-/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierPhysicalSources"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open Set IsManifold MeasureTheory Bundle Filter
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierPhysicalSources
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AllFakeLeafModel AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open LinearRechartedManifold HyperbolicLinearRechart FractionalManifoldRegularity
open KellerLiverani1999 Paper.RegularNoise
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V₀ : Set M} {base : BasicData (E := E) T Λ V₀}
  {system : PatchSystem base}
  (atlas : ChartAtlas system) {radius : ℝ} {tubes : Finset atlas.NormalizedTubeIndex}
  (d : FiniteSmoothCapturePartition.Data (E := E) Λ
    (fun i : tubes => atlas.normalizedTube radius i.val))
  (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
  {V : Set M} (openV : IsOpen V) (region : V ⊆ d.capture)
  {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  {r : ℝ} (F : Paper.RegularNoise.Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
  (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
  (hT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
  {g : M → ℝ} {q : ℝ} (hbq : b < q)
  (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
  (support : tsupport g ⊆ V)
  (positiveStable : 0 < system.framing.stableDimension)
  (radial : ConeDyadicSymbols.RadialCutoff)
  (angle : ConeDyadicSymbols.AngularCutoff
    (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (ProjectionConeTransversality.cone system.euclideanSecondProjection
      (OneStepConePolarization.minusOpening system.rate)))
  (exponent : Bool → ℝ) (margin : ∀ a, exponent a ≤ b)
  (lossH lossW : ℝ) (hH : 0 < lossH) (hW : 0 < lossW)
  (η : NNReal) (cap : η ≤ (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).window)

local notation "carrier" => model atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
  positiveStable radial angle exponent margin lossH lossW hH hW η cap

set_option maxHeartbeats 2000000 in
/-- The eventual physical scale sources of the carrier for any actual annealed record of its
literal noise. -/
theorem carrier_sources (h1 : ∀ σ s, exponent σ - 1 - exponent s < 0)
    (h2 : ∀ s, -1 - exponent s < 0) (h3 : ∀ σ, exponent σ ≤ 1)
    (htb : ∀ s, 0 < b + exponent s)
    (backward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (T.symm : M → M))
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hba : b < a) (haq : a < q) (lowerA : a + 1 < r)
    (capHigh : η ≤ (bounds atlas d μE openV region ha ha1 F hr regularT hT haq hg support).window)
    (positiveη : 0 < η) (L : Laws (ι := ι))
    (K : Set M) [CompactSpace K] (hK : IsCompact K)
    (hcoreK : LeanShared.isolatedCore T K = Λ) (hVK : V ⊆ K) (coreV : Λ ⊆ V)
    (G B : Set M) (openG : IsOpen G) (coreG : Λ ⊆ G) (openB : IsOpen B) (coreB : Λ ⊆ B)
    (hBV : closure B ⊆ V) (noReturn : (T '' closure B) ∩ LeanShared.forwardTrapped T K ⊆ B)
    (wg : M → ℝ) (hwg : Continuous wg) (wgNonneg : ∀ x, 0 ≤ wg x)
    (wgPos : ∀ x ∈ closure G, 0 < wg (T.symm x))
    (hgc : Continuous g) (gNonneg : ∀ x, 0 ≤ g x) (agree : ∀ x ∈ closure B, g x = wg x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, wg x ≤ R) (hgR : ∀ x, g x ≤ R) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    letI : NormedAddCommGroup (carrier).StrongSpace := (carrier).strongNormedParent;
    letI : SeminormedAddCommGroup (carrier).StrongSpace := (carrier).strongSeminormedParent;
    letI : NormedSpace ℂ (carrier).StrongSpace := (carrier).strongScalarParent;
    letI : UniformSpace (carrier).StrongSpace := (carrier).strongCarrierUniform;
    letI : CompleteSpace (carrier).StrongSpace := (carrier).strongCarrierComplete;
    ∀ (hF : ∀ ε, Measurable (fun z : M × FixedControl (ι := ι) =>
        (carrier).maps (MapImage.clipped (maps atlas F regularT) hr η
          (cap.trans (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).below)
          ε z.2) z.1))
      {Lrows : ℝ} (_analytic : PhysicalModelAnalytic.AnalyticBound (carrier) Lrows)
      {W : Type*} {_iW : NormedAddCommGroup W} {_sW : NormedSpace ℂ W} [CompleteSpace W]
      (j : (carrier).StrongSpace →L[ℂ] W)
      (inputs : ActualAnnealedInputs L.fixedLaw (fun _ => inferInstance) j R)
      (_hgenerator : ∀ ε z, inputs.generator ε z = (carrier).generator
        (MapImage.clipped (maps atlas F regularT) hr η
          (cap.trans (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).below)
          ε z))
      (_injectivej : Function.Injective j) (_compactj : IsCompactOperator j)
      {det : DeterministicLeading (inputs.operator 0)} {q' δ : ℝ}
      (o : ProjectorOutputs inputs.operator (TwoNormNormalization.weakEmbedding j) det q' δ)
      (_hδsub : δ < q' - det.subordinate) (_hδlead : δ < det.rate - q') (_hq : 0 < q')
      (_hprincipal : inputs.principal / R < q')
      (_conjugation : ∀ ε, RealOperatorConjugation (inputs.operator ε)),
    ∀ ζ : ℝ, 0 < ζ → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Nonempty (Global.NoFullSupportKLFamily.ScaleSources
        (Z := ConstructedHolderPhysicalModel.Regular (fun j => atlas.normalizedTubeChart j)
          (localization atlas d) openV hb hb1 →L[ℂ] ℂ)
        (Zret := (RetainedRegularTests.space (⟨B, openB⟩ : TopologicalSpace.Opens M) V
          (carrier).regularCore (subset_closure.trans hBV) →L[ℂ] ℂ))
        (Core := ConstructedHolderPhysicalModel.Regular (fun j => atlas.normalizedTubeChart j)
          (localization atlas d) openV hb hb1)
        T V K G hK (L.fixedLaw ε)
        (fun z : M × FixedControl (ι := ι) => (carrier).maps (MapImage.clipped (maps atlas F regularT)
          hr η (cap.trans (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).below)
          ε z.2) z.1) (hF ε)
        (fun x : K => wg x.val) (hwg.comp continuous_subtype_val)
        (fun x : K => g x.val) (hgc.comp continuous_subtype_val).measurable
        R hR (fun x => hwR x.val) (fun x => hgR x.val) o ε ζ
        (SmoothPhysicalTests.tests (E := system.EuclideanModel) K)
        (fun t => ConstructedRegularMultipliers.analyticMultiplier (DyadicCompletion.coreLift (carrier).qa)
          (SmoothSupportedManifoldCore.multiplier V (SmoothPhysicalTests.complexExtension K t)
            (SmoothPhysicalTests.complexExtension_smooth K t)))) := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  letI : NormedAddCommGroup (carrier).StrongSpace := (carrier).strongNormedParent
  letI : SeminormedAddCommGroup (carrier).StrongSpace := (carrier).strongSeminormedParent
  letI : NormedSpace ℂ (carrier).StrongSpace := (carrier).strongScalarParent
  letI : UniformSpace (carrier).StrongSpace := (carrier).strongCarrierUniform
  letI : CompleteSpace (carrier).StrongSpace := (carrier).strongCarrierComplete
  intro hF Lrows analytic W _ _ _ j inputs hgenerator injectivej compactj det q' δ o hδsub hδlead hq
    hprincipal conjugation
  have _inverseRegular := inverseRegular
  letI : NormedSpace ℝ system.EuclideanModel :=
    (inferInstance : InnerProductSpace ℝ system.EuclideanModel).toNormedSpace
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let _ : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, system.EuclideanModel)) x) :=
    ⟨transportMetric atlas.originalModelEquiv original⟩
  let _ := continuous_metric (M := M) atlas.originalModelEquiv
  have forwardR := smoothT atlas hT
  have backwardR := contMDiff_one_rechart atlas.originalModelEquiv backward
  have regularTR := regularT.linearRechart atlas.originalModelEquiv
  have hgR' := hg.scalarLinearRechart atlas.originalModelEquiv
  let transported := transportBasic atlas.originalModelEquiv base (hT.mdifferentiable one_ne_zero)
    (backward.mdifferentiable one_ne_zero)
  have hw := cap.trans (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).below
  let rep := MapImage.representation (maps atlas F regularT) hr η hw positiveη
  let x₀ : M := Classical.choose base.nonempty
  let J := (maps atlas F regularT).inverseFamily hr forwardR (backwardR.mdifferentiable one_ne_zero) x₀
  have r1 : 1 < r := by linarith
  -- The ordinary inverse test action on the native order-`b` tests.
  let action := Classical.choice (J.native_testActionInputs FiniteSmoothReferenceCharts.canonicalData volume hb hba
    ha ha1 lowerA regularTR backwardR g q haq hgR')
  let view := NativeFullHolderTests.view (E := system.EuclideanModel) (M := M) b hb1.le
  have viewInj := NativeFullHolderTests.view_injective (E := system.EuclideanModel) (M := M) b hb1.le
  let qt := NativeFullHolderTests.core (E := system.EuclideanModel) (M := M) b hb1.le
  -- The ordinary layer record.
  have coreSub : LeanShared.isolatedCore T K ⊆ Λ := hcoreK.subset
  let classical := Paper.RegularLayerClassicalInputs.TestActionInputs.classicalInputs rep hK volume wg hwg
    (fun x _ => wgNonneg x) wgPos g hgc (fun x hx => hVK (support (subset_tsupport _ hx))) gNonneg R hR
    view viewInj qt J action hr forwardR backwardR transported coreSub openV hVK coreV openG coreG
  let geo := Paper.RegularLayerClassicalInputs.ClassicalInputs.withGeometry rep
    (FiniteSmoothReferenceCharts.referenceMeasure (M := M) volume) V K G hK (fun x => wg x.val)
    (fun x => g x.val) R view viewInj qt classical B openV hVK openG (hcoreK ▸ coreG) openB
    (hcoreK ▸ coreB) hBV noReturn (fun x => wgNonneg x.val) (hgc.comp continuous_subtype_val)
    (fun x => gNonneg x.val)
    (by
      refine (closure_minimal ?_ ((isClosed_tsupport g).preimage continuous_subtype_val)).trans ?_
      · intro x hx
        exact subset_tsupport g hx
      · intro x hx
        exact support hx)
    (fun x hx => agree x.val hx)
  let layer := geo.produce (Paper.RegularNoise.canonical_controlSubmersionSources volume) L
    (hwg.comp continuous_subtype_val) (hgc.comp continuous_subtype_val).measurable hR
    (fun x => hwR x.val) (fun x => hgR x.val) hF
  -- Distribution, regular inclusion and supported-core packet on the same tests.
  have localBound := AdaptedTubeUnitCarrierPairing.localPairing atlas d μE openV region hb hb1 F hr
    regularT hT hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW η cap
    hb hb1.le htb
  let incl := ManifoldHolderQuotient.includeReg (ManifoldSmoothHolderCore.regions
    (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1 (fun i => tubeChart_mem atlas i.val)
  have incView : ∀ v x, view (incl v) x = (carrier).view v x := fun v x =>
    ManifoldHolderQuotient.view_includeReg (ManifoldSmoothHolderCore.regions (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1 (fun i => tubeChart_mem atlas i.val) v x
  have uniform := ManifoldSmoothHolderCore.uniform_bound (fun j => atlas.normalizedTubeChart j)
    (localization atlas d) (tubeChart_mem atlas) openV hb hb1 region K
  have regularBound : ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, system.EuclideanModel)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ B : ℝ, ∀ c, ‖(carrier).regularCore (SmoothSupportedManifoldCore.multiplier V ψ hψ c)‖ ≤
        B * ‖(carrier).regularCore c‖ := fun ψ hψ =>
    ManifoldSmoothHolderCore.smooth_multiplier_bound (fun j => atlas.normalizedTubeChart j)
      (localization atlas d) (tubeChart_mem atlas) openV hb hb1 region ψ hψ
  let analyticBound :=
    fun (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, system.EuclideanModel)) (𝓘(ℝ, ℂ)) ∞ ψ) =>
      (AdaptedTubeUnitCarrierMultiplier.analyticMultiplier atlas d μE openV
        region hb hb1 F hr regularT hT hbq hg support positiveStable radial angle exponent margin
        lossH lossW hH hW η cap h1 h2 h3 ψ hψ).imp (fun _ h => h.2)
  have margins : RegularCoreApproximation.RegularityMargins r (a / 2) (-(a / 2)) a :=
    ⟨r1, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  let n := AdaptedTubeUnitCarrierSources.sources atlas d μE openV region hb hb1 F hr regularT hT hbq hg
    support positiveStable radial angle exponent margin lossH lossW hH hW η cap ha ha1 hba haq capHigh
  letI : CompleteSpace (NativeFullHolderTests.Full (E := system.EuclideanModel) (M := M) b hb1.le) := inferInstance
  let weightEq := fun (x : K) => (show (carrier).weight x.val = g x.val from rfl)
  letI : NormedAddCommGroup (ManifoldHolderQuotient.Coordinates (ManifoldSmoothHolderCore.regions (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1) := inferInstance
  letI : SeminormedAddCommGroup (ManifoldHolderQuotient.Coordinates (ManifoldSmoothHolderCore.regions (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1) := (inferInstance : NormedAddCommGroup (ManifoldHolderQuotient.Coordinates (ManifoldSmoothHolderCore.regions (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1)).toSeminormedAddCommGroup
  letI : NormedSpace ℂ (ManifoldHolderQuotient.Coordinates (ManifoldSmoothHolderCore.regions (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1) := inferInstance
  letI : CompleteSpace (ManifoldHolderQuotient.Coordinates (ManifoldSmoothHolderCore.regions (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1) := inferInstance
  letI : CompleteSpace (ConstructedHolderPhysicalModel.Regular (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV hb hb1) :=
    BanachFunctionQuotient.complete (ManifoldHolderQuotient.reconstruction (ManifoldSmoothHolderCore.regions (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1)
  let alignedLayer : LayerNoiseClassicalSources.Data T V K G B hK L.fixedLaw
      (fun ε (z : M × FixedControl (ι := ι)) => (carrier).maps
        (MapImage.clipped (maps atlas F regularT) hr η hw ε z.2) z.1) hF
      (fun x : K => wg x.val) (hwg.comp continuous_subtype_val) (fun x : K => g x.val)
      (hgc.comp continuous_subtype_val).measurable R hR (fun x => hwR x.val) (fun x => hgR x.val)
      ((FiniteSmoothReferenceCharts.referenceMeasure (M := M) volume).comap Subtype.val)
      view viewInj qt := layer
  let assemble0 := PhysicalManifoldNoFullSupportScaleSourcesNative.eventual_native_sources_of_layer
    (TestCore := SmoothSupportedManifoldCore.core (E := system.EuclideanModel) (univ : Set M))
    (carrier) (FiniteSmoothReferenceCharts.canonicalData (E := system.EuclideanModel) (M := M)) b hb hb1.le localBound analytic
    n
    L.fixedLaw (MapImage.clipped (maps atlas F regularT) hr η hw)
    (MapImage.clipped_continuous (maps atlas F regularT) hr η hw) j R inputs hgenerator T K G B hK
    hF (fun x => wg x.val) (hwg.comp continuous_subtype_val) (fun x => g x.val)
    (hgc.comp continuous_subtype_val).measurable hR (fun x => hwR x.val) (fun x => hgR x.val)
    weightEq qt alignedLayer
  let assemble1 := assemble0 r (a / 2) (-(a / 2)) a margins
    incl
  let assemble2 := assemble1
    (fun v => ManifoldHolderQuotient.globalPhysical_includeReg (ManifoldSmoothHolderCore.regions (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1 (fun i => tubeChart_mem atlas i.val) K
      (carrier).regularCore (carrier).regularCore_dense _ uniform
      (fun c x => ManifoldSmoothHolderCore.physical_smooth (fun j => atlas.normalizedTubeChart j)
        (localization atlas d) (tubeChart_mem atlas) openV hb hb1 region c x) v)
    (NativeFullHolderTests.core_dense b hb1.le)
  let assemble3 := assemble2 incView _ uniform regularBound analyticBound
  let assemble4 := assemble3 injectivej compactj o hδsub hδlead hq hprincipal conjugation
  have result := assemble4
  exact result

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierPhysicalSources

