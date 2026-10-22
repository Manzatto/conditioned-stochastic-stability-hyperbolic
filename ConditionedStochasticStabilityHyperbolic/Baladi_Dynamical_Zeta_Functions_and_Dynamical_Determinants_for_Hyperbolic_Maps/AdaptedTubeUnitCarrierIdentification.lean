module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierMultiplier
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeProductIdentification
public import LeanShared.Geometry.ManifoldSmoothHolderCoreBounds
meta import Lean.LibrarySuggestions.Basic

/-! The equilibrium identification on the adapted tube carrier. On the same carrier data as the
leading record, any deterministic leading record at the pressure rate `e^P` has spectral product
`Re m(M_ψ v) = ∫ ψ dη` for every smooth real `ψ`, where `η` is the unique equilibrium state of
the weight's potential on the basic set. The regular-core multiplier bound comes from the smooth
Hölder core and the strong one from the unit carrier. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierIdentification"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierIdentification
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AllFakeLeafModel AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open LinearRechartedManifold HyperbolicLinearRechart FractionalManifoldRegularity ThermodynamicDefinitions
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
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

set_option maxHeartbeats 4000000 in
/-- The regular-core bound of the literal multiplier by a smooth real function. -/
theorem carrier_regular_bound :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∀ (ψ : M → ℝ) (hψ : ContMDiff (𝓘(ℝ, system.EuclideanModel)) 𝓘(ℝ) ∞ ψ),
      ∃ CR : ℝ, ∀ c, ‖(carrier).regularCore (PhysicalModelHorizonIdentities.coreMultiplier ψ hψ c)‖ ≤
        CR * ‖(carrier).regularCore c‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  intro ψ hψ
  exact ManifoldSmoothHolderCore.smooth_multiplier_bound
    (fun j => atlas.normalizedTubeChart j) (localization atlas d) (tubeChart_mem atlas) openV hb hb1
    region (fun x => (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)

set_option maxHeartbeats 4000000 in
/-- The strong-core bound of the literal multiplier by a smooth real function. -/
theorem carrier_analytic_bound (h1 : ∀ σ s, exponent σ - 1 - exponent s < 0)
    (h2 : ∀ s, -1 - exponent s < 0) (h3 : ∀ σ, exponent σ ≤ 1) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∀ (ψ : M → ℝ) (hψ : ContMDiff (𝓘(ℝ, system.EuclideanModel)) 𝓘(ℝ) ∞ ψ),
      ∃ CA : ℝ, ∀ c, ‖DyadicCompletion.coreLift (carrier).qa
        (PhysicalModelHorizonIdentities.coreMultiplier ψ hψ c)‖ ≤
        CA * ‖DyadicCompletion.coreLift (carrier).qa c‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  intro ψ hψ
  have ex := AdaptedTubeUnitCarrierMultiplier.analyticMultiplier atlas d μE
    openV region hb hb1 F hr regularT hT hbq hg support positiveStable radial angle exponent margin
    lossH lossW hH hW η cap h1 h2 h3 (fun x => (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)
  exact ⟨Classical.choose ex, (Classical.choose_spec ex).2⟩

set_option maxHeartbeats 8000000 in
/-- On the carrier, the spectral product of any leading record at rate `e^P` is the integral against
the unique equilibrium state of `g`. -/
theorem carrier_identification (h1 : ∀ σ s, exponent σ - 1 - exponent s < 0)
    (h2 : ∀ s, -1 - exponent s < 0) (h3 : ∀ σ, exponent σ ≤ 1)
    (ht : ∀ s, 0 < 1 + exponent s)
    (backward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (T.symm : M → M)) (hr1 : 1 < r)
    (inverseRegular : Regular (E := E) (F := E) r T.symm) (mixing : MixingOn T Λ)
    (weightNonneg : ∀ x, 0 ≤ g x) (weightPos : ∀ x ∈ Λ, 0 < g x)
    (forwardSupport : (T : M → M) '' tsupport g ⊆ V) (withinV : closure V ⊆ V₀)
    (P0 : ℝ) (hP0 : pressure T (base.hyperbolic.potential g) Λ = (P0 : EReal))
    (state : ProbabilityMeasure M)
    (equilibrium : IsEquilibriumState T (base.hyperbolic.potential g) Λ state)
    (unique : ∀ μ, IsEquilibriumState T (base.hyperbolic.potential g) Λ μ → μ = state) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∀ (a : _) (_hTa : (carrier).maps a = T) {L : ℝ}
      (_bound : PhysicalModelAnalytic.AnalyticBound (carrier) L)
      (dl : PhysicalModelHorizonIdentities.LeadingRecord (carrier) a)
      (_hrate : dl.rate = Real.exp P0)
      (ψ : M → ℝ) (hψ : ContMDiff (𝓘(ℝ, system.EuclideanModel)) 𝓘(ℝ) ∞ ψ),
      PhysicalModelHorizonIdentities.productValue (carrier) dl ψ hψ =
        ∫ x, ψ x ∂(state : Measure M) := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  intro a hTa L bound dl hrate ψ hψ
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let _ : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, system.EuclideanModel)) x) :=
    ⟨transportMetric atlas.originalModelEquiv original⟩
  let _ := continuous_metric (M := M) atlas.originalModelEquiv
  have coreV : Λ ⊆ V := fun x hx => support (subset_tsupport _ (weightPos x hx).ne')
  let transported := transportBasic atlas.originalModelEquiv base (hT.mdifferentiable one_ne_zero)
    (backward.mdifferentiable one_ne_zero)
  let bd := transported.restrictNeighborhood V openV coreV (fun x hx => withinV (subset_closure hx))
  have samePotential : bd.hyperbolic.potential g = base.hyperbolic.potential g :=
    basic_potential_eq atlas.originalModelEquiv base (hT.mdifferentiable one_ne_zero)
      (backward.mdifferentiable one_ne_zero) g
  have lowered : Regular (E := E) (F := ℝ) b g := by
    have := hg.lower_noninteger (n := 0) hb hb1 (by simpa using hbq)
    simpa using this
  let refData : FiniteSmoothReferenceCharts.Data (E := system.EuclideanModel) (M := M) :=
    Classical.choice FiniteSmoothReferenceCharts.exists_data
  have localBound := AdaptedTubeUnitCarrierPairing.localPairing atlas d μE openV region hb hb1 F hr
    regularT hT hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW η cap
    one_pos le_rfl ht
  have equilibrium' : IsEquilibriumState T (bd.hyperbolic.potential g) Λ state :=
    samePotential ▸ equilibrium
  have unique' : ∀ μ, IsEquilibriumState T (bd.hyperbolic.potential g) Λ μ → μ = state :=
    samePotential ▸ unique
  have pressure' : pressure T (bd.hyperbolic.potential g) Λ = (P0 : EReal) :=
    samePotential ▸ hP0
  have mapCont : Continuous ((carrier).maps a) := hTa ▸ T.continuous
  have forward' : (carrier).maps a '' tsupport (carrier).weight ⊆ V := hTa ▸ forwardSupport
  have seedEx := PhysicalModelLeadingInputs.seed_exists (carrier) a mapCont openV forward'
  let seed := Classical.choose seedEx
  have hseed := Classical.choose_spec seedEx
  have regularEx := carrier_regular_bound atlas d μE openV region hb hb1 F hr regularT
    hT hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW η cap ψ hψ
  let CR := Classical.choose regularEx
  have regularBound := Classical.choose_spec regularEx
  have analyticEx := carrier_analytic_bound atlas d μE openV region hb hb1 F hr
    regularT hT hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW η cap
    h1 h2 h3 ψ hψ
  let CA := Classical.choose analyticEx
  have analyticBound := Classical.choose_spec analyticEx
  exact PhysicalModelHorizonIdentities.native_product_identification (carrier) refData localBound
    (ManifoldSmoothHolderCore.physical (fun j => atlas.normalizedTubeChart j) (localization atlas d)
      openV hb hb1) (fun _ _ => rfl) ψ hψ CR CA regularBound
    analyticBound bound a seed hseed mapCont (hg.differentiable.continuous) weightNonneg dl P0 hrate
    bd hTa.symm (contMDiff_one_rechart atlas.originalModelEquiv hT)
    (contMDiff_one_rechart atlas.originalModelEquiv backward) hr1 hb
    (regularT.linearRechart atlas.originalModelEquiv)
    (inverseRegular.linearRechart atlas.originalModelEquiv) mixing
    (lowered.scalarLinearRechart atlas.originalModelEquiv) weightPos
    (fun x hx => subset_closure (support (subset_tsupport _ hx)))
    pressure' state equilibrium' unique'

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierIdentification
