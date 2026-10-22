module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierForwardStages
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierPair
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierRecord
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierTowerH
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnnealedPairScale
meta import Lean.LibrarySuggestions.Basic

/-! For the actual physical carrier with a forward-supported weight: the analytic pair of
`Maps.adapted_carrier_pair`, built on the common setup of
`Maps.adapted_carrier_tower_stages_forward`, so that in addition `T` maps the support of the
carrier weight `χ g` into the carrier region and the closure of the region lies in the isolating
neighborhood. The cutoff is one on a separating collar, the high-order window cap is retained,
and the normalizing scale dominates a prescribed floor. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "adapted_carrier_pair_forward"

public noncomputable section
-- The section-variable linter does not finish on the final pair term.
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open AdaptedTubeUnitCarrierBounds

variable {E ι : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

set_option linter.style.haveILetI false in
set_option maxHeartbeats 3200000 in
theorem Maps.adapted_carrier_pair_forward (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
    {r α q : ℝ} (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (αq : α < q) (hr : 1 ≤ r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (atlas : ChartAtlas system) (positiveStable : 0 < system.framing.stableDimension)
    (g : M → ℝ) (weight : Continuous g) (positive : ∀ x ∈ Λ, 0 < g x)
    (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    (radial : ConeDyadicSymbols.RadialCutoff)
    (cutoffs : ConstructedEnlargedConeSymbols.Cutoffs
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (OneStepConePolarization.minusOpening system.rate)))
    {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀1 : b₀ < 1) (b₀q : b₀ < q)
    {t s δ : ℝ} (positiveT : 0 < t) (negativeS : s < 0) (positiveδ : 0 < δ) (twoδ : δ + δ < t)
    (gap : t - s + (δ + δ) < α)
    (margin : ∀ sign, BTLinkedDyadicWeights.exponent t s sign ≤ b₀)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hab : b₀ < a) (haq : a < q) (L : Laws (ι := ι))
    (K : Set M) (hK : IsCompact K) (hVK : V ⊆ K) (hcoreK : LeanShared.isolatedCore T K = Λ)
    (scaleFloor : ℝ) :
    ∃ radiusT : ℝ, ∃ tubes : Finset atlas.NormalizedTubeIndex,
    ∃ d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : tubes => atlas.normalizedTube radiusT i.val),
    ∃ W : Set M, ∃ openW : IsOpen W, ∃ region : W ⊆ d.capture,
    ∃ χ : M → ℝ,
    ∃ hχg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q (fun x => χ x * g x),
    ∃ support : tsupport (fun x => χ x * g x) ⊆ W,
    ∃ _forwardSupport : (T : M → M) '' tsupport (fun x => χ x * g x) ⊆ W,
    ∃ _withinV : closure W ⊆ V,
    ∃ _χbounds : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1, ∃ _χone : ∀ x ∈ Λ, χ x = 1,
    ∃ _collar : (∃ G Bc : Set M, IsOpen G ∧ Λ ⊆ G ∧ closure G ⊆ W ∧
      (∀ x ∈ closure G, 0 < g x ∧ 0 < g (T.symm x)) ∧ IsOpen Bc ∧ Λ ⊆ Bc ∧ closure Bc ⊆ G ∧
      (T '' closure Bc) ∩ LeanShared.forwardTrapped T K ⊆ Bc ∧ ∀ x ∈ closure Bc, χ x = 1),
    ∃ η : ℝ≥0, ∃ _positiveη : 0 < η,
    ∃ cap : η ≤ (bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support).window,
    ∃ _capHigh : η ≤ (bounds atlas d μE openW region ha ha1 F hr regularT forward haq hχg
      support).window,
    ∃ P : ℝ, ThermodynamicDefinitions.pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < Real.exp P ∧ ∃ weakRate : ℝ, Real.exp P ≤ weakRate ∧ ρ < weakRate ∧
    ∃ scale : ℝ, 1 ≤ scale ∧ ρ < scale ∧ scaleFloor ≤ scale ∧
    scale = max (max 1 (ρ + 1)) scaleFloor ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     PhysicalModelAnnealedPair.PairStatement
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ
        (add_pos positiveδ positiveδ) η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ - δ) (s - δ - δ))
        (carrierStage_margin (carrierStage_margin margin positiveδ.le) positiveδ.le)
        δ δ positiveδ positiveδ η cap)
      L.fixedLaw (fun _ => inferInstance)
      (MapImage.clipped (maps atlas F regularT) hr η
        (cap.trans (bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
          support).below))
      scale ρ ρ weakRate weakRate) ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ Smax : ℝ, ∃ R : tubes → tubes → ℝ, (∀ i j, 0 ≤ R i j) ∧ ∀ a, ∃ strong, 0 ≤ strong ∧
      strong ≤ Smax ∧ PhysicalModelUniformBounds.PairEstimate
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ
        (add_pos positiveδ positiveδ) η cap)
      ((AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ
        (add_pos positiveδ positiveδ) η cap).maps a)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ
        (add_pos positiveδ positiveδ) η cap).weight strong (fun i j => R i.val j.val)) ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ Smax : ℝ, ∃ R : tubes → tubes → ℝ, (∀ i j, 0 ≤ R i j) ∧ ∀ a, ∃ strong, 0 ≤ strong ∧
      strong ≤ Smax ∧ PhysicalModelUniformBounds.PairEstimate
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap)
      ((AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap).maps a)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap).weight strong (fun i j => R i.val j.val)) ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ L : ℝ, 0 ≤ L ∧ PhysicalModelAnalytic.AnalyticBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ
        (add_pos positiveδ positiveδ) η cap) L) ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     ∃ L : ℝ, 0 ≤ L ∧ PhysicalModelAnalytic.AnalyticBound
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap) L) := by
  choose radiusT tubes d W openW region χ hχg support forwardSupport withinV χbounds χone collar η
    positiveη cap capHigh rest
    using Maps.adapted_carrier_tower_stages_forward μE F positiveα subunitα lower αq hr regularT forward
      backward atlas positiveStable g weight positive hg radial cutoffs hb₀ hb₀1 b₀q positiveT
      negativeS positiveδ twoδ gap margin ha ha1 haq K hK hVK hcoreK
  have hA₀ := rest.1
  have hA₁ := rest.2.1
  have hA₂ := rest.2.2.1
  choose P pressureP ρ positiveρ belowP N positiveN B hB words₀ words₁ est₀ est₁ using rest.2.2.2
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  choose L₀ hL₀ bound₀ using hA₀
  choose L₁ hL₁ bound₁ using hA₁
  choose L₂ hL₂ bound₂ using hA₂
  have margin₁ := carrierStage_margin margin positiveδ.le
  have margin₂ := carrierStage_margin margin₁ positiveδ.le
  have hnormH := AdaptedTubeUnitCarrierTowerH.middle_norm atlas d μE openW region hb₀ hb₀1 F hr
    regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ (add_pos positiveδ positiveδ)
    η cap (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) margin₁ δ δ positiveδ positiveδ
    (carrierStage_lowered t s δ)
  have hnorm₀ := AdaptedTubeUnitCarrierTower.weak_norm atlas d μE openW region hb₀ hb₀1 F hr
    regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin
    (BTLinkedDyadicWeights.exponent (t - δ - δ) (s - δ - δ)) margin₂ δ (δ + δ) δ positiveδ
    (add_pos positiveδ positiveδ) positiveδ (towerStage_lowered₂ t s δ) η cap
  have hnorm₁ := AdaptedTubeUnitCarrierTower.weak_norm atlas d μE openW region hb₀ hb₀1 F hr
    regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) margin₁
    (BTLinkedDyadicWeights.exponent (t - δ - δ) (s - δ - δ)) margin₂ δ δ δ positiveδ positiveδ
    positiveδ (carrierStage_lowered (t - δ) (s - δ) δ) η cap
  have compactH₀ := AdaptedTubeUnitCarrierTowerH.inclusionH_compact atlas d μE openW region hb₀
    hb₀1 F hr regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ (add_pos positiveδ positiveδ)
    η cap
  have compactW₀ := AdaptedTubeUnitCarrierTower.inclusionW_compact atlas d μE openW region hb₀ hb₀1
    F hr regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ (add_pos positiveδ positiveδ)
    η cap
  have compactW₁ := AdaptedTubeUnitCarrierTower.inclusionW_compact atlas d μE openW region hb₀ hb₀1
    F hr regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) margin₁ δ δ positiveδ positiveδ η cap
  have srcM₀ := AdaptedTubeUnitCarrierSources.sources atlas d μE openW region hb₀ hb₀1 F hr
    regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ (add_pos positiveδ positiveδ)
    η cap ha ha1 hab haq capHigh
  have srcM₁ := AdaptedTubeUnitCarrierSources.sources atlas d μE openW region hb₀ hb₀1 F hr
    regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) margin₁ δ δ positiveδ positiveδ η cap ha
    ha1 hab haq capHigh
  have srcM₂ := AdaptedTubeUnitCarrierSources.sources atlas d μE openW region hb₀ hb₀1 F hr
    regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent (t - δ - δ) (s - δ - δ)) margin₂ δ δ positiveδ positiveδ η
    cap ha ha1 hab haq capHigh
  have hw := cap.trans (bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
    support).below
  have rates := carrierPair_rates ρ L₂ P
  exact ⟨radiusT, tubes, d, W, openW, region, χ, hχg, support, forwardSupport, withinV, χbounds,
    χone, collar, η, positiveη, cap, capHigh, P, pressureP,
    ρ, positiveρ, belowP, max L₂ (max ρ (Real.exp P)) + 1, rates.2.2.1, rates.1,
    max (max 1 (ρ + 1)) scaleFloor, le_max_of_le_left rates.2.2.2.1,
    lt_of_lt_of_le rates.2.2.2.2 (le_max_left _ _), le_max_right _ _, rfl,
    PhysicalModelAnnealedPair.pairStatement_of_words_scale
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ
      (add_pos positiveδ positiveδ) η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) margin₁ δ δ
      positiveδ positiveδ η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent (t - δ - δ) (s - δ - δ)) margin₂ δ δ
      positiveδ positiveδ η cap)
      L.fixedLaw (fun _ => inferInstance) (MapImage.clipped (maps atlas F regularT) hr η hw)
      hnormH hnorm₀ hnorm₁ compactH₀ compactW₀ compactW₁ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl hL₀ hL₁ hL₂ bound₀ bound₁ bound₂ srcM₀ srcM₁ srcM₂
      (MapImage.reference (maps atlas F regularT) hr η hw)
      (MapImage.clipped_zero (maps atlas F regularT) hr η hw)
      (MapImage.clipped_continuous (maps atlas F regularT) hr η hw)
      (MapImage.clipped_tendsto (maps atlas F regularT) hr η hw) η positiveη N positiveN ρ B
      (Real.exp P) positiveρ hB (fun ε : ℝ≥0 => cube (ι := ι) ε)
      (fun ε hp hl c => letter atlas d hb₀ hb₀1 μE openW region F hr regularT forward b₀q
        hχg support η cap ε hp hl c) (fun ε hp z => NoiseCubeRescaling.rescale (ε : ℝ) hp z)
      ⟨0, MapImage.zero_mem_cube η⟩
      (fun ε hp hl z => MapImage.clipped_pos (maps atlas F regularT) hr η hw hp hl z)
      (fun z => (MapImage.clipped_zero (maps atlas F regularT) hr η hw z).trans
        (MapImage.reference_eq_noise (maps atlas F regularT) hr η hw positiveη)) words₀ words₁
      (max (max 1 (ρ + 1)) scaleFloor) (le_max_of_le_left rates.2.2.2.1)
      (lt_of_lt_of_le rates.2.2.2.2 (le_max_left _ _)),
    est₀, est₁, ⟨L₀, hL₀, bound₀⟩, ⟨L₁, hL₁, bound₁⟩⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
