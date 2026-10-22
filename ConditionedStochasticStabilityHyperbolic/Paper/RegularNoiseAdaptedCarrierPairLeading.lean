module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierForwardPair
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelPairLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelPairNativeIdentification
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierIdentification
public import LeanShared.Dynamics.PressureRestriction
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierRecord
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierTowerH
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnnealedPair
meta import Lean.LibrarySuggestions.Basic

/-! The deterministic leading records of the actual carrier pair. The forward-supported pair of
`Maps.adapted_carrier_pair_forward` has, for both strong stages, the leading record of the
deterministic generator at the pressure rate `e^P`, hence leading records of the normalized
zero-noise operators at rate `e^P / scale`. For the unique equilibrium state of `g`, the
consumer ratio of these records against the strong multiplier by a smooth `ψ` on the
intermediate stage is `∫ ψ`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "adapted_carrier_pair_leading"

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
  [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

/-- The commutator and pairing exponent conditions of a linked carrier stage. -/
theorem carrierExponent_conditions {t s : ℝ} (ht : 0 < t) (hs : s < 0) (hts : t - s < 1) :
    (∀ σ s', BTLinkedDyadicWeights.exponent t s σ - 1 - BTLinkedDyadicWeights.exponent t s s' < 0) ∧
    (∀ s', -1 - BTLinkedDyadicWeights.exponent t s s' < 0) ∧
    (∀ σ, BTLinkedDyadicWeights.exponent t s σ ≤ 1) ∧
    (∀ s', 0 < 1 + BTLinkedDyadicWeights.exponent t s s') := by
  refine ⟨fun σ s' => ?_, fun s' => ?_, fun σ => ?_, fun s' => ?_⟩
  · cases σ <;> cases s' <;> simp only [BTLinkedDyadicWeights.exponent] <;> linarith
  · cases s' <;> simp only [BTLinkedDyadicWeights.exponent] <;> linarith
  · cases σ <;> simp only [BTLinkedDyadicWeights.exponent] <;> linarith
  · cases s' <;> simp only [BTLinkedDyadicWeights.exponent] <;> linarith

set_option maxHeartbeats 40000000 in
theorem Maps.adapted_carrier_pair_leading (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
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
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (mixing : HyperbolicBasicSet.MixingOn T Λ) (gNonneg : ∀ x, 0 ≤ g x)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hab : b₀ < a) (haq : a < q) (L : Laws (ι := ι))
    (K : Set M) (hK : IsCompact K) (hVK : V ⊆ K) (hcoreK : LeanShared.isolatedCore T K = Λ)
    (scaleFloor : ℝ) (state : ProbabilityMeasure M)
    (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T (b.hyperbolic.potential g) Λ state)
    (unique : ∀ μ, ThermodynamicDefinitions.IsEquilibriumState T (b.hyperbolic.potential g) Λ μ →
      μ = state) :
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
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap) L) ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     PhysicalModelAnnealedPair.NativePairIdentified
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
      scale ρ ρ weakRate weakRate (Real.exp P) (fun ψ => ∫ x, ψ.1 x ∂(state : Measure M))) := by
  obtain ⟨radiusT, tubes, d, W, openW, region, χ, hχg, support, forwardSupport, withinV, χbounds,
    χone, collar, η, positiveη, cap, capHigh, P, pressureP, ρ, positiveρ, belowP, weakRate, hweak,
    hρweak, scale, hscale, hρscale, hfloor, hscaleEq, pairSt, est₀, est₁, ab₀, ab₁⟩ :=
    Maps.adapted_carrier_pair_forward μE F positiveα subunitα lower αq hr regularT forward backward
      atlas positiveStable g weight positive hg radial cutoffs hb₀ hb₀1 b₀q positiveT negativeS
      positiveδ twoδ gap margin ha ha1 hab haq L K hK hVK hcoreK scaleFloor
  refine ⟨radiusT, tubes, d, W, openW, region, χ, hχg, support, forwardSupport, withinV, χbounds,
    χone, collar, η, positiveη, cap, capHigh, P, pressureP, ρ, positiveρ, belowP, weakRate, hweak,
    hρweak, scale, hscale, hρscale, hfloor, hscaleEq, ab₀, ab₁, ?_⟩
  have mapsTo : MapsTo (T : M → M) Λ Λ := fun x hx => b.hyperbolic.invariant ▸ mem_image_of_mem _ hx
  have hP0 : ThermodynamicDefinitions.pressure T
      (b.hyperbolic.potential (fun x => χ x * g x)) Λ = (P : EReal) :=
    (ThermodynamicDefinitions.pressure_eq_of_eqOn mapsTo fun x hx => by
      simp only [HyperbolicData.potential, χone x hx, one_mul]).trans pressureP
  have samePotential : EqOn (b.hyperbolic.potential g)
      (b.hyperbolic.potential (fun x => χ x * g x)) Λ := fun x hx => by
    simp only [HyperbolicData.potential, χone x hx, one_mul]
  have equilibrium' : ThermodynamicDefinitions.IsEquilibriumState T
      (b.hyperbolic.potential (fun x => χ x * g x)) Λ state :=
    ThermodynamicDefinitions.isEquilibriumState_congr mapsTo samePotential equilibrium
  have unique' : ∀ μ, ThermodynamicDefinitions.IsEquilibriumState T
      (b.hyperbolic.potential (fun x => χ x * g x)) Λ μ → μ = state := fun μ hμ =>
    unique μ (ThermodynamicDefinitions.isEquilibriumState_congr mapsTo samePotential.symm hμ)
  have weightNonneg : ∀ x, 0 ≤ χ x * g x := fun x => mul_nonneg (χbounds x).1 (gNonneg x)
  have weightPos : ∀ x ∈ Λ, 0 < χ x * g x := fun x hx => by
    rw [χone x hx, one_mul]
    exact positive x hx
  have hr1 : 1 < r := by linarith
  have cond₀ := carrierExponent_conditions positiveT negativeS (by linarith)
  have cond₁ := carrierExponent_conditions (t := t - δ) (s := s - δ) (by linarith) (by linarith)
    (by linarith)
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  have hw := cap.trans (bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
    support).below
  obtain ⟨L₀, _, bound₀⟩ := ab₀
  obtain ⟨L₁, _, bound₁⟩ := ab₁
  obtain ⟨Smax₀, R₀, hR₀, letters₀⟩ := est₀
  obtain ⟨Smax₁, R₁, hR₁, letters₁⟩ := est₁
  obtain ⟨strong₀, hs₀, _, pe₀⟩ := letters₀ (MapImage.reference (maps atlas F regularT) hr η hw)
  obtain ⟨strong₁, hs₁, _, pe₁⟩ := letters₁ (MapImage.reference (maps atlas F regularT) hr η hw)
  have key := PhysicalModelAnnealedPair.PairStatement.identified_native _ _ _ L.fixedLaw (fun _ => inferInstance)
    _ scale ρ ρ weakRate weakRate pairSt (MapImage.reference (maps atlas F regularT) hr η hw)
    (MapImage.clipped_zero (maps atlas F regularT) hr η hw) (Real.exp P) belowP belowP
    (AdaptedTubeUnitCarrierLeading.carrier_leading atlas d μE openW region hb₀ hb₀1 F hr regularT
        forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin δ (δ + δ) positiveδ (add_pos positiveδ positiveδ)
        η cap cond₀.1 cond₀.2.1 cond₀.2.2.1 cond₀.2.2.2 backward hr1 inverseRegular mixing
        weightNonneg weightPos forwardSupport withinV P hP0 _ rfl bound₀ strong₀ _ hs₀
        (fun i j => hR₀ _ _) pe₀)
    (AdaptedTubeUnitCarrierLeading.carrier_leading atlas d μE openW region hb₀ hb₀1 F hr regularT
        forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) (carrierStage_margin margin positiveδ.le)
        δ δ positiveδ positiveδ η cap cond₁.1 cond₁.2.1 cond₁.2.2.1 cond₁.2.2.2 backward hr1
        inverseRegular mixing weightNonneg weightPos forwardSupport withinV P hP0 _ rfl bound₁
        strong₁ _ hs₁ (fun i j => hR₁ _ _) pe₁)
    (fun ψ => ∫ x, ψ.1 x ∂(state : Measure M))
    (fun ψ dl hdl =>
      AdaptedTubeUnitCarrierIdentification.carrier_identification atlas d μE openW region hb₀ hb₀1
        F hr regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (s - δ)) (carrierStage_margin margin positiveδ.le)
        δ δ positiveδ positiveδ η cap cond₁.1 cond₁.2.1 cond₁.2.2.1 cond₁.2.2.2 backward hr1
        inverseRegular mixing weightNonneg weightPos forwardSupport withinV P hP0 state
        equilibrium' unique' _ rfl bound₁ dl hdl ψ.1 ψ.2)
  exact key

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
