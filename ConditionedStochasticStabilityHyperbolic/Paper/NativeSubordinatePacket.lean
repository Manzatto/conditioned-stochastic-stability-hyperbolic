module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeProducerOrders
public import ConditionedStochasticStabilityHyperbolic.Paper.NativePairPacket
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeSourceOrders
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierPairLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierPhysicalSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierReal
public import ConditionedStochasticStabilityHyperbolic.Paper.NativePacketOfPair
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedMapAgreement
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierForwardPair
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierComparison
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierRadius
public import LeanShared.Dynamics.PressureRestriction
public import LeanShared.Dynamics.HyperbolicAdaptedEvenCutoffs
public import LeanShared.Analysis.ConstructedSchwartzCutoff
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
meta import Lean.LibrarySuggestions.Basic

/-! The native analytic packet of one closed layer (global route, every layer). For a basic set
with positive stable dimension, an ordinary regular weight agreeing with the physical weight on
the isolating neighborhood, and a normalizer above the pressure, the forward carrier pair on the
layer gives a packet whose radius is bounded by the pressure and whose spectrum compares with the
physical-weight chain of any noisy map with the same germ. No mixing, leading record or
equilibrium state is used. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativeSubordinatePacket"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeSubordinatePacket
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open KellerLiverani1999 RegularNoise AdaptedTubeUnitCarrierBounds
open LinearRechartedManifold HyperbolicLinearRechart

variable {E ι : Type*} {M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

set_option maxHeartbeats 40000000 in
/-- The native packet of a closed layer. -/
theorem exists_packet {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    {r : ℝ} (r1 : 1 < r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (gp : M → ℝ) (hgp : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) gp)
    (gpNonneg : ∀ x, 0 ≤ gp x) (gpPos : ∀ x ∈ Λ, 0 < gp x)
    (w : M → ℝ) (hw : Continuous w) (wPos : ∀ x, 0 < w x) (agree : ∀ x ∈ V, gp x = w x)
    (stable : ∀ x ∈ Λ, 0 < Module.finrank ℝ (b.hyperbolic.stable x))
    (N : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
    (K : Set M) [CompactSpace K] (hK : IsCompact K) (hKm : MeasurableSet K)
    (hcoreK : LeanShared.isolatedCore T K = Λ) (hVK : V ⊆ K)
    (P0 : ℝ) (hP0 : ThermodynamicDefinitions.pressure T (b.hyperbolic.potential gp) Λ = (P0 : EReal))
    (R : ℝ) (hR1 : 1 ≤ R) (hRP : Real.exp P0 + 1 ≤ R) (hwR : ∀ x, w x ≤ R)
    (hgpR : ∀ x, gp x ≤ R)
    (Fg : ℝ≥0 → M × FixedControl (ι := ι) → M) (hFg : ∀ ε, Measurable (Fg ε))
    (hsame : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, Fg ε = fun z => N.fixedMap ε z.1 z.2) :
    Nonempty (NativeNullPrefixSources.NativePacket.{0, 0} K
      (fun ε => RestrictedNoise.chain (L.fixedLaw ε) (Fg ε) (hFg ε) K hKm (fun x => w x.val)
        (hw.measurable.comp measurable_subtype_coe) R (zero_lt_one.trans_le hR1)
        (fun x => hwR x.val))
      L.fixedLaw (fun _ => inferInstance) R P0) := by
  classical
  -- Orders and regularity.
  obtain ⟨α, t, sn, δ, positiveα, subunitα, αq, lowerα, positiveT, negativeS, positiveδ, twoδ, gap⟩ :=
    NativeLocalOutcomeProducer.native_orders r1
  obtain ⟨b₀, a, hb₀, hb₀1, b₀q, hab, -, ha1, haq, lowerA, tBelow, dual⟩ :=
    NativeSourceOrders.choose_orders t sn δ α (r - 1) r positiveT negativeS positiveδ gap subunitα αq
      lowerα
  have ha : 0 < a := hb₀.trans hab
  have stage0 := NativeSourceOrders.stage_conditions t sn δ α b₀ 0 negativeS positiveδ twoδ gap
    subunitα hb₀1 tBelow dual le_rfl (by linarith)
  have stage1 := NativeSourceOrders.stage_conditions t sn δ α b₀ δ negativeS positiveδ twoδ gap
    subunitα hb₀1 tBelow dual positiveδ.le (by linarith)
  have margin : ∀ sign, BTLinkedDyadicWeights.exponent t sn sign ≤ b₀ := by
    have := stage0.1
    simpa only [sub_zero] using this
  have hn : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using r1.le)
  have forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T :=
    regularT.differentiable.of_le (by exact_mod_cast hn)
  have backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M) :=
    inverseRegular.differentiable.of_le (by exact_mod_cast hn)
  obtain ⟨system⟩ := exists_system b forward backward
  let atlas := system.chartAtlas
  obtain ⟨x₀, hx₀⟩ := b.nonempty
  have positiveStable : 0 < system.framing.stableDimension :=
    NativeLocalOutcomeProducer.framing_stable_pos system.framing hx₀ (stable x₀ hx₀)
  have gpCont : Continuous gp := hgp.differentiable.continuous
  have hR : 0 < R := zero_lt_one.trans_le hR1
  -- The forward carrier pair with normalizer floor `R`.
  obtain ⟨radiusT, tubes, d, W, openW, region, χ, hχg, support, forwardSupport, withinV, χbounds,
    χone, collar, η, positiveη, cap, capHigh, P, pressureP, ρ, positiveρ, belowP, weakRate, hweak,
    hρweak, scale, hscale, hρscale, hfloor, hscaleEq, pairSt, -, -, -, ab₁⟩ :=
    Maps.adapted_carrier_pair_forward (volume : Measure system.EuclideanModel) N positiveα subunitα
      lowerα αq r1.le regularT forward backward atlas positiveStable gp gpCont gpPos hgp
      ConstructedSchwartzCutoff.radial system.evenCutoffs hb₀ hb₀1 b₀q positiveT negativeS
      positiveδ twoδ gap margin ha ha1 hab haq L K hK hVK hcoreK R
  have hPP : P = P0 := EReal.coe_injective (pressureP.symm.trans hP0)
  rw [hPP] at belowP
  have hscaleR : scale = R := hscaleEq.trans
    (max_eq_right (max_le hR1 (by linarith [belowP])))
  have hRscale : R = scale := hscaleR.symm
  subst hRscale
  obtain ⟨G, Bc, openG, coreG, GW, posG, openBc, coreBc, BcG, sepBc, χoneB⟩ := collar
  have coreW : Λ ⊆ W := fun x hx => support (subset_tsupport _ (by
    show χ x * gp x ≠ 0
    rw [χone x hx, one_mul]; exact (gpPos x hx).ne'))
  have hWK : W ⊆ K := fun x hx => hVK (withinV (subset_closure hx))
  have hBcW : closure Bc ⊆ W := BcG.trans (subset_closure.trans GW)
  -- The recharted structure.
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let _ : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, system.EuclideanModel)) x) :=
    ⟨transportMetric atlas.originalModelEquiv original⟩
  let _ := continuous_metric (M := M) atlas.originalModelEquiv
  obtain ⟨hnormH, hnorm₁, ⟨q⟩⟩ := pairSt
  obtain ⟨L₁, -, bound₁⟩ := ab₁
  have hw' := cap.trans (bounds atlas d (volume : Measure system.EuclideanModel) openW region hb₀
    hb₀1 N r1.le regularT forward b₀q hχg support).below
  let Nr := maps atlas N regularT
  let rep := MapImage.representation Nr r1.le η hw' positiveη
  have srcJoint := (AdaptedTubeUnitCarrierSources.sources atlas d (volume : Measure system.EuclideanModel)
    openW region hb₀ hb₀1 N r1.le regularT forward b₀q hχg support positiveStable
    ConstructedSchwartzCutoff.radial system.evenCutoffs.original
    (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ)) (carrierStage_margin margin positiveδ.le)
    δ δ positiveδ positiveδ η cap ha ha1 hab haq capHigh).joint
  have hF : ∀ ε : ℝ≥0, Measurable (fun z : M × FixedControl (ι := ι) =>
      MapImage.maps Nr r1.le η hw' (rep.fixedParameters ε z.2) z.1) := fun ε =>
    (srcJoint.comp (((MapImage.clipped_continuous Nr r1.le η hw' ε).comp continuous_snd).prodMk
      continuous_fst)).measurable
  -- Weights.
  have χgpCont : Continuous (fun x => χ x * gp x) := hχg.differentiable.continuous
  have χgpNonneg : ∀ x, 0 ≤ χ x * gp x := fun x => mul_nonneg (χbounds x).1 (gpNonneg x)
  have χgpPos : ∀ x ∈ Λ, 0 < χ x * gp x := fun x hx => by
    rw [χone x hx, one_mul]; exact gpPos x hx
  have wcBound : ∀ x, χ x * gp x ≤ R := fun x =>
    (mul_le_of_le_one_left (gpNonneg x) (χbounds x).2).trans (hgpR x)
  have agreeC : ∀ x ∈ closure Bc, χ x * gp x = w x := fun x hx => by
    rw [χoneB x hx, one_mul]
    exact agree x (withinV (subset_closure (hBcW hx)))
  -- Pressure of the cut weight.
  have mapsTo : MapsTo (T : M → M) Λ Λ := fun x hx =>
    b.hyperbolic.invariant ▸ mem_image_of_mem _ hx
  have cutPotential : EqOn (b.hyperbolic.potential (fun x => χ x * gp x))
      (b.hyperbolic.potential gp) Λ := fun x hx => by
    simp only [HyperbolicData.potential, χone x hx, one_mul]
  have hP0χ : ThermodynamicDefinitions.pressure T (b.hyperbolic.potential (fun x => χ x * gp x)) Λ =
      (P0 : EReal) :=
    (ThermodynamicDefinitions.pressure_eq_of_eqOn mapsTo cutPotential).trans hP0
  -- Spectrum comparison, nontriviality.
  have comparisonPack := NativePairLocalStability.pair_comparison_of_cached L R _ _ _ _ hnormH
    hnorm₁ q _ (AdaptedTubeUnitCarrierComparison.carrier_comparison atlas d
    (volume : Measure system.EuclideanModel) openW region hb₀ hb₀1 N r1.le regularT
    forward b₀q hχg support positiveStable ConstructedSchwartzCutoff.radial
    system.evenCutoffs.original (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ))
    (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap
    stage1.2.2.1 stage1.2.2.2.1 stage1.2.2.2.2.1 stage1.2.1 backward inverseRegular
    ha ha1 hab haq lowerA capHigh positiveη L K hK hcoreK hWK coreW G Bc openG
    coreG openBc coreBc hBcW sepBc w hw (fun x => (wPos x).le) (fun x _ => wPos _)
    χgpCont χgpNonneg agreeC R hR hwR wcBound hF bound₁)
  have nontrivial := comparisonPack.1
  have compare := comparisonPack.2
  have := nontrivial
  have sameGerm : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      (fun z : M × FixedControl (ι := ι) =>
        MapImage.maps Nr r1.le η hw' (MapImage.clipped Nr r1.le η hw' ε z.2) z.1) = Fg ε := by
    filter_upwards [MapImage.eventually_clipped_fixedMap (F := Nr) r1.le η hw' positiveη, hsame]
      with ε h1 h2
    rw [h2]
    exact h1
  have comparison := NativeLayerComparison.SpectrumComparison.of_eventually_eq L.fixedLaw _ Fg hF
    hFg sameGerm K hKm (fun x => w x.val) (hw.measurable.comp measurable_subtype_coe) R hR
    (fun x => hwR x.val) compare
  -- Radius at the pressure.
  have hH : ∀ z, (MapImage.clipped Nr r1.le η hw' 0 z) = MapImage.reference Nr r1.le η hw' :=
    MapImage.clipped_zero Nr r1.le η hw'
  -- Radius, packet and comparison are assembled at the model level.
  exact ⟨NativePairPacket.pairPacket K _ L R _ _ _ _ hnormH hnorm₁ q _ (fun z => hH z) P0 belowP.le
    (AdaptedTubeUnitCarrierRadius.carrier_radius_upper atlas d
      (volume : Measure system.EuclideanModel) openW region hb₀ hb₀1 N r1.le regularT
      forward b₀q hχg support positiveStable ConstructedSchwartzCutoff.radial
      system.evenCutoffs.original (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ))
      (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap
      (fun s => by linarith [stage1.2.1 s, hb₀1]) backward χgpNonneg χgpPos withinV P0 hP0χ
      (MapImage.reference Nr r1.le η hw') rfl bound₁)
    comparison⟩

/-- The native packet of a closed layer from basic data with any isolating neighborhood: the
neighborhood is shrunk inside the layer interior and the region where the regular weight is the
physical weight. -/
theorem exists_packet_of_layer {T : M ≃ₜ M} {Λ V₀ : Set M} (b : BasicData (E := E) T Λ V₀)
    {r : ℝ} (r1 : 1 < r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (O : Set M) (openO : IsOpen O) (coreO : Λ ⊆ O)
    (gp : M → ℝ) (hgp : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) gp)
    (gpNonneg : ∀ x, 0 ≤ gp x) (gpPos : ∀ x ∈ Λ, 0 < gp x)
    (w : M → ℝ) (hw : Continuous w) (wPos : ∀ x, 0 < w x) (agree : ∀ x ∈ O, gp x = w x)
    (stable : ∀ x ∈ Λ, 0 < Module.finrank ℝ (b.hyperbolic.stable x))
    (N : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
    (K : Set M) [CompactSpace K] (hK : IsCompact K) (hKm : MeasurableSet K)
    (hcoreK : LeanShared.isolatedCore T K = Λ) (coreK : Λ ⊆ interior K)
    (P0 : ℝ) (hP0 : ThermodynamicDefinitions.pressure T (b.hyperbolic.potential gp) Λ = (P0 : EReal))
    (R : ℝ) (hR1 : 1 ≤ R) (hRP : Real.exp P0 + 1 ≤ R) (hwR : ∀ x, w x ≤ R)
    (hgpR : ∀ x, gp x ≤ R)
    (Fg : ℝ≥0 → M × FixedControl (ι := ι) → M) (hFg : ∀ ε, Measurable (Fg ε))
    (hsame : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, Fg ε = fun z => N.fixedMap ε z.1 z.2) :
    Nonempty (NativeNullPrefixSources.NativePacket.{0, 0} K
      (fun ε => RestrictedNoise.chain (L.fixedLaw ε) (Fg ε) (hFg ε) K hKm (fun x => w x.val)
        (hw.measurable.comp measurable_subtype_coe) R (zero_lt_one.trans_le hR1)
        (fun x => hwR x.val))
      L.fixedLaw (fun _ => inferInstance) R P0) :=
  exists_packet (b.restrictNeighborhood (V₀ ∩ O ∩ interior K)
      ((b.open_neighborhood.inter openO).inter isOpen_interior)
      (fun _ hx => ⟨⟨b.subset_neighborhood hx, coreO hx⟩, coreK hx⟩) (fun _ hx => hx.1.1))
    r1 regularT inverseRegular gp hgp gpNonneg gpPos w hw wPos (fun x hx => agree x hx.1.2)
    stable N L K hK hKm hcoreK (fun _ hx => interior_subset hx.2) P0 hP0 R hR1 hRP hwR hgpR
    Fg hFg hsame

end ConditionedStochasticStabilityHyperbolic.Paper.NativeSubordinatePacket
