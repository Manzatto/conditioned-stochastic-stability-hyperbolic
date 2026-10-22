module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeSubordinatePacket
public import ConditionedStochasticStabilityHyperbolic.Global.ScaleSourcesCongr
public import ConditionedStochasticStabilityHyperbolic.Paper.NativePairPacket
public import LeanShared.Dynamics.HyperbolicAdaptedEvenCutoffs
public import LeanShared.Analysis.ConstructedSchwartzCutoff
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
meta import Lean.LibrarySuggestions.Basic

/-! The native selected layer. On the selected closed layer the basic set is mixing and its pair
weight has a unique equilibrium state; the leading carrier pair then gives the native packet
together with its selection: leading record, contour, and the eventual physical sources of the
carrier transported to the global noisy map. The collars of the carrier are exported for the
prefix geometry. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativeSelectedLayer"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeSelectedLayer
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open KellerLiverani1999 RegularNoise AdaptedTubeUnitCarrierBounds
open LinearRechartedManifold HyperbolicLinearRechart

/-- The selected layer: carrier collars, cutoff weight, native packet and its selection. -/
structure SelectedLayer {M ι : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M]
    [BorelSpace M] [SecondCountableTopology M] [Fintype ι]
    (T : M ≃ₜ M) (Λ K : Set M) [CompactSpace K] (hK : IsCompact K)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K) (L : RegularNoise.Laws (ι := ι))
    (R P0 : ℝ) (hR : 0 < R)
    (Fg : ℝ≥0 → M × FixedControl (ι := ι) → M) (hFg : ∀ ε, Measurable (Fg ε))
    (w : M → ℝ) (hw : Continuous w) (hwR : ∀ x, w x ≤ R) where
  V : Set M
  G : Set M
  B : Set M
  live_open : IsOpen V
  live_subset : V ⊆ K
  retained_open : IsOpen B
  core_retained : Λ ⊆ B
  retained_live : closure B ⊆ V
  retained_collar : closure B ⊆ G
  core_collar : Λ ⊆ G
  no_return : (T '' closure B) ∩ forwardTrapped T K ⊆ B
  cutoff : K → ℝ
  cutoff_measurable : Measurable cutoff
  cutoff_bound : ∀ x, cutoff x ≤ R
  packet : NativeNullPrefixSources.NativePacket.{0, 0} K C L.fixedLaw (fun _ => inferInstance) R P0
  selection : NativeNullPrefixSources.NativeSelection.{0, 0, 0, _, _, _, 0, 0} packet T V G hK L.fixedLaw Fg
    hFg (fun x => w x.val) cutoff (hw.comp continuous_subtype_val) cutoff_measurable hR
    (fun x => hwR x.val) cutoff_bound

variable {E ι : Type*} {M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

set_option maxHeartbeats 40000000 in
/-- The native selected layer. -/
theorem exists_selected {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    {r : ℝ} (r1 : 1 < r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (mixing : HyperbolicBasicSet.MixingOn T Λ)
    (gp : M → ℝ) (hgp : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) gp)
    (gpNonneg : ∀ x, 0 ≤ gp x) (gpPos : ∀ x ∈ Λ, 0 < gp x)
    (state : ProbabilityMeasure M)
    (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T (b.hyperbolic.potential gp) Λ state)
    (unique : ∀ μ, ThermodynamicDefinitions.IsEquilibriumState T (b.hyperbolic.potential gp) Λ μ →
      μ = state)
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
    Nonempty (SelectedLayer T Λ K hK
      (fun ε => RestrictedNoise.chain (L.fixedLaw ε) (Fg ε) (hFg ε) K hKm (fun x => w x.val)
        (hw.measurable.comp measurable_subtype_coe) R (zero_lt_one.trans_le hR1)
        (fun x => hwR x.val))
      L R P0 (zero_lt_one.trans_le hR1) Fg hFg w hw hwR) := by
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
  -- The leading carrier pair with normalizer floor `R`.
  obtain ⟨radiusT, tubes, d, W, openW, region, χ, hχg, support, forwardSupport, withinV, χbounds,
    χone, collar, η, positiveη, cap, capHigh, P, pressureP, ρ, positiveρ, belowP, weakRate, hweak,
    hρweak, scale, hscale, hρscale, hfloor, hscaleEq, ab₀, ab₁, pairPack⟩ :=
    Maps.adapted_carrier_pair_leading (volume : Measure system.EuclideanModel) N positiveα subunitα
      lowerα αq r1.le regularT forward backward atlas positiveStable gp gpCont gpPos hgp
      ConstructedSchwartzCutoff.radial system.evenCutoffs hb₀ hb₀1 b₀q positiveT negativeS
      positiveδ twoδ gap margin inverseRegular mixing gpNonneg ha ha1 hab haq L K hK hVK hcoreK R
      state equilibrium unique
  have hPP : P = P0 := EReal.coe_injective (pressureP.symm.trans hP0)
  rw [hPP] at belowP hweak
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
  obtain ⟨hnormH, hnorm₁, q, ds, dm, rateS, rateH₀, -⟩ := pairPack
  -- Term-mode transport: rewriting would traverse the carrier terms inside `dm.rate`.
  have rateH := rateH₀.trans (congrArg (fun P' => R⁻¹ * Real.exp P') hPP)
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
  have mapsTo : MapsTo (T : M → M) Λ Λ := fun x hx =>
    b.hyperbolic.invariant ▸ mem_image_of_mem _ hx
  have cutPotential : EqOn (b.hyperbolic.potential (fun x => χ x * gp x))
      (b.hyperbolic.potential gp) Λ := fun x hx => by
    simp only [HyperbolicData.potential, χone x hx, one_mul]
  have hP0χ : ThermodynamicDefinitions.pressure T (b.hyperbolic.potential (fun x => χ x * gp x)) Λ =
      (P0 : EReal) :=
    (ThermodynamicDefinitions.pressure_eq_of_eqOn mapsTo cutPotential).trans hP0
  -- Spectrum comparison, nontriviality, germ.
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
  have evenAngle : ∀ ξ, system.evenCutoffs.original.toFun (-ξ) = system.evenCutoffs.original.toFun ξ :=
    system.evenCutoffs_even
  -- Packet and selection are assembled at the model level.
  exact ⟨{
    V := W
    G := G
    B := Bc
    live_open := openW
    live_subset := hWK
    retained_open := openBc
    core_retained := coreBc
    retained_live := hBcW
    retained_collar := BcG
    core_collar := coreG
    no_return := sepBc
    cutoff := fun x => χ x.val * gp x.val
    cutoff_measurable := (χgpCont.comp continuous_subtype_val).measurable
    cutoff_bound := fun x => wcBound x.val
    packet := NativePairPacket.pairPacket K _ L R _ _ _ _ hnormH hnorm₁ q _ (fun z => hH z) P0
      belowP.le (AdaptedTubeUnitCarrierRadius.carrier_radius_upper atlas d
      (volume : Measure system.EuclideanModel) openW region hb₀ hb₀1 N r1.le regularT
      forward b₀q hχg support positiveStable ConstructedSchwartzCutoff.radial
      system.evenCutoffs.original (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ))
      (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap
      (fun s => by linarith [stage1.2.1 s, hb₀1]) backward χgpNonneg χgpPos withinV P0 hP0χ
      (MapImage.reference Nr r1.le η hw') rfl bound₁) comparison
    selection := NativePairPacket.pairSelection K _ L R _ _ _ _ hnormH hnorm₁ q _ (fun z => hH z) P0
      belowP.le (AdaptedTubeUnitCarrierRadius.carrier_radius_upper atlas d
      (volume : Measure system.EuclideanModel) openW region hb₀ hb₀1 N r1.le regularT
      forward b₀q hχg support positiveStable ConstructedSchwartzCutoff.radial
      system.evenCutoffs.original (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ))
      (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap
      (fun s => by linarith [stage1.2.1 s, hb₀1]) backward χgpNonneg χgpPos withinV P0 hP0χ
      (MapImage.reference Nr r1.le η hw') rfl bound₁) comparison T W G hK _ Fg hF hFg sameGerm (fun x => w x.val)
      (fun x => χ x.val * gp x.val) (hw.comp continuous_subtype_val)
      (χgpCont.comp continuous_subtype_val).measurable hR (fun x => hwR x.val)
      (fun x => wcBound x.val) dm rateH belowP hweak _
      (fun i x => AdaptedTubeUnitCarrierReal.cutoff_real atlas d
        (volume : Measure system.EuclideanModel) openW region hb₀ hb₀1 N r1.le
        regularT forward b₀q hχg support positiveStable
        ConstructedSchwartzCutoff.radial system.evenCutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap i x)
      (fun i ξ => evenAngle ξ)
      (AdaptedTubeUnitCarrierReal.jreg atlas d openW hb₀ hb₀1)
      (fun v x => AdaptedTubeUnitCarrierReal.view_jreg atlas d
        (volume : Measure system.EuclideanModel) openW region hb₀ hb₀1 N r1.le
        regularT forward b₀q hχg support positiveStable
        ConstructedSchwartzCutoff.radial system.evenCutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap v x)
      bound₁
      (AdaptedTubeUnitCarrierPhysicalSources.carrier_sources atlas d
        (volume : Measure system.EuclideanModel) openW region hb₀ hb₀1 N r1.le regularT
        forward b₀q hχg support positiveStable ConstructedSchwartzCutoff.radial
        system.evenCutoffs.original (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ))
        (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap
        stage1.2.2.1 stage1.2.2.2.1 stage1.2.2.2.2.1 stage1.2.1 backward inverseRegular
        ha ha1 hab haq lowerA capHigh positiveη L K hK hcoreK hWK coreW G Bc openG
        coreG openBc coreBc hBcW sepBc w hw (fun x => (wPos x).le) (fun x _ => wPos _)
        χgpCont χgpNonneg agreeC R hR hwR wcBound hF bound₁) }⟩

/-- The native selected layer from basic data with any isolating neighborhood. -/
theorem exists_selected_of_layer {T : M ≃ₜ M} {Λ V₀ : Set M} (b : BasicData (E := E) T Λ V₀)
    {r : ℝ} (r1 : 1 < r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (mixing : HyperbolicBasicSet.MixingOn T Λ)
    (O : Set M) (openO : IsOpen O) (coreO : Λ ⊆ O)
    (gp : M → ℝ) (hgp : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) gp)
    (gpNonneg : ∀ x, 0 ≤ gp x) (gpPos : ∀ x ∈ Λ, 0 < gp x)
    (state : ProbabilityMeasure M)
    (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T (b.hyperbolic.potential gp) Λ state)
    (unique : ∀ μ, ThermodynamicDefinitions.IsEquilibriumState T (b.hyperbolic.potential gp) Λ μ →
      μ = state)
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
    Nonempty (SelectedLayer T Λ K hK
      (fun ε => RestrictedNoise.chain (L.fixedLaw ε) (Fg ε) (hFg ε) K hKm (fun x => w x.val)
        (hw.measurable.comp measurable_subtype_coe) R (zero_lt_one.trans_le hR1)
        (fun x => hwR x.val))
      L R P0 (zero_lt_one.trans_le hR1) Fg hFg w hw hwR) :=
  exists_selected (b.restrictNeighborhood (V₀ ∩ O ∩ interior K)
      ((b.open_neighborhood.inter openO).inter isOpen_interior)
      (fun _ hx => ⟨⟨b.subset_neighborhood hx, coreO hx⟩, coreK hx⟩) (fun _ hx => hx.1.1))
    r1 regularT inverseRegular mixing gp hgp gpNonneg gpPos state equilibrium unique w hw wPos
    (fun x hx => agree x hx.1.2) stable N L K hK hKm hcoreK (fun _ hx => interior_subset hx.2)
    P0 hP0 R hR1 hRP hwR hgpR Fg hFg hsame

end ConditionedStochasticStabilityHyperbolic.Paper.NativeSelectedLayer
