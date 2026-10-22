module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcome
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeProducerOrders
public import ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSetup
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierPairLeading
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeSourceOrders
public import ConditionedStochasticStabilityHyperbolic.Paper.NativePairLocalStability
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalEquilibriumIdentification
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImageRepresentation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierPhysicalSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierReal
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeLoweredParents
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniProjectorSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusSource
public import LeanShared.Dynamics.HyperbolicAdaptedEvenCutoffs
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
public import LeanShared.Analysis.ConstructedSchwartzCutoff
meta import Lean.LibrarySuggestions.Basic

/-! The native local outcome (thm:local and thm:qem-local). For an HL triple with positive stable
dimension, a weight `w` and an adapted local weight setup on an analysis neighborhood, the
actual noise and laws give literal local stochastic stability and gap retention on any compact
live state `K` isolating `Λ`, with any prescribed lower bound for the normalizer. The carrier
pair, its leading records and D07 identification, its physical sources, conjugations and the
local consumer are all applied here; no spectral, source or stability statement is assumed. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativeLocalOutcomeProducer"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcomeProducer
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
/-- The native local outcome: literal stability and retention on a compact live state. -/
theorem native_local_outcome {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)
    (w : M → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    {W' : Set M} (s : AdaptedLocalWeightSetup.Data h w W')
    (K : Set M) [CompactSpace K] (hK : IsCompact K) (hcoreK : LeanShared.isolatedCore T K = Λ)
    (hW'K : W' ⊆ K)
    (stable : ∀ x ∈ Λ, 0 < Module.finrank ℝ (s.fresh.basic.hyperbolic.stable x))
    (N : RegularNoise.Maps (E := E) (ι := ι) T s.fresh.r) (L : RegularNoise.Laws (ι := ι))
    (φ : M → ℝ) (hφ : ∀ x ∈ Λ, (s.cutoff * w) x = Real.exp (φ x)) (floor : ℝ) :
    ∃ d : NativeLocalOutcome s.fresh ι K hK (fun x => w x.val) φ,
      d.maps = N ∧ d.laws = L ∧ floor ≤ d.scale := by
  classical
  -- Orders, regularity and the restricted basic data.
  let r := s.fresh.r
  have hrdef : r = s.fresh.r := rfl
  have r1 : 1 < r := s.fresh.regularity_gt_one
  obtain ⟨α, t, sn, δ, positiveα, subunitα, αq, lowerα, positiveT, negativeS, positiveδ, twoδ, gap⟩ :=
    native_orders r1
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
    s.fresh.map_regular.differentiable.of_le (by exact_mod_cast hn)
  have backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M) :=
    s.fresh.inverse_regular.differentiable.of_le (by exact_mod_cast hn)
  have retainedW' : s.retained ⊆ W' := fun x hx =>
    s.collar_live (subset_closure (s.retained_collar (subset_closure hx)))
  let b := s.fresh.basic.restrictNeighborhood s.retained s.retained_open s.core_retained retainedW'
  have hVK : s.retained ⊆ K := fun x hx => hW'K (retainedW' hx)
  obtain ⟨system⟩ := exists_system b forward backward
  let atlas := system.chartAtlas
  obtain ⟨x₀, hx₀⟩ := h.nonempty_core
  have positiveStable : 0 < system.framing.stableDimension :=
    NativeLocalOutcomeProducer.framing_stable_pos system.framing hx₀ (stable x₀ hx₀)
  -- The globally regular pair weight and the bounds of the two weights.
  let gp : M → ℝ := s.cutoff * w
  have hgp : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) gp :=
    s.fresh.weight_regular
  have gpCont : Continuous gp := hgp.differentiable.continuous
  have gpNonneg : ∀ x, 0 ≤ gp x := s.fresh.weight_nonnegative
  have gpPos : ∀ x ∈ Λ, 0 < gp x := s.fresh.weight_positive
  obtain ⟨xw, -, maxw⟩ := isCompact_univ.exists_isMaxOn (h.nonempty_core.mono (subset_univ _)) hw.continuousOn
  obtain ⟨xg, -, maxg⟩ := isCompact_univ.exists_isMaxOn (h.nonempty_core.mono (subset_univ _)) gpCont.continuousOn
  let floor' := max floor (max (w xw) (gp xg))
  have wBound : ∀ x, w x ≤ floor' := fun x =>
    (maxw (mem_univ x)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have gpBound : ∀ x, gp x ≤ floor' := fun x =>
    (maxg (mem_univ x)).trans ((le_max_right _ _).trans (le_max_right _ _))
  -- The equilibrium state of the pair weight.
  let e₀ := s.fresh.proved_equilibriumPackage
  -- The carrier pair with leading records and consumer ratios.
  obtain ⟨radiusT, tubes, d, W, openW, region, χ, hχg, support, forwardSupport, withinV, χbounds,
    χone, collar, η, positiveη, cap, capHigh, P, pressureP, ρ, positiveρ, belowP, weakRate, hweak,
    hρweak, scale, hscale, hρscale, hfloor, -, ab₀, ab₁, pairPack⟩ :=
    Maps.adapted_carrier_pair_leading (volume : Measure system.EuclideanModel) N positiveα subunitα
      lowerα αq r1.le s.fresh.map_regular forward backward atlas positiveStable gp gpCont gpPos hgp
      ConstructedSchwartzCutoff.radial system.evenCutoffs hb₀ hb₀1 b₀q positiveT negativeS
      positiveδ twoδ gap margin s.fresh.inverse_regular s.fresh.mixing gpNonneg ha ha1 hab haq L
      K hK hVK hcoreK floor' e₀.state e₀.equilibrium e₀.unique
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
  obtain ⟨L₀, -, bound₀⟩ := ab₀
  obtain ⟨L₁, -, bound₁⟩ := ab₁
  have hw' := cap.trans (bounds atlas d (volume : Measure system.EuclideanModel) openW region hb₀
    hb₀1 N r1.le s.fresh.map_regular forward b₀q hχg support).below
  let Nr := maps atlas N s.fresh.map_regular
  let rep := MapImage.representation Nr r1.le η hw' positiveη
  have srcJoint := (AdaptedTubeUnitCarrierSources.sources atlas d (volume : Measure system.EuclideanModel)
    openW region hb₀ hb₀1 N r1.le s.fresh.map_regular forward b₀q hχg support positiveStable
    ConstructedSchwartzCutoff.radial system.evenCutoffs.original
    (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ)) (carrierStage_margin margin positiveδ.le)
    δ δ positiveδ positiveδ η cap ha ha1 hab haq capHigh).joint
  have hF : ∀ ε : ℝ≥0, Measurable (fun z : M × FixedControl (ι := ι) =>
      MapImage.maps Nr r1.le η hw' (rep.fixedParameters ε z.2) z.1) := fun ε =>
    (srcJoint.comp (((MapImage.clipped_continuous Nr r1.le η hw' ε).comp continuous_snd).prodMk
      continuous_fst)).measurable
  -- The fresh HL record of the cutoff weight on the carrier region, in the recharted charts.
  let bdR := (HyperbolicLinearRechart.transportBasic atlas.originalModelEquiv b
    (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero)).restrictNeighborhood
    W openW coreW (fun x hx => withinV (subset_closure hx))
  let hFresh : HL (E := system.EuclideanModel) T (fun x => χ x * gp x) Λ W :=
    { r := r
      regularity_gt_one := r1
      map_regular := s.fresh.map_regular.linearRechart atlas.originalModelEquiv
      inverse_regular := s.fresh.inverse_regular.linearRechart atlas.originalModelEquiv
      basic := bdR
      weight_regular := hχg.scalarLinearRechart atlas.originalModelEquiv
      weight_nonnegative := fun x => mul_nonneg (χbounds x).1 (gpNonneg x)
      weight_supported := support
      weight_positive := fun x hx => by rw [χone x hx, one_mul]; exact gpPos x hx
      mixing := s.fresh.mixing }
  let e := hFresh.proved_equilibriumPackage
  -- The fresh equilibrium state is the pair-weight equilibrium state.
  have mapsTo : MapsTo (T : M → M) Λ Λ := fun x hx =>
    s.fresh.basic.hyperbolic.invariant ▸ mem_image_of_mem _ hx
  have samePotential : hFresh.basic.hyperbolic.potential (fun x => χ x * gp x) =
      b.hyperbolic.potential (fun x => χ x * gp x) :=
    HyperbolicLinearRechart.basic_potential_eq atlas.originalModelEquiv b
      (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero) _
  have cutPotential : EqOn (b.hyperbolic.potential (fun x => χ x * gp x))
      (s.fresh.basic.hyperbolic.potential gp) Λ := fun x hx => by
    simp only [HyperbolicData.potential, χone x hx, one_mul]
    rfl
  have stateEq : e.state = e₀.state := by
    apply e₀.unique
    have := e.equilibrium
    rw [samePotential] at this
    exact ThermodynamicDefinitions.isEquilibriumState_congr mapsTo cutPotential this
  -- The local consumer in the recharted charts.
  have hΛK : isolatedCore T K = Λ := hcoreK
  have hcoreU : isolatedCore T K ⊆ Bc := hΛK ▸ coreBc
  have hcoreG : isolatedCore T K ⊆ G := hΛK ▸ coreG
  have htrans : ControlledPlaqueClosure.forwardTransitiveOn T (isolatedCore T K) := by
    rw [hΛK]; exact s.fresh.transitive
  have hcore : (isolatedCore T K).Nonempty := by rw [hΛK]; exact h.nonempty_core
  have wPos : ∀ x : K, x.val ∈ G → 0 < w x.val := fun x hx => by
    have positive := (posG x.val (subset_closure hx)).1
    rcases (hw0 x.val).lt_or_eq with lt | eq
    · exact lt
    · exfalso
      change 0 < s.cutoff x.val * w x.val at positive
      rw [← eq, mul_zero] at positive
      exact lt_irrefl _ positive
  have χgpCont : Continuous (fun x => χ x * gp x) := hχg.differentiable.continuous
  have wcBound : ∀ x, χ x * gp x ≤ scale := fun x =>
    (mul_le_of_le_one_left (gpNonneg x) (χbounds x).2).trans ((gpBound x).trans hfloor)
  have hR : 0 < scale := zero_lt_one.trans_le hscale
  have agree : ∀ x ∈ closure Bc, χ x * gp x = w x := fun x hx => by
    rw [χoneB x hx, one_mul]
    exact s.weight_agreement (subset_closure (withinV (subset_closure (hBcW hx))))
  have evenAngle : ∀ ξ, system.evenCutoffs.original.toFun (-ξ) = system.evenCutoffs.original.toFun ξ :=
    system.evenCutoffs_even
  -- Stability and retention from the identified pair, assembled at the model level.
  obtain ⟨stability, retain⟩ := NativePairLocalStability.native_pair_stability
      T W K G Bc hFresh hΛK e φ
      (fun x hx => by rw [χone x hx, one_mul]; exact hφ x hx)
      openW hWK hK openBc hcoreU hBcW BcG sepBc hcoreG htrans hcore Nr L rep hF
      (fun x => w x.val) (hw.comp continuous_subtype_val) wPos
      (fun x => χ x.val * gp x.val)
      ((χgpCont.comp continuous_subtype_val).measurable)
      scale hR (fun x => (wBound x.val).trans hfloor) (fun x => wcBound x.val)
      _ _ _ _ e₀.state pairPack belowP hweak stateEq
      (fun i x => AdaptedTubeUnitCarrierReal.cutoff_real atlas d (volume : Measure system.EuclideanModel)
        openW region hb₀ hb₀1 N r1.le s.fresh.map_regular forward b₀q hχg support positiveStable
        ConstructedSchwartzCutoff.radial system.evenCutoffs.original
        (BTLinkedDyadicWeights.exponent t sn) margin δ (δ + δ) positiveδ (add_pos positiveδ positiveδ) η cap i x)
      (fun i ξ => evenAngle ξ)
      (AdaptedTubeUnitCarrierReal.jreg atlas d openW hb₀ hb₀1)
      (fun v x => AdaptedTubeUnitCarrierReal.view_jreg atlas d (volume : Measure system.EuclideanModel)
        openW region hb₀ hb₀1 N r1.le s.fresh.map_regular forward b₀q hχg support positiveStable
        ConstructedSchwartzCutoff.radial system.evenCutoffs.original
        (BTLinkedDyadicWeights.exponent t sn) margin δ (δ + δ) positiveδ (add_pos positiveδ positiveδ) η cap v x)
      bound₀
      (fun i x => AdaptedTubeUnitCarrierReal.cutoff_real atlas d (volume : Measure system.EuclideanModel)
        openW region hb₀ hb₀1 N r1.le s.fresh.map_regular forward b₀q hχg support positiveStable
        ConstructedSchwartzCutoff.radial system.evenCutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ)) (carrierStage_margin margin positiveδ.le)
        δ δ positiveδ positiveδ η cap i x)
      (fun i ξ => evenAngle ξ)
      (AdaptedTubeUnitCarrierReal.jreg atlas d openW hb₀ hb₀1)
      (fun v x => AdaptedTubeUnitCarrierReal.view_jreg atlas d (volume : Measure system.EuclideanModel)
        openW region hb₀ hb₀1 N r1.le s.fresh.map_regular forward b₀q hχg support positiveStable
        ConstructedSchwartzCutoff.radial system.evenCutoffs.original
        (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ)) (carrierStage_margin margin positiveδ.le)
        δ δ positiveδ positiveδ η cap v x)
      bound₁
      (fun j inputs hgen injective compact _ _ _ o hδsub hδlead hq hprincipal conjugation =>
        AdaptedTubeUnitCarrierPhysicalSources.carrier_sources atlas d
          (volume : Measure system.EuclideanModel) openW region hb₀ hb₀1 N r1.le s.fresh.map_regular
          forward b₀q hχg support positiveStable ConstructedSchwartzCutoff.radial
          system.evenCutoffs.original (BTLinkedDyadicWeights.exponent (t - δ) (sn - δ))
          (carrierStage_margin margin positiveδ.le) δ δ positiveδ positiveδ η cap
          stage1.2.2.1 stage1.2.2.2.1 stage1.2.2.2.2.1 stage1.2.1 backward s.fresh.inverse_regular
          ha ha1 hab haq lowerA capHigh positiveη L K hK hcoreK hWK coreW G Bc openG
          coreG openBc coreBc hBcW sepBc w hw hw0 (fun x hx => by
            have positive := (posG x hx).2
            rcases (hw0 (T.symm x)).lt_or_eq with lt | eq
            · exact lt
            · exfalso
              change 0 < s.cutoff (T.symm x) * w (T.symm x) at positive
              rw [← eq, mul_zero] at positive
              exact lt_irrefl _ positive)
          χgpCont
          (fun x => mul_nonneg (χbounds x).1 (gpNonneg x)) agree scale hR
          (fun x => (wBound x).trans hfloor) wcBound hF bound₁ j inputs hgen injective compact o
          hδsub hδlead hq hprincipal conjugation)
  -- The same Jacobian on the transported and original hyperbolic data.
  have logJacobian : ∀ x, Real.log (hFresh.basic.hyperbolic.unstableJacobian x) =
      Real.log (s.fresh.basic.hyperbolic.unstableJacobian x) := fun x => by
    have oneEq : hFresh.basic.hyperbolic.potential (fun _ => (1 : ℝ)) =
        b.hyperbolic.potential (fun _ => (1 : ℝ)) :=
      HyperbolicLinearRechart.basic_potential_eq atlas.originalModelEquiv b
        (forward.mdifferentiable one_ne_zero) (backward.mdifferentiable one_ne_zero) _
    have one := congrFun oneEq x
    simp only [HyperbolicData.potential, Real.log_one, zero_sub, neg_inj] at one
    exact one
  have samePotentialφ : (fun x => φ x - Real.log (hFresh.basic.hyperbolic.unstableJacobian x)) =
      (fun x => φ x - Real.log (s.fresh.basic.hyperbolic.unstableJacobian x)) :=
    funext fun x => by rw [logJacobian x]
  rw [samePotentialφ] at stability
  exact ⟨{ maps := N
           laws := L
           scale := scale
           scale_positive := hR
           weight_continuous := hw.comp continuous_subtype_val
           weight_bound := fun x => (wBound x.val).trans hfloor
           stability := stability
           retain := retain }, rfl, rfl, (le_max_left _ _).trans hfloor⟩

end ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcomeProducer
