module

import all ConditionedStochasticStabilityHyperbolic.Paper.RegularCoreLocalConsumer

public import ConditionedStochasticStabilityHyperbolic.Paper.HLNoFullSupportLocalStability
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalLayerUniversalScaleFactory
public import LeanShared.Geometry.SmoothHolderNormedParents
public import LeanShared.Analysis.SubmoduleNormedSpaceParent
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierComplete
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerNoiseSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicPairTrace
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderAnnealedConjugation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldRealStructure

/-! The local conclusion from the constructed two analytic models and ordinary
physical sources. In particular no noisy gap, comparison, probability product,
physical source factory or weak-limit assertion is an input. -/
public noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalLocalStability
open LeanShared DyadicCompletion SmoothSupportedManifoldCore KellerLiverani1999
open LeanShared.ControlledPlaqueClosure LeanShared.TwoNormNormalization
open PhysicalHolderClassicalSources.SourceData

universe uX

private theorem stability_from_classical_physical_sources
  {X : Type uX} {E U AtlasIndex A Parameters : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MetricSpace Parameters]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  (u : ℝ) (holder : ∀ c : core (E := E) (univ : Set X), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)
  {V S : Set X} {μ : Measure U} [μ.IsAddHaarMeasure]
  (ms mh : PhysicalManifoldModel.Data (E := E) (U := U) (M := X)
    (AtlasIndex := AtlasIndex) (Reg := PhysicalHolderClassicalSources.Regular u holder V)
    (LocalReg := LocalReg) (A := A) (Ω := Parameters) V S μ)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  {ι : Type*} [Fintype ι] {T : X ≃ₜ X} {g : X → ℝ} {Λ : Set X}

    (K G B : Set X) [CompactSpace K] (hK : IsCompact K)
    (hHL : HL (E := E) T g Λ V) (hΛ : isolatedCore T K = Λ)
    (equilibrium : HyperbolicBasicSet.EquilibriumPackage hHL.basic.hyperbolic g)
    (φ : X → ℝ) (hφ : ∀ x ∈ Λ, g x = Real.exp (φ x))
    (N : RegularNoise.Maps (E := E) (ι := ι) T hHL.r) (L : RegularNoise.Laws (ι := ι))
    (representation : RegularNoise.Representation N Parameters mh.maps)
    (hF : ∀ ε : ℝ≥0, Measurable (fun z : X × RegularNoise.FixedControl (ι := ι) =>
      mh.maps (representation.fixedParameters ε z.2) z.1))
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (hweight : ∀ x : K, mh.weight x.val = wc x)
    (i : ms.StrongSpace →L[ℂ] mh.StrongSpace) (j : mh.StrongSpace →L[ℂ] W)
    (p : ProducedAnnealedPair.Data i j L.fixedLaw (fun _ => inferInstance)
      (fun ε z => ms.generator (representation.fixedParameters ε z))
      (fun ε z => mh.generator (representation.fixedParameters ε z)) R)
    (rowsS : PhysicalManifoldRowSources.Data ms) (rowsH : PhysicalManifoldRowSources.Data mh)
    (noiseH : PhysicalManifoldNoiseSources.Data mh)
    (σ : Measure X) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (commonS : PhysicalHolderClassicalSources.Data u holder ms K (σ.comap Subtype.val))
    (common : PhysicalHolderClassicalSources.Data u holder mh K (σ.comap Subtype.val))
    (ordinarySource : RegularLayerNoiseSources.Data representation σ V K G B hK w wc R
      (fullView u holder) (fullView_injective u holder) (fullCore u holder))
    (submersion : RegularNoise.ControlSubmersionSources (E := E) (ι := ι) σ)
    (hBG : closure B ⊆ G)
    (r t sn : ℝ) (margins : RegularCoreApproximation.RegularityMargins r t sn u)
    (essentialS : EssentialRadiusContract (E := ms.StrongSpace) (W := W))
    (essentialH : EssentialRadiusContract (E := mh.StrongSpace) (W := W))
    (klS : ClassicalContract (E := ms.StrongSpace) (W := W))
    (klH : ClassicalContract (E := mh.StrongSpace) (W := W))
    (ds : DeterministicLeading (p.strong.operator 0))
    (dm : DeterministicLeading (p.intermediate.operator 0))
    (hprincipalS : p.strong.principal / R < ds.rate)
    (hweakS : ds.rate ≤ p.strong.weakRate / R)
    (hprincipalH : p.intermediate.principal / R < dm.rate)
    (hweakH : dm.rate ≤ p.intermediate.weakRate / R)
    (deterministicPressure : ds.rate = dm.rate)
    (realCutoffS : ∀ a x, conj (ms.localization.cutoff a x) = ms.localization.cutoff a x)
    (realCutoffH : ∀ a x, conj (mh.localization.cutoff a x) = mh.localization.cutoff a x)
    (evenAngleS : ∀ a ξ, (ms.angle a).toFun (-ξ) = (ms.angle a).toFun ξ)
    (evenAngleH : ∀ a ξ, (mh.angle a).toFun (-ξ) = (mh.angle a).toFun ξ)
    (a2 : ∀ {Z : Type uX} [NormedAddCommGroup Z] [NormedSpace ℂ Z],
      CommonAmbientClassicalComparison.ClassicalContract (A := mh.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K mh.regularCore))
      (Z := Z)
      (Reg := PhysicalHolderClassicalSources.Regular u holder V) (W := W))
    (deterministicEquilibrium : ∀ h : SmoothPhysicalTests.tests (E := E) K,
      (∫ x, h.val x ∂(hHL.stateOnCollar equilibrium K hK.measurableSet (by
        rw [← hΛ]; exact ordinarySource.core_retained.trans
          ((subset_closure.trans ordinarySource.retained_live).trans ordinarySource.live_subset)) : Measure K)) =
      (dm.mean (ConstructedRegularMultipliers.analyticMultiplier (coreLift mh.qa)
        (multiplier V ((common.coreData u holder mh K (σ.comap Subtype.val)).test h)
          ((common.coreData u holder mh K (σ.comap Subtype.val)).test_smooth h)) dm.vector)).re) :
    LocalConclusions.Stability N L K Λ hK.measurableSet w hw.measurable R hR hwR
      (fun x => φ x - Real.log (hHL.basic.hyperbolic.unstableJacobian x)) := by
  let ordinary := ordinarySource.produce submersion L hw hwc hR hwR hwcR hF
  have conjS := PhysicalHolderAnnealedConjugation.actual_conjugation u holder ms K (σ.comap Subtype.val)
    commonS rowsS realCutoffS evenAngleS L.fixedLaw representation.fixedParameters (j.comp i) R
      p.strong p.strong_generator
  have conjH := PhysicalHolderAnnealedConjugation.actual_conjugation u holder mh K (σ.comap Subtype.val)
    common rowsH realCutoffH evenAngleH L.fixedLaw representation.fixedParameters j R
      p.intermediate p.intermediate_generator
  let cm := contourParameters dm (p.intermediate.principal / R)
    (p.intermediate.weakRate / R) hprincipalH hweakH
  have physical (om : ProjectorOutputs p.intermediate.operator (weakEmbedding j) dm cm.cutoff cm.radius) :=
    PhysicalLayerUniversalScaleFactory.eventual_sources u holder mh K (σ.comap Subtype.val) rowsH noiseH L.fixedLaw
      representation.fixedParameters representation.fixedParameters_continuous j R p.intermediate
      p.intermediate_generator T G B hK hF w hw wc hwc hR hwR hwcR hweight common ordinary
      r t sn margins essentialH p.injectiveH p.compactH om cm.radius_subordinate cm.radius_leading
      cm.cutoff_pos cm.principal_lt realCutoffH evenAngleH a2
  have ratio (h : SmoothPhysicalTests.tests (E := E) K) :=
    KellerLiveraniMeasureStability.deterministic_multiplier_ratio
      ds dm i p.injectiveS (p.compatible 0) deterministicPressure
      (ConstructedRegularMultipliers.analyticMultiplier (coreLift mh.qa)
        (multiplier V ((common.coreData u holder mh K (σ.comap Subtype.val)).test h)
          ((common.coreData u holder mh K (σ.comap Subtype.val)).test_smooth h)))
  have projectedRatio (h : SmoothPhysicalTests.tests (E := E) K) :=
    congrArg Complex.re (ratio h)
  have equilibriumTrace (h : SmoothPhysicalTests.tests (E := E) K) :=
    (deterministicEquilibrium h).trans (projectedRatio h).symm
  have htrans : forwardTransitiveOn T (isolatedCore T K) := by simpa only [hΛ] using hHL.transitive
  have hcore : (isolatedCore T K).Nonempty := by simpa only [hΛ] using hHL.nonempty_core
  have consume := @RegularCoreLocalConsumer.consume
    ms.strongCarrier mh.strongCarrier W
    (PhysicalHolderClassicalSources.Regular u holder V) X E Parameters ι
    ms.strongCarrierNormed ms.strongCarrierScalar ms.strongCarrierComplete
    mh.strongCarrierNormed mh.strongCarrierScalar mh.strongCarrierComplete
    (inferInstance : NormedAddCommGroup W) (inferInstance : NormedSpace ℂ W)
    (inferInstance : CompleteSpace W)
    (inferInstance : NormedAddCommGroup (PhysicalHolderClassicalSources.Regular u holder V))
    (inferInstance : NormedSpace ℂ (PhysicalHolderClassicalSources.Regular u holder V))
    (inferInstance : MetricSpace X) (inferInstance : CompactSpace X)
    (inferInstance : MeasurableSpace X) (inferInstance : BorelSpace X)
    (inferInstance : SecondCountableTopology X)
    (inferInstance : NormedAddCommGroup E) (inferInstance : NormedSpace ℝ E)
    (inferInstance : FiniteDimensional ℝ E) (inferInstance : ChartedSpace E X)
    (inferInstance : IsManifold (𝓘(ℝ, E)) ∞ X)
    (inferInstance : RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x))
    (inferInstance : MetricSpace Parameters) (inferInstance : Fintype ι)
    mh.maps g Λ
  have result := consume V (⟨B, ordinary.retained_open⟩ : TopologicalSpace.Opens X)
    mh.regularCore ordinary.retained_live
    T V K G B hHL hΛ equilibrium φ hφ ordinary.live_open ordinary.live_subset hK
    ordinary.retained_open ordinary.core_retained ordinary.retained_live hBG ordinary.no_return
    (ordinary.core_retained.trans (subset_closure.trans hBG)) htrans hcore N L representation hF
    w hw hwG wc hwc R hR hwR hwcR i j p essentialS essentialH klS klH ds dm
    hprincipalS hweakS hprincipalH hweakH (SmoothPhysicalTests.tests (E := E) K)
    (SmoothPhysicalTests.dense K hK.isClosed)
    (fun h => ConstructedRegularMultipliers.analyticMultiplier (coreLift mh.qa)
      (multiplier V ((common.coreData u holder mh K (σ.comap Subtype.val)).test h)
        ((common.coreData u holder mh K (σ.comap Subtype.val)).test_smooth h)))
    deterministicPressure (fun ε => ⟨conjS ε⟩) (fun ε => ⟨conjH ε⟩) physical equilibriumTrace
  exact result

end ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalLocalStability
