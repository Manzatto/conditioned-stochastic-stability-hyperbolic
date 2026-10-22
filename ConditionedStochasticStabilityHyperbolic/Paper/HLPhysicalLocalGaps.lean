module

import all ConditionedStochasticStabilityHyperbolic.Paper.RegularCoreGapConsumer

public import ConditionedStochasticStabilityHyperbolic.Paper.HLNoFullSupportLocalStability
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalLayerUniversalScaleFactory
public import LeanShared.Geometry.SmoothHolderNormedParents
public import LeanShared.Analysis.SubmoduleNormedSpaceParent
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierComplete
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerNoiseSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicPairTrace
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderAnnealedConjugation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldRealStructure

/-! Retain actual normalized power gaps for the SAME constructed QEM family. Actual analytic inputs
and ordinary physical sources produce the projector and scale packets internally; no noisy gap
or product is a source. -/
public noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalLocalGaps
open LeanShared DyadicCompletion SmoothSupportedManifoldCore KellerLiverani1999
open LeanShared.ControlledPlaqueClosure LeanShared.TwoNormNormalization
open PhysicalHolderClassicalSources.SourceData

universe uX

private theorem gaps_from_classical_physical_sources
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
    (rowsH : PhysicalManifoldRowSources.Data mh)
    (noiseH : PhysicalManifoldNoiseSources.Data mh)
    (σ : Measure X) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (common : PhysicalHolderClassicalSources.Data u holder mh K (σ.comap Subtype.val))
    (ordinarySource : RegularLayerNoiseSources.Data representation σ V K G B hK w wc R
      (fullView u holder) (fullView_injective u holder) (fullCore u holder))
    (submersion : RegularNoise.ControlSubmersionSources (E := E) (ι := ι) σ)
    (hBG : closure B ⊆ G)
    (r t sn : ℝ) (margins : RegularCoreApproximation.RegularityMargins r t sn u)
    (essentialH : EssentialRadiusContract (E := mh.StrongSpace) (W := W))
    (klH : ClassicalContract (E := mh.StrongSpace) (W := W))
    (dm : DeterministicLeading (p.intermediate.operator 0))
    (hprincipalH : p.intermediate.principal / R < dm.rate)
    (hweakH : dm.rate ≤ p.intermediate.weakRate / R)
    (realCutoffH : ∀ a x, conj (mh.localization.cutoff a x) = mh.localization.cutoff a x)
    (evenAngleH : ∀ a ξ, (mh.angle a).toFun (-ξ) = (mh.angle a).toFun ξ)
    (a2 : ∀ {Z : Type uX} [NormedAddCommGroup Z] [NormedSpace ℂ Z],
      CommonAmbientClassicalComparison.ClassicalContract (A := mh.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K mh.regularCore))
      (Z := Z)
      (Reg := PhysicalHolderClassicalSources.Regular u holder V) (W := W))
    (ν : ℝ≥0 → ProbabilityMeasure K)
    (points : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      LocalConclusions.PointAt N L K Λ hK.measurableSet w hw.measurable R hR hwR (ν ε) ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      LocalConclusions.NormalizedGapAt N L K Λ hK.measurableSet w hw.measurable R hR hwR (ν ε) ε := by
  let ordinary := ordinarySource.produce submersion L hw hwc hR hwR hwcR hF
  let cm := contourParameters dm (p.intermediate.principal / R)
    (p.intermediate.weakRate / R) hprincipalH hweakH
  obtain ⟨om⟩ := p.intermediate.exists_projector_outputs essentialH klH p.injectiveH p.compactH dm
    cm.cutoff cm.radius cm.principal_lt cm.cutoff_lt_rate cm.cutoff_lt_weak
    cm.subordinate_lt cm.radius_pos cm.radius_subordinate cm.radius_leading
  have physical :=
    PhysicalLayerUniversalScaleFactory.eventual_sources u holder mh K (σ.comap Subtype.val) rowsH noiseH L.fixedLaw
      representation.fixedParameters representation.fixedParameters_continuous j R p.intermediate
      p.intermediate_generator T G B hK hF w hw wc hwc hR hwR hwcR hweight common ordinary
      r t sn margins essentialH p.injectiveH p.compactH om cm.radius_subordinate cm.radius_leading
      cm.cutoff_pos cm.principal_lt realCutoffH evenAngleH a2
  have htrans : forwardTransitiveOn T (isolatedCore T K) := by simpa only [hΛ] using hHL.transitive
  have hcore : (isolatedCore T K).Nonempty := by simpa only [hΛ] using hHL.nonempty_core
  have pointsFixed := LocalConclusions.eventual_represented_points_of_literal N L K Λ
    hK.measurableSet w hw.measurable R hR hwR representation hF ν points
  have properties : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      let C := RestrictedNoise.chain (L.fixedLaw ε)
        (fun z : X × RegularNoise.FixedControl (ι := ι) =>
          mh.maps (representation.fixedParameters ε z.2) z.1)
        (hF ε) K hK.measurableSet w hw.measurable R hR hwR
      C.IsQuasiErgodic (ν ε : Measure K) ∧
        {x : K | x.val ∈ isolatedCore T K} ⊆ (ν ε : Measure K).support ∧
        (∀ ζ : Measure K, C.IsQuasiErgodic ζ →
          {x : K | x.val ∈ isolatedCore T K} ⊆ ζ.support → ζ = (ν ε : Measure K)) := by
    filter_upwards [pointsFixed] with ε hp
    simpa only [hΛ] using And.intro hp.1 (And.intro hp.2.1 hp.2.2.1)
  have consume := @RegularCoreGapConsumer.consume
    mh.strongCarrier W (PhysicalHolderClassicalSources.Regular u holder V) X E
    (RegularNoise.FixedControl (ι := ι))
    mh.strongCarrierNormed mh.strongCarrierScalar mh.strongCarrierComplete
    (inferInstance : NormedAddCommGroup W) (inferInstance : NormedSpace ℂ W)
    (inferInstance : NormedAddCommGroup (PhysicalHolderClassicalSources.Regular u holder V))
    (inferInstance : NormedSpace ℂ (PhysicalHolderClassicalSources.Regular u holder V))
    (inferInstance : MetricSpace X) (inferInstance : CompactSpace X)
    (inferInstance : MeasurableSpace X) (inferInstance : BorelSpace X)
    (inferInstance : SecondCountableTopology X)
    (inferInstance : NormedAddCommGroup E) (inferInstance : NormedSpace ℝ E)
    (inferInstance : ChartedSpace E X)
    (inferInstance : TopologicalSpace (RegularNoise.FixedControl (ι := ι)))
    (inferInstance : CompactSpace (RegularNoise.FixedControl (ι := ι)))
    (inferInstance : MeasurableSpace (RegularNoise.FixedControl (ι := ι)))
  have result := consume V (⟨B, ordinary.retained_open⟩ : TopologicalSpace.Opens X)
    mh.regularCore ordinary.retained_live
    T V K G B ordinary.live_open ordinary.live_subset hK
    ordinary.retained_open ordinary.core_retained ordinary.retained_live hBG ordinary.no_return
    (ordinary.core_retained.trans (subset_closure.trans hBG)) htrans hcore
    L.fixedLaw (fun ε hε => L.fixedLaw_full_support ε hε)
    (fun ε (z : X × RegularNoise.FixedControl (ι := ι)) =>
      mh.maps (representation.fixedParameters ε z.2) z.1) hF
    w hw hwG wc hwc R hR hwR hwcR om cm.radius_subordinate cm.radius_leading cm.cutoff_pos
    (SmoothPhysicalTests.tests (E := E) K)
    (fun h => ConstructedRegularMultipliers.analyticMultiplier (coreLift mh.qa)
      (multiplier V ((common.coreData u holder mh K (σ.comap Subtype.val)).test h)
        ((common.coreData u holder mh K (σ.comap Subtype.val)).test_smooth h)))
    physical ν properties
  apply LocalConclusions.eventual_gaps_of_represented N L K Λ hK.measurableSet
    w hw.measurable R hR hwR representation hF ν
  simpa only [hΛ, LocalConclusions.NormalizedGap, Set.mem_ofPred_eq] using result

end ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalLocalGaps
