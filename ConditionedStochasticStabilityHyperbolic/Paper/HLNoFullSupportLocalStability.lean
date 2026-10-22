module

public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportProducedPairStability
public import ConditionedStochasticStabilityHyperbolic.Paper.UniformLocalWitnessAttachment
public import ConditionedStochasticStabilityHyperbolic.Paper.HLRepresentedConclusion

/-! Literal local stochastic stability from the produced analytic pair and
actual physical sources. The reference measure is required to support the
core, permitting closed live regions with volume-null boundary pieces.
The same weakly convergent family receives the complete spectral witness;
no leading gap, probability product or measure convergence is supplied. -/

public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared Restriction LocalPositiveCollar KellerLiverani1999
open LeanShared.ControlledPlaqueClosure
variable {H W Z Zret Core X Ω : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

theorem eventual_points_of_nofull_sources_and_qem_family
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (noise : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (noise ε)]
    (hopen : ∀ ε : ℝ≥0, 0 < ε → (noise ε).IsOpenPosMeasure)
    (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    {P : ℝ≥0 → H →L[ℂ] H} {j : H →L[ℂ] W} {det : DeterministicLeading (P 0)} {q δ : ℝ}
    (o : ProjectorOutputs P j det q δ)
    (hδsub : δ < q - det.subordinate) (hδlead : δ < det.rate - q) (hq : 0 < q)
    (A : Set (K →ᵇ ℝ)) (M : A → H →L[ℂ] H)
    (sources : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Nonempty (Global.NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
        T V K G hK (noise ε) (F ε) (hF ε) w hw wc hwc R hR hwR hwcR o ε η A M))
    (ν : ℝ≥0 → ProbabilityMeasure K)
    (properties : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      let C := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet w hw.measurable R hR hwR
      C.IsQuasiErgodic (ν ε : Measure K) ∧
      {x : K | x.val ∈ isolatedCore T K} ⊆ (ν ε : Measure K).support ∧
      (∀ ζ : Measure K, C.IsQuasiErgodic ζ →
        {x : K | x.val ∈ isolatedCore T K} ⊆ ζ.support → ζ = (ν ε : Measure K))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Point (RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet w hw.measurable R hR hwR)
        R {x : K | x.val ∈ isolatedCore T K} (ν ε) := by
  obtain ⟨η, hη, attach⟩ := exists_uniform_noise_tolerance_for_witness_attachment
    (E := H) (W := W) (Z := Zret) (Ω := Ω)
    T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore w hw hwG R hR hwR
  filter_upwards [properties, sources η hη, self_mem_nhdsWithin] with ε hp hs hε
  obtain ⟨s⟩ := hs
  let _ := hopen ε hε
  let C := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet w hw.measurable R hR hwR
  let D := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet wc hwc R hR hwcR
  let produced := s.sameCutoff.originalInputs o hδsub hδlead hq ε D C s.cutoffSF s.originalSF R hR
  exact ⟨hp.1, hp.2.1, hp.2.2,
    attach (noise ε) (F ε) (hF ε) s.close s.plaques s.originalSF produced (ν ε) hp.1 hp.2.1⟩

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions

end

public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NoFullSupportProducedLocalStability
open LeanShared Restriction KellerLiverani1999 KellerLiveraniMeasureStability
open LocalActualAnnealedStability
open LeanShared.ControlledPlaqueClosure LeanShared.TwoNormNormalization

variable {S H W Z Zret Core X Ω : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

set_option maxHeartbeats 800000 in
theorem exists_actual_point_family_from_produced_pair
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (noise : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (noise ε)]
    (hopen : ∀ ε : ℝ≥0, 0 < ε → (noise ε).IsOpenPosMeasure)
    (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (i : S →L[ℂ] H) (j : H →L[ℂ] W)
    {genS : ℝ≥0 → Ω → S →L[ℂ] S} {genH : ℝ≥0 → Ω → H →L[ℂ] H}
    (p : ProducedAnnealedPair.Data i j noise (fun _ => inferInstance) genS genH R)
    (essentialS : EssentialRadiusContract (E := S) (W := W))
    (essentialH : EssentialRadiusContract (E := H) (W := W))
    (klS : ClassicalContract (E := S) (W := W))
    (klH : ClassicalContract (E := H) (W := W))
    (ds : DeterministicLeading (p.strong.operator 0)) (dm : DeterministicLeading (p.intermediate.operator 0))
    (hprincipalS : p.strong.principal / R < ds.rate)
    (hweakS : ds.rate ≤ p.strong.weakRate / R)
    (hprincipalH : p.intermediate.principal / R < dm.rate)
    (hweakH : dm.rate ≤ p.intermediate.weakRate / R)
    (A : Set (K →ᵇ ℝ)) (hA : Dense A) (M : A → H →L[ℂ] H) (ν₀ : ProbabilityMeasure K)
    (deterministicPressure : ds.rate = dm.rate)
    (conjugationS : ∀ ε, Nonempty (RealOperatorConjugation (p.strong.operator ε)))
    (conjugationH : ∀ ε, Nonempty (RealOperatorConjugation (p.intermediate.operator ε)))
    (physicalSources :
      ∀ om : ProjectorOutputs p.intermediate.operator (weakEmbedding j) dm
        (contourParameters dm _ _ hprincipalH hweakH).cutoff
        (contourParameters dm _ _ hprincipalH hweakH).radius,
      ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        Nonempty (Global.NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
          T V K G hK (noise ε) (F ε) (hF ε) w hw wc hwc R hR hwR hwcR om ε η A M))
    (equilibriumIdentification : ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure K)) =
      (dm.mean (M h (i ds.vector)) / dm.mean (i ds.vector)).re) :
    ∃ ν : ℝ≥0 → ProbabilityMeasure K,
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        LocalConclusions.Point
          (RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet w hw.measurable R hR hwR)
          R {x : K | x.val ∈ isolatedCore T K} (ν ε) := by
  obtain ⟨ν, _rate, hlimit, _rateLimit, hp⟩ :=
    Global.NoFullSupportProducedPairStability.exists_actual_local_family_from_produced_pair
      T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore noise hopen F hF
      w hw hwG wc hwc R hR hwR hwcR i j p essentialS essentialH klS klH ds dm
      hprincipalS hweakS hprincipalH hweakH A hA M ν₀ deterministicPressure
      conjugationS conjugationH physicalSources equilibriumIdentification
  let cm := contourParameters dm (p.intermediate.principal / R) (p.intermediate.weakRate / R)
    hprincipalH hweakH
  obtain ⟨om⟩ := p.intermediate.exists_projector_outputs essentialH klH p.injectiveH p.compactH
    dm cm.cutoff cm.radius cm.principal_lt cm.cutoff_lt_rate cm.cutoff_lt_weak
    cm.subordinate_lt cm.radius_pos cm.radius_subordinate cm.radius_leading
  refine ⟨ν, hlimit, ?_⟩
  apply LocalConclusions.eventual_points_of_nofull_sources_and_qem_family
    T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore noise hopen F hF
    w hw hwG wc hwc R hR hwR hwcR om cm.radius_subordinate cm.radius_leading cm.cutoff_pos
    A M (physicalSources om) ν
  exact hp.mono (fun _ h => ⟨h.1, h.2.2.1, h.2.2.2.1⟩)

end ConditionedStochasticStabilityHyperbolic.Paper.NoFullSupportProducedLocalStability

end

public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Bundle IsManifold
open scoped Topology NNReal BoundedContinuousFunction Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLNoFullSupportProducedLocalStability
open LeanShared Restriction KellerLiverani1999 KellerLiveraniMeasureStability
open LocalActualAnnealedStability
open LeanShared.ControlledPlaqueClosure LeanShared.TwoNormNormalization

variable {S H W Z Zret Core X E Parameters ι : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MetricSpace Parameters] [Fintype ι]
  {evaluate : Parameters → X → X} {g : X → ℝ} {Λ : Set X}

set_option maxHeartbeats 800000 in
theorem stability_from_produced_pair
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hHL : HL (E := E) T g Λ V)
    (hΛ : isolatedCore T K = Λ)
    (e : HyperbolicBasicSet.EquilibriumPackage hHL.basic.hyperbolic g)
    (φ : X → ℝ) (hφ : ∀ x ∈ Λ, g x = Real.exp (φ x))
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (N : RegularNoise.Maps (E := E) (ι := ι) T hHL.r) (L : RegularNoise.Laws (ι := ι))
    (representation : RegularNoise.Representation N Parameters evaluate)
    (hF : ∀ ε : ℝ≥0, Measurable (fun z : X × RegularNoise.FixedControl (ι := ι) =>
      evaluate (representation.fixedParameters ε z.2) z.1))
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (i : S →L[ℂ] H) (j : H →L[ℂ] W)
    {genS : ℝ≥0 → RegularNoise.FixedControl (ι := ι) → S →L[ℂ] S} {genH : ℝ≥0 → RegularNoise.FixedControl (ι := ι) → H →L[ℂ] H}
    (p : ProducedAnnealedPair.Data i j L.fixedLaw (fun _ => inferInstance) genS genH R)
    (essentialS : EssentialRadiusContract (E := S) (W := W))
    (essentialH : EssentialRadiusContract (E := H) (W := W))
    (klS : ClassicalContract (E := S) (W := W))
    (klH : ClassicalContract (E := H) (W := W))
    (ds : DeterministicLeading (p.strong.operator 0)) (dm : DeterministicLeading (p.intermediate.operator 0))
    (hprincipalS : p.strong.principal / R < ds.rate)
    (hweakS : ds.rate ≤ p.strong.weakRate / R)
    (hprincipalH : p.intermediate.principal / R < dm.rate)
    (hweakH : dm.rate ≤ p.intermediate.weakRate / R)
    (A : Set (K →ᵇ ℝ)) (hA : Dense A) (M : A → H →L[ℂ] H) 
    (deterministicPressure : ds.rate = dm.rate)
    (conjugationS : ∀ ε, Nonempty (RealOperatorConjugation (p.strong.operator ε)))
    (conjugationH : ∀ ε, Nonempty (RealOperatorConjugation (p.intermediate.operator ε)))
    (physicalSources :
      ∀ om : ProjectorOutputs p.intermediate.operator (weakEmbedding j) dm
        (contourParameters dm _ _ hprincipalH hweakH).cutoff
        (contourParameters dm _ _ hprincipalH hweakH).radius,
      ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        Nonempty (Global.NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
          T V K G hK (L.fixedLaw ε) ((fun z : X × RegularNoise.FixedControl (ι := ι) => evaluate (representation.fixedParameters ε z.2) z.1)) (hF ε) w hw wc hwc R hR hwR hwcR om ε η A M))
    (equilibriumIdentification : ∀ h : A, (∫ x, h.val x ∂(hHL.stateOnCollar e K hK.measurableSet (by rw [← hΛ]; exact hcoreU.trans ((subset_closure.trans hUV).trans hVK)) : Measure K)) =
      (dm.mean (M h (i ds.vector)) / dm.mean (i ds.vector)).re) :
    LocalConclusions.Stability N L K Λ hK.measurableSet w hw.measurable R hR hwR
      (fun x => φ x - Real.log (hHL.basic.hyperbolic.unstableJacobian x)) := by
  have hΛK : Λ ⊆ K := by
    rw [← hΛ]
    exact hcoreU.trans ((subset_closure.trans hUV).trans hVK)
  let ν₀ := hHL.stateOnCollar e K hK.measurableSet hΛK
  obtain ⟨ν, limit, points⟩ := NoFullSupportProducedLocalStability.exists_actual_point_family_from_produced_pair
    T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore L.fixedLaw
    L.fixedLaw_full_support
    (fun ε z => evaluate (representation.fixedParameters ε z.2) z.1) hF
    w hw hwG wc hwc R hR hwR hwcR i j p essentialS essentialH klS klH ds dm
    hprincipalS hweakS hprincipalH hweakH A hA M ν₀ deterministicPressure
    conjugationS conjugationH physicalSources equilibriumIdentification
  apply LocalConclusions.stability_of_hl_represented_points hHL e N L K hK.measurableSet hΛK
    w hw.measurable R hR hwR representation hF φ hφ ν limit
  simpa only [hΛ] using points

end ConditionedStochasticStabilityHyperbolic.Paper.HLNoFullSupportProducedLocalStability

end
