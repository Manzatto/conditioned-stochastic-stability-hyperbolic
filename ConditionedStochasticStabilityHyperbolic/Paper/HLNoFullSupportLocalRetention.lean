module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLNoFullSupportLocalStability
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalProducedGaps
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapRetention

/-! Literal local stochastic stability with gap retention from the produced analytic pair and
the no-full-support physical sources (thm:local and thm:qem-local, consumer form). The same
sources give, for every family of literal QEM points, the normalized spectral gap (retention). -/

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

set_option maxHeartbeats 1600000 in
theorem stability_and_gapRetention_from_produced_pair
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
      (fun x => φ x - Real.log (hHL.basic.hyperbolic.unstableJacobian x)) ∧
    LocalConclusions.GapRetention N L K Λ hK.measurableSet w hw.measurable R hR hwR := by
  have stability := stability_from_produced_pair T V K G U hHL hΛ e φ hφ hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore N L
    representation hF w hw hwG wc hwc R hR hwR hwcR i j p essentialS essentialH klS klH ds dm
    hprincipalS hweakS hprincipalH hweakH A hA M deterministicPressure conjugationS conjugationH
    physicalSources equilibriumIdentification
  have retain : LocalConclusions.GapRetention N L K Λ hK.measurableSet w hw.measurable R hR hwR := by
    intro ν points
    let cm := contourParameters dm _ _ hprincipalH hweakH
    obtain ⟨om⟩ := p.intermediate.exists_projector_outputs essentialH klH p.injectiveH p.compactH
      dm cm.cutoff cm.radius cm.principal_lt cm.cutoff_lt_rate cm.cutoff_lt_weak
      cm.subordinate_lt cm.radius_pos cm.radius_subordinate cm.radius_leading
    have pointsFixed := LocalConclusions.eventual_represented_points_of_literal N L K Λ
      hK.measurableSet w hw.measurable R hR hwR representation hF ν points
    have properties : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        let C := RestrictedNoise.chain (L.fixedLaw ε)
          (fun z : X × RegularNoise.FixedControl (ι := ι) =>
            evaluate (representation.fixedParameters ε z.2) z.1)
          (hF ε) K hK.measurableSet w hw.measurable R hR hwR
        C.IsQuasiErgodic (ν ε : Measure K) ∧
          {x : K | x.val ∈ isolatedCore T K} ⊆ (ν ε : Measure K).support ∧
          (∀ ζ : Measure K, C.IsQuasiErgodic ζ →
            {x : K | x.val ∈ isolatedCore T K} ⊆ ζ.support → ζ = (ν ε : Measure K)) := by
      filter_upwards [pointsFixed] with ε hp
      simpa only [hΛ] using And.intro hp.1 (And.intro hp.2.1 hp.2.2.1)
    have gaps := LocalConclusions.eventual_gaps_of_nofull_sources_and_qem_family
      T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore
      L.fixedLaw L.fixedLaw_full_support
      (fun ε (z : X × RegularNoise.FixedControl (ι := ι)) =>
        evaluate (representation.fixedParameters ε z.2) z.1) hF
      w hw hwG wc hwc R hR hwR hwcR om cm.radius_subordinate cm.radius_leading cm.cutoff_pos
      A M (physicalSources om) ν properties
    apply LocalConclusions.eventual_gaps_of_represented N L K Λ hK.measurableSet
      w hw.measurable R hR hwR representation hF ν
    simpa only [hΛ, LocalConclusions.NormalizedGap, Set.mem_ofPred_eq] using gaps
  exact ⟨stability, retain⟩

end ConditionedStochasticStabilityHyperbolic.Paper.HLNoFullSupportProducedLocalStability
