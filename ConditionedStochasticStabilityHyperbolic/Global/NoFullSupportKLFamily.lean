module

public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLPointwise
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniInvariantCoreStability

/-! One positive-noise family satisfies the actual local QEM conclusions
and converges weakly. Noise laws may vary arbitrarily with the scale. The
geometric tolerance is selected before the laws; smoothing and submersion
sources are used only at positive scales. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLFamily
open LeanShared Restriction KellerLiverani1999 LocalPositiveCollar
open LeanShared.ControlledPlaqueClosure KellerLiveraniMeasureStability

variable {S H W Vweak Z Zret Core X Ω : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Vweak] [NormedSpace ℂ Vweak]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

structure ScaleSources
    (T : X ≃ₜ X) (V K G : Set X) (hK : IsCompact K) [CompactSpace K]
    (noise : Measure Ω) [IsProbabilityMeasure noise]
    (F : X × Ω → X) (hF : Measurable F)
    (w : K → ℝ) (hw : Continuous w) (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    {P : ℝ≥0 → H →L[ℂ] H} {weak : H →L[ℂ] Vweak}
    {det : DeterministicLeading (P 0)} {q δ : ℝ}
    (o : ProjectorOutputs P weak det q δ) (ε : ℝ≥0) (η : ℝ)
    (A : Set (K →ᵇ ℝ)) (M : A → H →L[ℂ] H) where
  close : ∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < η
  plaques : ForwardCollarPlaqueInputs T F V K G
  originalSF : HasStrongFellerKernel
    (RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR)
  cutoffSF : HasStrongFellerKernel
    (RestrictedNoise.chain noise F hF K hK.measurableSet wc hwc R hR hwcR)
  sameCutoff : SameCutoffClassicalSources (Z := Z) (Zret := Zret) o ε
    (RestrictedNoise.chain noise F hF K hK.measurableSet wc hwc R hR hwcR)
    (RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR)
    cutoffSF originalSF R
  inverse : NoFullSupportCollarDensityCertificate.Inputs T V K G hK noise F hF w hw.measurable R η
  core : ∀ (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ)
      (RestrictedNoise.chain noise F hF K hK.measurableSet wc hwc R hR hwcR) cutoffSF)
      (1 : K →ᵇ ℝ)) (μcut : Measure K) [IsFiniteMeasure μcut],
    (∀ f : K →ᵇ ℝ, dc.mean f = ∫ x, f x ∂μcut) →
    Nonempty (LocalKLPointwise.SupportedCoreSources (Z := Z) (Core := Core)
      (o.projection ε) (((o.eigenvalue ε).re : ℂ)⁻¹ • P ε)
      (RestrictedNoise.chain noise F hF K hK.measurableSet wc hwc R hR hwcR) cutoffSF dc μcut wc A M)

set_option maxHeartbeats 800000 in
theorem exists_actual_local_qem_family_with_weak_limit
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
    {Ps : ℝ≥0 → S →L[ℂ] S} {Pm : ℝ≥0 → H →L[ℂ] H}
    {i : S →L[ℂ] H} {j : H →L[ℂ] W} {jm : H →L[ℂ] Vweak}
    {ds : DeterministicLeading (Ps 0)} {dm : DeterministicLeading (Pm 0)}
    {qs δs qm δm : ℝ}
    (os : ProjectorOutputs Ps (j.comp i) ds qs δs)
    (om : ProjectorOutputs Pm jm dm qm δm)
    (hδsub : δm < qm - dm.subordinate) (hδlead : δm < dm.rate - qm) (hqm : 0 < qm)
    (hi : IsCompactOperator i) (hj : Function.Injective j) (hdense : DenseRange i)
    (hagree : ∀ ε ≤ min os.window om.window,
      (om.projection ε).comp i = i.comp (os.projection ε))
    (φ : W →L[ℂ] ℂ) (hφ : φ (j (i ds.vector)) ≠ 0)
    (A : Set (K →ᵇ ℝ)) (hA : Dense A) (M : A → H →L[ℂ] H)
    (ν₀ : ProbabilityMeasure K)
    (hsources : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      Nonempty (ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
        T V K G hK (noise ε) (F ε) (hF ε) w hw wc hwc R hR hwR hwcR om ε η A M))
    (hequilibrium : ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure K)) =
      realLeftTrace os om φ 0 (M h (i ds.vector))) :
    ∃ ν : ℝ≥0 → ProbabilityMeasure K,
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        let C := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet
          w hw.measurable R hR hwR
        C.IsQuasiErgodic (ν ε : Measure K) ∧
        (ν ε : Measure K).support ⊆ retainedRegion K U ∧
        {x : K | x.val ∈ isolatedCore T K} ⊆ (ν ε : Measure K).support ∧
        (∀ ζ : Measure K, C.IsQuasiErgodic ζ →
          {x : K | x.val ∈ isolatedCore T K} ⊆ ζ.support → ζ = (ν ε : Measure K)) := by
  classical
  obtain ⟨η, hη, hpoint⟩ := NoFullSupportKLPointwise.exists_uniform_pointwise_local_pairing_package
    (H := H) (W := Vweak) (Z := Z) (Zret := Zret) (Core := Core) (Ω := Ω)
    T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore w hw hwG R hR hwR
  let C := fun ε => RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet
    w hw.measurable R hR hwR
  let Property := fun (ε : ℝ≥0) (ν : ProbabilityMeasure K) =>
    (C ε).IsQuasiErgodic (ν : Measure K) ∧
    (ν : Measure K).support ⊆ retainedRegion K U ∧
    {x : K | x.val ∈ isolatedCore T K} ⊆ (ν : Measure K).support ∧
    (∀ ζ : Measure K, (C ε).IsQuasiErgodic ζ →
      {x : K | x.val ∈ isolatedCore T K} ⊆ ζ.support → ζ = (ν : Measure K)) ∧
    Nonempty (InvariantPhysicalPairing.Inputs (Z := Z) (Core := Core)
      (om.projection ε) (((om.eigenvalue ε).re : ℂ)⁻¹ • Pm ε)
      (rightBranch os i ε) ν A M)
  have hex : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ∃ ν : ProbabilityMeasure K, Property ε ν := by
    filter_upwards [hsources η hη, self_mem_nhdsWithin,
      (eventually_projector_eq_leftTrace os om hagree φ hφ).filter_mono nhdsWithin_le_nhds]
      with ε hs hε hPa
    obtain ⟨s⟩ := hs
    let : (noise ε).IsOpenPosMeasure := hopen ε hε
    exact hpoint (noise ε) (F ε) (hF ε) s.close s.plaques wc hwc hwcR
      s.originalSF s.cutoffSF om hδsub hδlead hqm ε s.sameCutoff s.inverse
      (rightBranch os i ε) (leftTrace os om φ ε) hPa A M s.core
  let ν : ℝ≥0 → ProbabilityMeasure K := fun ε =>
    if h : ∃ μ : ProbabilityMeasure K, Property ε μ then h.choose else ν₀
  have hproperty : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), Property ε (ν ε) := by
    filter_upwards [hex] with ε hε
    simp only [ν, dite_eq_left hε]
    exact hε.choose_spec
  have hconj : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), Nonempty (RealOperatorConjugation (Pm ε)) := by
    filter_upwards [hsources η hη] with ε hε
    obtain ⟨s⟩ := hε
    exact ⟨s.sameCutoff.conjugation⟩
  refine ⟨ν, ?_, ?_⟩
  · exact KellerLiveraniPhysicalStability.tendsto_actual_probability_from_invariant_core
      os om hδsub hδlead hqm hi hj hdense hagree φ hφ A hA M ν ν₀ hconj
      (hproperty.mono fun _ h => h.2.2.2.2) hequilibrium
  · exact hproperty.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLFamily
