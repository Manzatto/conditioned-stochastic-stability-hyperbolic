module

public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportIntertwinedStability
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedPair
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniParameters
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicEquilibriumProduct
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Actual local stability without assuming a family-specific analytic
projector comparison. Completed transfer intertwining and the two KL power
limits construct that comparison, after shrinking their noise windows. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportProducedPairStability
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
theorem exists_actual_local_family_from_produced_pair
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
        Nonempty (NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
          T V K G hK (noise ε) (F ε) (hF ε) w hw wc hwc R hR hwR hwcR om ε η A M))
    (equilibriumIdentification : ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure K)) =
      (dm.mean (M h (i ds.vector)) / dm.mean (i ds.vector)).re) :
    ∃ (ν : ℝ≥0 → ProbabilityMeasure K) (r : ℝ≥0 → ℝ),
      Tendsto ν (𝓝[>] (0 : ℝ≥0)) (𝓝 ν₀) ∧
      Tendsto r (𝓝[>] (0 : ℝ≥0)) (𝓝 (R * dm.rate)) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        let C := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet
          w hw.measurable R hR hwR
        C.IsQuasiErgodic (ν ε : Measure K) ∧
        (ν ε : Measure K).support ⊆ retainedRegion K U ∧
        {x : K | x.val ∈ isolatedCore T K} ⊆ (ν ε : Measure K).support ∧
        (∀ ζ : Measure K, C.IsQuasiErgodic ζ →
          {x : K | x.val ∈ isolatedCore T K} ⊆ ζ.support → ζ = (ν ε : Measure K)) ∧
        0 < r ε ∧ ∃ hSF : HasStrongFellerKernel C,
          spectralRadius ℝ (R • strongFellerTransferOperator C hSF) = ENNReal.ofReal (r ε) := by
  let cs := contourParameters ds (p.strong.principal / R) (p.strong.weakRate / R) hprincipalS hweakS
  let cm := contourParameters dm (p.intermediate.principal / R) (p.intermediate.weakRate / R) hprincipalH hweakH
  have hv : ds.vector ≠ 0 := by
    intro hz
    have h := ds.normalization
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hwv : (outerWeak i j) (i ds.vector) ≠ 0 := by
    intro hz
    have hi0 : i ds.vector = 0 := (outerWeak_injective i j p.injectiveH)
      (hz.trans (map_zero _).symm)
    exact hv (p.injectiveS (hi0.trans (map_zero i).symm))
  obtain ⟨φ, _hφnorm, hφvalue⟩ := exists_dual_vector ℂ ((outerWeak i j) (i ds.vector))
    (norm_ne_zero_iff.mpr hwv)
  have hφ : φ ((outerWeak i j) (i ds.vector)) ≠ 0 := by
    intro hz
    have heq := hφvalue.symm.trans hz
    exact (norm_ne_zero_iff.mpr hwv) (Complex.ofReal_eq_zero.mp heq)
  apply NoFullSupportIntertwinedStability.exists_actual_local_family_from_intertwined_annealed_sources
    T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore noise hopen F hF
    w hw hwG wc hwc R hR hwR hwcR i j p.injectiveS p.compactS p.denseS p.injectiveH p.compactH
    p.strong p.intermediate essentialS essentialH klS klH ds dm cs.cutoff cs.radius cm.cutoff cm.radius
    cs.principal_lt cs.cutoff_lt_rate cs.cutoff_lt_weak cs.subordinate_lt cs.radius_pos
    cs.radius_subordinate cs.radius_leading cm.principal_lt cm.cutoff_lt_rate cm.cutoff_lt_weak
    cm.subordinate_lt cm.radius_pos cm.radius_subordinate cm.radius_leading cm.cutoff_pos
    φ hφ A hA M ν₀ deterministicPressure (Eventually.of_forall p.compatible)
    (Eventually.of_forall conjugationS) (Eventually.of_forall conjugationH) physicalSources
  intro os om h
  have hevent := eventually_projector_comparison_of_intertwining os om
    cs.radius_subordinate cs.radius_leading cs.cutoff_pos
    cm.radius_subordinate cm.radius_leading cm.cutoff_pos i p.injectiveS
    (by rw [deterministicPressure]; exact cm.cutoff_lt_rate)
    (Eventually.of_forall p.compatible) (Eventually.of_forall conjugationS) (Eventually.of_forall conjugationH)
  have hzero := mem_of_mem_nhds hevent
  rw [KellerLiveraniMeasureStability.realLeftTrace_zero_eq_normalized_product os om hzero φ hφ]
  exact equilibriumIdentification h

end ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportProducedPairStability
