module

public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportProducedPairStability
public import ConditionedStochasticStabilityHyperbolic.Paper.UniformLocalGapAttachment
public import ConditionedStochasticStabilityHyperbolic.Paper.HLRepresentedConclusion

/-! Retain normalized rank-one gaps for the already chosen local family,
using the actual scale-source producer and a law-uniform geometry threshold.
This feeds stabilization descent without introducing a spectral premise. -/

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

theorem eventual_gaps_of_nofull_sources_and_qem_family
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
      let C := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet w hw.measurable R hR hwR
      ∃ sf : HasStrongFellerKernel C,
      ∃ d : RankOneSpectralData (strongFellerTransferOperator C sf) (1 : K →ᵇ ℝ),
        (ν ε : Measure K) = eigenvectorMeasure
          (d.eigenmeasure (fun f hf x => by
            rw [strongFellerTransferOperator_represents]
            exact integral_nonneg hf)) d.eigenvector ∧
        ∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x := by
  obtain ⟨η, hη, attach⟩ := exists_uniform_noise_tolerance_for_gap_attachment
    (E := H) (W := W) (Z := Zret) (Ω := Ω)
    T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore w hw hwG R hR hwR
  filter_upwards [properties, sources η hη, self_mem_nhdsWithin] with ε hp hs hε
  obtain ⟨s⟩ := hs
  let _ := hopen ε hε
  let C := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet w hw.measurable R hR hwR
  let D := RestrictedNoise.chain (noise ε) (F ε) (hF ε) K hK.measurableSet wc hwc R hR hwcR
  let produced := s.sameCutoff.originalInputs o hδsub hδlead hq ε D C s.cutoffSF s.originalSF R hR
  exact ⟨s.originalSF,
    attach (noise ε) (F ε) (hF ε) s.close s.plaques s.originalSF produced (ν ε) hp.1 hp.2.1⟩

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
end
