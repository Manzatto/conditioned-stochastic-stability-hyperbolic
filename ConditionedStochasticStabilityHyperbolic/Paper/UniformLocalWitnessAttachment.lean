module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalWitnessAttachment
public import ConditionedStochasticStabilityHyperbolic.Spectral.UniformCollarChainQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFellerSpectralInputs

/-! A uniform geometric threshold attaches the full spectral witness to the
already chosen weakly convergent QEM family. The gap and core positivity are
produced internally; no family re-selection or additional weak-limit proof
is needed. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
open LeanShared LocalPositiveCollar Restriction LeanShared.ControlledPlaqueClosure
variable {E W Z X Ω : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

theorem exists_uniform_noise_tolerance_for_witness_attachment
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
      (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ z, dist (F (x, z)) (T x) < δ) →
      ForwardCollarPlaqueInputs T F V K G →
      let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw.measurable R hR hwR
      ∀ (sf : HasStrongFellerKernel C),
      KellerLiverani1999.StrongFellerSpectralInputs (E := E) (W := W) (Z := Z) C sf R →
      ∀ ν : ProbabilityMeasure K, C.IsQuasiErgodic (ν : Measure K) →
      {x : K | x.val ∈ isolatedCore T K} ⊆ (ν : Measure K).support →
      Nonempty (SpectralWitness C R ν) := by
  obtain ⟨δ, hδ, hlocal⟩ := UniformLocalCollarQuasiErgodic.exists_uniform_noise_tolerance_for_collar_chain_package
    (Ω := Ω) T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore w hw hwG R hR hwR
  refine ⟨δ, hδ, ?_⟩
  intro ρ _ _ F hF hclose plaques
  dsimp only
  intro sf source ν hν hsupp
  obtain ⟨d, _hrate, _hone⟩ := source.exists_gap
  obtain ⟨_μ, _hμ, _hm, _hq, _hloc, hpositive, _hunique, _hsimple⟩ :=
    hlocal ρ F hF hclose plaques sf d
  let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw.measurable R hR hwR
  have hnonneg : ∀ f : K →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ (R • strongFellerTransferOperator C sf) f x := by
    intro f hf x
    change 0 ≤ R * (strongFellerTransferOperator C sf f x)
    rw [strongFellerTransferOperator_represents]
    exact mul_nonneg hR.le (integral_nonneg hf)
  have hne : ({x : K | x.val ∈ isolatedCore T K} : Set K).Nonempty := by
    obtain ⟨x, hx⟩ := hcore
    exact ⟨⟨x, forwardTrapped_subset T K hx.1⟩, hx⟩
  exact ⟨SpectralWitness.of_core_positive_rankOne C R hR sf d hnonneg _ hne hpositive ν hν hsupp⟩

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
