module

public import ConditionedStochasticStabilityHyperbolic.Global.UniformNoFullSupportCollarQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFellerSpectralInputs

/-! # The full literal local QEM package from KL and cited strong-Feller inputs

The actual normalized spectral gap, leading measure, full measurable-observable
QEM, core support, qualified uniqueness and radius are constructed. Inputs are
explicit classical spectral/noise/geometric source facts and the analytic KL
outputs; no actual noisy right/left pair or power gap is supplied.
Pointwise density continuity and C0 regularity upgrades are unnecessary.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.UniformNoFullSupportCollarQuasiErgodic
open LeanShared LocalPositiveCollar Restriction
open LeanShared.ControlledPlaqueClosure

variable {E W Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

theorem exists_uniform_noise_tolerance_for_strongFeller_produced_full_collar_package
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (noise : Measure Ω) [IsProbabilityMeasure noise] [noise.IsOpenPosMeasure],
      ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardCollarPlaqueInputs T F V K G →
      let C := RestrictedNoise.chain noise F hF K hK.measurableSet w hw.measurable R hR hwR
      ∀ (hSF : HasStrongFellerKernel C),
      let P := R • strongFellerTransferOperator C hSF
      ∀ s : KellerLiverani1999.StrongFellerSpectralInputs (E := E) (W := W) (Z := Z) C hSF R,
      NoFullSupportCollarDensityCertificate.Inputs T V K G hK noise F hF w hw.measurable R δ →
      ∃ d : RankOneSpectralData P (1 : K →ᵇ ℝ),
        d.rate = s.analyticScale * (s.outputs.eigenvalue s.noiseParameter).re ∧ d.mean 1 = 1 ∧
      ∃ ν : Measure K, IsFiniteMeasure ν ∧
        (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂ν) ∧
        C.IsQuasiErgodic (eigenvectorMeasure ν d.eigenvector) ∧
        (eigenvectorMeasure ν d.eigenvector).support ⊆ retainedRegion K U ∧
        (∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x) ∧
        ({x : K | x.val ∈ isolatedCore T K} ⊆ (eigenvectorMeasure ν d.eigenvector).support) ∧
        (∀ η : Measure K, C.IsQuasiErgodic η →
          {x : K | x.val ∈ isolatedCore T K} ⊆ η.support → η = eigenvectorMeasure ν d.eigenvector) ∧
        (∀ v : K →ᵇ ℝ, P v = d.rate • v → v = d.mean v • d.eigenvector) ∧
        spectralRadius ℝ P = ENNReal.ofReal d.rate := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_noise_tolerance_for_full_collar_chain_package
    (Ω := Ω) T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG htrans hcore w hw hwG R hR hwR
  refine ⟨δ, hδ, ?_⟩
  intro noise _ _ F hF hclose hp
  dsimp only
  intro hSF s c
  obtain ⟨d, hrate, hone⟩ := s.exists_gap
  exact ⟨d, hrate, hone, hlocal noise F hF hclose hp hSF d c⟩

end ConditionedStochasticStabilityHyperbolic.Global.UniformNoFullSupportCollarQuasiErgodic
