module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualNoiseClosedLayer
public import ConditionedStochasticStabilityHyperbolic.Global.UniformNoFullSupportStrongFellerQuasiErgodic

/-! # Actual global closed-layer spectral/measure sources produced from KL

The full process, its closed restriction and the local analytic noise model
are identified by their actual kernels. Independent cited KL/noise/collar
sources construct the closed-layer raw gap and represented physical product.
Neither an operator identity nor an actual noisy spectral pair is assumed.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualProducedClosedLayerSource
open LeanShared LocalPositiveCollar Restriction ActualNoiseClosedLayer RestrictedLayerChain
open ComplexStrongFeller
open LeanShared.ControlledPlaqueClosure
variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

private theorem strongFeller_of_kernel_eq {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (C D : AbsorbingMarkovChains.CanonicalChain Y)
    (h : C.killedTransition = D.killedTransition) (hD : HasStrongFellerKernel D) :
    HasStrongFellerKernel C := by
  intro f hf hb
  have hc := hD f hf hb
  simpa only [h] using hc

omit [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] in
/-- The actual full-process kernel's smoothing property constructs the
literal local kernel's strong-Feller source. -/
theorem localStrongFeller
    (noise : Measure Ω) [IsProbabilityMeasure noise] (F : X × Ω → X) (hF : Measurable F)
    (Live K : Set X) (hLive : MeasurableSet Live) (hK : MeasurableSet K) (hKLive : K ⊆ Live)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hSF : HasStrongFellerKernel (NoiseKernel.chain noise F hF Live hLive w hw R hR hwR)) :
    HasStrongFellerKernel (RestrictedNoise.chain noise F hF K hK (fun x : K => w x.val)
      (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)) := by
  exact strongFeller_of_kernel_eq _ _
    (local_killedTransition_eq_global_layer noise F hF Live K hLive hK hKLive w hw R hR hwR)
    (strongFeller (NoiseKernel.chain noise F hF Live hLive w hw R hR hwR) hSF K hK)

private theorem exists_source_of_operator_eq {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    (P Q : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ)) (heq : P = Q)
    (a : ℝ) (Core Region : Set Y)
    (dl : RankOneSpectralData P (1 : Y →ᵇ ℝ)) (hrate : dl.rate = a) (hone : dl.mean 1 = 1)
    (μ : Measure Y) (hμ : IsFiniteMeasure μ)
    (hm : ∀ f, dl.mean f = ∫ y, f y ∂μ)
    (hloc : (eigenvectorMeasure μ dl.eigenvector).support ⊆ Region)
    (hpos : ∀ x ∈ Core, 0 < dl.eigenvector x)
    (hsupp : Core ⊆ (eigenvectorMeasure μ dl.eigenvector).support) :
    ∃ d : RankOneSpectralData Q (1 : Y →ᵇ ℝ), d.rate = a ∧ d.mean 1 = 1 ∧
      ∃ μ : Measure Y, IsFiniteMeasure μ ∧ (∀ f, d.mean f = ∫ y, f y ∂μ) ∧
        (eigenvectorMeasure μ d.eigenvector).support ⊆ Region ∧
        (∀ x ∈ Core, 0 < d.eigenvector x) ∧ Core ⊆ (eigenvectorMeasure μ d.eigenvector).support := by
  subst Q
  exact ⟨dl, hrate, hone, μ, hμ, hm, hloc, hpos, hsupp⟩

variable {E Weak Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup Weak] [NormedSpace ℂ Weak] [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem exists_uniform_noise_tolerance_for_actual_closed_layer_source
    (T : X ≃ₜ X) (Live V K G U : Set X) [CompactSpace K]
    (hLive : MeasurableSet Live) (hKLive : K ⊆ Live)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (w : X → ℝ) (hw : Measurable w) (hwK : Continuous (fun x : K => w x.val))
    (hwG : ∀ x : K, x.val ∈ G → 0 < w x.val)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (noise : Measure Ω) [IsProbabilityMeasure noise] [noise.IsOpenPosMeasure],
      ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardCollarPlaqueInputs T F V K G →
      let C := NoiseKernel.chain noise F hF Live hLive w hw R hR hwR
      ∀ hSF : HasStrongFellerKernel C,
      let Clocal := RestrictedNoise.chain noise F hF K hK.measurableSet (fun x : K => w x.val)
        (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)
      let sfLocal := localStrongFeller noise F hF Live K hLive hK.measurableSet hKLive w hw R hR hwR hSF
      ∀ s : KellerLiverani1999.StrongFellerSpectralInputs (E := E) (W := Weak) (Z := Z) Clocal sfLocal R,
      NoFullSupportCollarDensityCertificate.Inputs T V K G hK noise F hF (fun x : K => w x.val)
        (hw.comp measurable_subtype_coe) R δ →
      ∃ d : RankOneSpectralData (R • transferOperator (𝕜 := ℝ) (chain C K hK.measurableSet)
        (strongFeller C hSF K hK.measurableSet)) (1 : K →ᵇ ℝ),
        d.rate = s.analyticScale * (s.outputs.eigenvalue s.noiseParameter).re ∧ d.mean 1 = 1 ∧
      ∃ μ : Measure K, IsFiniteMeasure μ ∧
        (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) ∧
        (eigenvectorMeasure μ d.eigenvector).support ⊆ retainedRegion K U ∧
        (∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x) ∧
        ({x : K | x.val ∈ isolatedCore T K} ⊆ (eigenvectorMeasure μ d.eigenvector).support) := by
  obtain ⟨δ, hδ, hsource⟩ :=
    UniformNoFullSupportCollarQuasiErgodic.exists_uniform_noise_tolerance_for_strongFeller_produced_full_collar_package
      (E := E) (W := Weak) (Z := Z) (Ω := Ω) T V K G U hV hVK hK hU hcoreU hUV hUG hsep hcoreG
      htrans hcore (fun x : K => w x.val) hwK hwG R hR (fun x => hwR x.val)
  refine ⟨δ, hδ, ?_⟩
  intro noise _ _ F hF hclose hp
  dsimp only
  intro hSF s cert
  let sfLocal := localStrongFeller noise F hF Live K hLive hK.measurableSet hKLive w hw R hR hwR hSF
  obtain ⟨dl, hrate, hone, μ, hμ, hm, _hq, hloc, hpos, hsupp, _hunique, _hsimple, _hradius⟩ :=
    hsource noise F hF hclose hp sfLocal s cert
  let heq := raw_local_transfer_eq_global_layer noise F hF Live K hLive hK.measurableSet hKLive
    w hw R hR hwR hSF sfLocal
  exact exists_source_of_operator_eq _ _ heq _
    {x : K | x.val ∈ isolatedCore T K} (retainedRegion K U) dl hrate hone μ hμ hm hloc hpos hsupp

end ConditionedStochasticStabilityHyperbolic.Global.ActualProducedClosedLayerSource
