module

public import ConditionedStochasticStabilityHyperbolic.Global.ProducedModelCutoffFactory
public import ConditionedStochasticStabilityHyperbolic.Global.ActualProducedClosedLayerSource

/-! # Constructing actual closed-layer gap and measure from the produced model

Actual finite-block/compactness inputs construct analytic projectors; geometric
localization constructs retained certificates; classical same-cutoff comparison
and the independent bounded-noise density/plaque inputs then construct the
actual closed-layer physical data consumed by the final global application.
No noisy local or global spectral pair, QEM or growth bound is supplied.
-/
@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ProducedModelClosedLayerFactory
open KellerLiverani1999 Restriction LeanShared LocalPositiveCollar LeanShared.ControlledPlaqueClosure
open ComplexStrongFeller RestrictedLayerChain ProducedModelCutoffFactory
variable {E H W Z Zret X Ξ Ω : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSpace Ξ]
  [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

theorem exists_actual_closed_layer_data_of_produced_model
    (iH : E →L[ℂ] H) (iW : E →L[ℂ] W)
    (law : NNReal → Measure Ξ) (prob : ∀ ε, IsProbabilityMeasure (law ε))
    (generator : NNReal → Ξ → E →L[ℂ] E) (R : ℝ)
    (model : ProducedAnnealedModel.Data iH iW law prob generator R)
    (essential : EssentialRadiusContract (E := E) (W := W))
    (kl : ClassicalContract (E := E) (W := W))
    (deterministic : DeterministicLeading (model.inputs.operator 0)) (q δ : ℝ)
    (hαq : model.inputs.principal / R < q) (hqr : q < deterministic.rate)
    (hqweak : q < model.inputs.weakRate / R) (hsubq : deterministic.subordinate < q)
    (hδ : 0 < δ) (hδsub : δ < q - deterministic.subordinate)
    (hδlead : δ < deterministic.rate - q) (hq : 0 < q) (hR : 0 < R)
    (T : X ≃ₜ X) (Live V K G U : Set X) [CompactSpace K]
    (hLive : MeasurableSet Live) (hKLive : K ⊆ Live)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (w : X → ℝ) (hw : Measurable w) (hwK : Continuous (fun x : K => w x.val))
    (hwG : ∀ x : K, x.val ∈ G → 0 < w x.val) (hwR : ∀ x, w x ≤ R) :
    ∃ o : ProjectorOutputs model.inputs.operator (LeanShared.TwoNormNormalization.weakEmbedding iW)
        deterministic q δ,
      ∃ η ζ : ℝ, 0 < η ∧ 0 < ζ ∧
        ∀ (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
        (F : X × Ω → X) (hF : Measurable F),
        (∀ x ∈ K, ∀ z, dist (F (x, z)) (T x) < η) →
        ForwardCollarPlaqueInputs T F V K G →
        ∀ (wc : K → ℝ) (hwc : Measurable wc) (hwcR : ∀ x, wc x ≤ R),
        (∀ x : K, x.val ∈ closure U → wc x = w x.val) →
        let C := NoiseKernel.chain ρ F hF Live hLive w hw R hR hwR
        ∀ hSF : HasStrongFellerKernel C,
        let D := RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc R hR hwcR
        ∀ (hD : HasStrongFellerKernel D) (ε : NNReal),
        ClassicalSameCutoffComparisons (Z := Z) (Zret := Zret) o ε D hD R (retainedRegion K U) →
        NoFullSupportCollarDensityCertificate.Inputs T V K G hK ρ F hF
          (fun x : K => w x.val) (hw.comp measurable_subtype_coe) R ζ →
        ∃ d : RankOneSpectralData (R • transferOperator (𝕜 := ℝ)
          (chain C K hK.measurableSet) (strongFeller C hSF K hK.measurableSet)) (1 : K →ᵇ ℝ),
          d.rate = R * (o.eigenvalue ε).re ∧ d.mean 1 = 1 ∧
          ∃ μ : Measure K, IsFiniteMeasure μ ∧
            (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) ∧
            (eigenvectorMeasure μ d.eigenvector).support ⊆ retainedRegion K U ∧
            (∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x) ∧
            ({x : K | x.val ∈ isolatedCore T K} ⊆ (eigenvectorMeasure μ d.eigenvector).support) := by
  obtain ⟨o, η, hη, hspectral⟩ := exists_actual_dominant_sources_of_produced_model
    (Z := Z) (Zret := Zret) (Ω := Ω) iH iW law prob generator R model essential kl
    deterministic q δ hαq hqr hqweak hsubq hδ hδsub hδlead hq hR
    T K U hK hU hcoreU (hUV.trans hVK) hsep
  obtain ⟨ζ, hζ, hphysical⟩ := ActualProducedClosedLayerSource.exists_uniform_noise_tolerance_for_actual_closed_layer_source
    (E := E) (Weak := W) (Z := Zret) (Ω := Ω) T Live V K G U hLive hKLive hV hVK hK hU
    hcoreU hUV hUG hsep hcoreG htrans hcore w hw hwK hwG R hR hwR
  refine ⟨o, min η ζ, ζ, lt_min hη hζ, hζ, ?_⟩
  intro ρ _ _ F hF hclose hplaques wc hwc hwcR hagree
  dsimp only
  intro hSF hD ε comparison certificate
  let hC := ActualProducedClosedLayerSource.localStrongFeller ρ F hF Live K hLive hK.measurableSet
    hKLive w hw R hR hwR hSF
  obtain ⟨inputs, hinputs⟩ := hspectral ρ F hF
    (fun x hx z => (hclose x hx z).trans_le (min_le_left _ _))
    (fun x : K => w x.val) wc (hw.comp measurable_subtype_coe) hwc
    (fun x => hwR x.val) hwcR hagree hC hD ε comparison
  obtain ⟨d, hrate, hone, μ, hμ, hm, hlocal, hpos, hsupp⟩ := hphysical ρ F hF
    (fun x hx z => (hclose x hx z).trans_le (min_le_right _ _)) hplaques hSF inputs certificate
  exact ⟨d, hrate.trans hinputs.2.2.2, hone, μ, hμ, hm, hlocal, hpos, hsupp⟩

end ConditionedStochasticStabilityHyperbolic.Global.ProducedModelClosedLayerFactory
