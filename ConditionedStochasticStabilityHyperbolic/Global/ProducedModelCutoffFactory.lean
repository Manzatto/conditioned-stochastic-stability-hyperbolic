module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedModel
public import ConditionedStochasticStabilityHyperbolic.Spectral.UniformSameCutoffSources

/-! # Actual produced manifold models supply dominant physical sources

The model bundle is an OUTPUT of PhysicalManifoldPrimitiveSources.actualModel.
Its actual finite-block bounds and proved compact weak inclusion construct KL
projectors. Uniform geometric localization constructs every retained-kernel
certificate; only SAME-cutoff ordinary/generalized/reverse comparisons remain
classical source facts. No noisy projector, physical gap, eigenfunction lift,
compact inclusion or retained extinction certificate is an independent input.
-/
@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ProducedModelCutoffFactory
open KellerLiverani1999 Restriction LeanShared
variable {E H W Z Zret X Ξ Ω : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSpace Ξ] [MeasurableSpace Ω]

theorem exists_actual_dominant_sources_of_produced_model
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
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) [CompactSpace K] (hU : IsOpen U)
    (hcore : isolatedCore T K ⊆ U) (hUK : closure U ⊆ K)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U) :
    ∃ o : ProjectorOutputs model.inputs.operator (LeanShared.TwoNormNormalization.weakEmbedding iW)
        deterministic q δ,
      ∃ η : ℝ, 0 < η ∧ ∀ (ρ : Measure Ω) [IsProbabilityMeasure ρ]
        (F : X × Ω → X) (hF : Measurable F),
        (∀ x ∈ K, ∀ z, dist (F (x, z)) (T x) < η) →
        ∀ (w wc : K → ℝ) (hw : Measurable w) (hwc : Measurable wc)
        (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R),
        (∀ x : K, x.val ∈ closure U → wc x = w x) →
        let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw R hR hwR
        let D := RestrictedNoise.chain ρ F hF K hK.measurableSet wc hwc R hR hwcR
        ∀ (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D) (ε : NNReal),
        ClassicalSameCutoffComparisons (Z := Z) (Zret := Zret)
          o ε D hD R (retainedRegion K U) →
        ∃ inputs : StrongFellerSpectralInputs (E := E) (W := W) (Z := Zret) C hC R,
          inputs.analytic = model.inputs.operator ∧ inputs.analyticScale = R ∧ inputs.noiseParameter = ε ∧
            inputs.analyticScale * (inputs.outputs.eigenvalue inputs.noiseParameter).re = R * (o.eigenvalue ε).re := by
  obtain ⟨o⟩ := model.inputs.exists_projector_outputs essential kl model.injectiveW model.compactW
    deterministic q δ hαq hqr hqweak hsubq hδ hδsub hδlead
  obtain ⟨η, hη, hsources⟩ := exists_uniform_same_cutoff_sources
    (E := E) (W := W) (Z := Z) (Zret := Zret) (Ω := Ω)
    T K U hK hU hcore hUK hsep
  refine ⟨o, η, hη, ?_⟩
  intro ρ _ F hF hclose w wc hw hwc hwR hwcR hagree
  dsimp only
  intro hC hD ε comparison
  obtain ⟨source⟩ := hsources ρ F hF hclose w wc hw hwc R hR hwR hwcR hagree hC hD o ε comparison
  refine ⟨source.originalInputs o hδsub hδlead hq ε _ _ hD hC R hR, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

end ConditionedStochasticStabilityHyperbolic.Global.ProducedModelCutoffFactory
