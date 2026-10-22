module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldForwardCommonCore
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualCutoffCommonCoreFacts
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualCutoffAdjoint
public import ConditionedStochasticStabilityHyperbolic.Spectral.SupportedCommonCoreFacts

/-! Appendix A.2 comparison from the actual physical manifold model.
The regular average, both completed forward identities, inverse averaged
duality, supported Banach core and raw power bounds are all constructed.
Only ordinary full-test distribution/Jacobian facts and the universal
classical functional-analysis contracts remain source inputs. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldCommonCoreComparison
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)


variable [MetricSpace Ω]

variable {Test TestCore : Type*}
  [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
  [AddCommGroup TestCore] [Module ℂ TestCore]

set_option synthInstance.maxHeartbeats 400000 in
omit [SecondCountableTopology M] [T2Space M] in
theorem common_core_facts
    (rows : PhysicalManifoldRowSources.Data m) (n : PhysicalManifoldNoiseSources.Data m)
    {Noise W : Type*} [TopologicalSpace Noise] [MeasurableSpace Noise]
    [OpensMeasurableSpace Noise] [SecondCountableTopology Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise : ℝ≥0 → Noise → Ω) (hnoise : ∀ ε, Continuous (noise ε))
    (j : m.StrongSpace →L[ℂ] W) (R : ℝ)
    (inputs : ActualAnnealedInputs law (fun _ => inferInstance) j R)
    (hgenerator : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    (K : Set M) [CompactSpace K]
    (uniformConstant : ℝ)
    (uniformBound : ∀ c, ‖physicalCore V K c‖ ≤ uniformConstant * ‖m.regularCore c‖)
    (hVK : V ⊆ K) (hK : MeasurableSet K) (ε : ℝ≥0)
    (hF : Measurable (fun z : M × Noise => m.maps (noise ε z.2) z.1))
    (wc : K → ℝ) (hwc : Measurable wc) (hwc0 : ∀ x, 0 ≤ wc x)
    (hR : 0 < R) (hwcR : ∀ x, wc x ≤ R)
    (hweight : ∀ x : K, m.weight x.val = wc x)
    (sf : HasStrongFellerKernel (RestrictedNoise.chain (law ε)
      (fun z : M × Noise => m.maps (noise ε z.2) z.1) hF K hK wc hwc R hR hwcR))
    (hKclosed : IsClosed K) (hV : IsOpen V)
    (hwSupport : tsupport wc ⊆ {x : K | x.val ∈ V})
    (σ : Measure K) [IsFiniteMeasure σ]
    (hpositive : {x : K | x.val ∈ V} ⊆ σ.support)
    (globalPhysical : Test →L[ℂ] (K →ᵇ ℂ))
    (includeReg : Reg →L[ℂ] Test)
    (include_view : ∀ v, globalPhysical (includeReg v) = physicalRealization V K m.regularCore v)
    (qt : TestCore →ₗ[ℂ] Test) (denseTest : DenseRange qt)
    (aFull : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (haFull : Function.Injective aFull)
    (smoothFull : ∀ c d, aFull (coreLift m.qa c) (qt d) =
      ∫ x, physicalCore V K c x * globalPhysical (qt d) x ∂σ)
    (a : m.StrongSpace →L[ℂ] (Reg →L[ℂ] ℂ))
    (smoothRestriction : ∀ c d, aFull (coreLift m.qa c) (includeReg (m.regularCore d)) =
      a (coreLift m.qa c) (m.regularCore d))
    (h : Hypotheses inputs.operator (TwoNormNormalization.weakEmbedding j))
    (compactj : IsCompactOperator j)
    (hε : ε ≤ h.window)
    (J : Noise → Test →L[ℂ] Test)
    (measurableJ : ∀ v, AEStronglyMeasurable (fun z => J z v) (law ε))
    (MJ : ℝ) (boundJ : ∀ z, ‖J z‖ ≤ MJ)
    (changeVariables : ∀ z f v,
      (∫ x, ActualCutoffAdjoint.raw K
        (fun p : M × Noise => m.maps (noise ε p.2) p.1) wc z f x * globalPhysical v x ∂σ) =
      ∫ x, f x * globalPhysical (J z v) x ∂σ)
    (cutoff : ℝ) (hcutoff : h.alpha < cutoff)
    (ultra : StrongFellerSquareCompact.UltraFellerContract (X := K))
    (classical : CommonAmbientClassicalComparison.ClassicalContract (A := m.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K m.regularCore))
      (Z := Test →L[ℂ] ℂ) (Reg := Reg) (W := W)) :
    CommonCoreSpectralFacts ((R : ℂ) • inputs.operator ε)
      (RestrictedNoise.chain (law ε)
        (fun z : M × Noise => m.maps (noise ε z.2) z.1) hF K hK wc hwc R hR hwcR)
      sf R (R * cutoff) a (SupportedRegularPairing.embedding σ (physicalRealization V K m.regularCore)) := by
  have producedForward :=
    PhysicalManifoldForwardCommonCore.exists_forward m rows n law noise hnoise j R inputs
      hgenerator K uniformConstant uniformBound hVK hK ε hF wc hwc hwc0 hR hwcR hweight sf
  let forward := Classical.choose producedForward
  have analytic_intertwining := (Classical.choose_spec producedForward).1
  have physical_intertwining := (Classical.choose_spec producedForward).2
  have analytic_core (c : PhysicalManifoldModel.Core (E := E) V) :
      ((R : ℂ) • inputs.operator ε) (coreLift m.qa c) = m.realize (forward (m.regularCore c)) := by
    have hh := congrArg (fun L : Reg →L[ℂ] m.StrongSpace => L (m.regularCore c)) analytic_intertwining
    exact (congrArg (((R : ℂ) • inputs.operator ε)) (m.realize_core c)).symm.trans hh.symm
  have physical_forward (v : Reg) :=
    congrArg (fun L : Reg →L[ℂ] (K →ᵇ ℂ) => L v) physical_intertwining
  have adjoint := ActualCutoffAdjoint.pairing_intertwining K hK
    (fun z : M × Noise => m.maps (noise ε z.2) z.1) hF wc hwc (law ε) R hR hwcR sf
    hwc0 σ globalPhysical J measurableJ MJ boundJ changeVariables
  have facts := ActualCutoffCommonCoreFacts.from_actual_cutoff_and_KL hKclosed hV
    m.regularCore m.regularCore_dense (coreLift m.qa) (coreLift_dense m.qa)
    m.realize m.realize_core (physicalRealization V K m.regularCore)
    (physicalRealization_core V K m.regularCore m.regularCore_dense uniformConstant uniformBound)
    σ hpositive globalPhysical includeReg include_view qt denseTest aFull haFull smoothFull
    inputs.operator (TwoNormNormalization.weakEmbedding j) h
    (TwoNormNormalization.weakEmbedding_isCompact j compactj) ε hε R hR (law ε)
    (fun z : M × Noise => m.maps (noise ε z.2) z.1) hF wc hwc hwcR sf hwSupport
    forward (AnnealedOperatorBounds.pointwiseAnnealed (law ε) J measurableJ MJ boundJ)
    analytic_core physical_forward adjoint cutoff hcutoff ultra classical
  exact CommonCoreSpectralFacts.restrict_global_tests _ _ sf R (R * cutoff) σ
    (coreLift m.qa) (coreLift_dense m.qa) m.regularCore m.regularCore_dense includeReg
    (physicalRealization V K m.regularCore) globalPhysical include_view aFull a smoothRestriction facts

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldCommonCoreComparison
