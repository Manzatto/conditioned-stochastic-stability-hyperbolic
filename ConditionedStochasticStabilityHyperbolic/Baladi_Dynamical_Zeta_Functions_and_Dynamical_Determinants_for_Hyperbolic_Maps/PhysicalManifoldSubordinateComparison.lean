module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldCommonCoreComparison
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldSpectrumNormalization
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL
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
open Set MeasureTheory Filter
open scoped Topology
open scoped Manifold ContDiff BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSubordinateComparison
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999

private theorem eigenvector_from_facts {H Z Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : H →L[ℂ] H) (C : AbsorbingMarkovChains.CanonicalChain Y)
    (sf : HasStrongFellerKernel C) (R cutoff : ℝ)
    (a : H →L[ℂ] Z) (b : (Y →ᵇ ℂ) →L[ℂ] Z)
    (facts : CommonCoreSpectralFacts P C sf R cutoff a b)
    (f : Y →ᵇ ℂ) (hf : f ≠ 0) (z : ℂ)
    (he : (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf) f = z • f)
    (hz : cutoff < ‖z‖) : ∃ v : H, v ≠ 0 ∧ P v = z • v := by
  have heComplex : (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf) f) = z • f := by
    simpa only [smul_apply, Complex.coe_smul] using he
  obtain ⟨v, hv, hve, _⟩ := facts.ordinary f hf z heComplex hz
  exact ⟨v, hv, hve⟩

theorem eventually_individual_eigencomparison
    {E U M AtlasIndex Reg A Ω : Type*}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
      [MeasurableSpace U] [BorelSpace U]
      [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
      [CompactSpace M]
      [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
      {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
      [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
    
    {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
      (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
    
    
    [MetricSpace Ω]
    
    {Test TestCore : Type*}
      [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
      [AddCommGroup TestCore] [Module ℂ TestCore]
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
    (hVK : V ⊆ K) (hK : MeasurableSet K)
    (hF : ∀ ε, Measurable (fun z : M × Noise => m.maps (noise ε z.2) z.1))
    (wc : K → ℝ) (hwc : Measurable wc) (hwc0 : ∀ x, 0 ≤ wc x)
    (hR : 0 < R) (hwcR : ∀ x, wc x ≤ R)
    (hweight : ∀ x : K, m.weight x.val = wc x)
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
    (essential : EssentialRadiusContract (E := m.StrongSpace) (W := W))
    (injectivej : Function.Injective j) (compactj : IsCompactOperator j)
    (inverseWindow : ℝ≥0) (inverseWindow_positive : 0 < inverseWindow)
    (J : ∀ ε : ℝ≥0, 0 < ε → ε ≤ inverseWindow → Noise → Test →L[ℂ] Test)
    (measurableJ : ∀ ε (hp : 0 < ε) (hw : ε ≤ inverseWindow) v, AEStronglyMeasurable (fun z => J ε hp hw z v) (law ε))
    (MJ : ∀ ε : ℝ≥0, 0 < ε → ε ≤ inverseWindow → ℝ)
    (boundJ : ∀ ε (hp : 0 < ε) (hw : ε ≤ inverseWindow) z, ‖J ε hp hw z‖ ≤ MJ ε hp hw)
    (changeVariables : ∀ ε (hp : 0 < ε) (hw : ε ≤ inverseWindow) z f v,
      (∫ x, ActualCutoffAdjoint.raw K
        (fun p : M × Noise => m.maps (noise ε p.2) p.1) wc z f x * globalPhysical v x ∂σ) =
      ∫ x, f x * globalPhysical (J ε hp hw z v) x ∂σ)
    (ultra : StrongFellerSquareCompact.UltraFellerContract (X := K))
    (classical : CommonAmbientClassicalComparison.ClassicalContract (A := m.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K m.regularCore))
      (Z := Test →L[ℂ] ℂ) (Reg := Reg) (W := W)) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel (RestrictedNoise.chain (law ε)
        (fun z : M × Noise => m.maps (noise ε z.2) z.1) (hF ε) K hK wc hwc R hR hwcR),
      ∀ (f : K →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
        (R • ComplexStrongFeller.transferOperator (𝕜 := ℂ)
          (RestrictedNoise.chain (law ε)
            (fun p : M × Noise => m.maps (noise ε p.2) p.1) (hF ε) K hK wc hwc R hR hwcR) sf) f = z • f →
        inputs.principal < ‖z‖ → ∃ v : m.StrongSpace, v ≠ 0 ∧ ((R : ℂ) • inputs.operator ε) v = z • v := by
  have existence := exists_hypotheses_of_varying_noise_classical_radius
    essential law (fun _ => inferInstance) inputs.generator inputs.measurable j injectivej compactj
    inputs.window inputs.window_pos inputs.blockLength inputs.blockLength_pos
    inputs.principal inputs.weakRate inputs.weakOneStep inputs.operatorBound inputs.remainder R
    inputs.principal_pos inputs.principal_weak inputs.weakOneStep_nonneg inputs.weakOneStep_rate
    inputs.operatorBound_nonneg inputs.remainder_nonneg inputs.scale_ge_one inputs.principal_scale
    inputs.generator_bound inputs.weak_bound inputs.block_bound inputs.perturbation
  let h := Classical.choose existence
  have hα : h.alpha = inputs.principal / R := (Classical.choose_spec existence).1
  have hrα : R * h.alpha = inputs.principal :=
    (congrArg (fun x : ℝ => R * x) hα).trans (mul_div_cancel₀ _ hR.ne')
  have window : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ h.window :=
    ((gt_mem_nhds h.window_pos).mono fun _ he => he.le).filter_mono nhdsWithin_le_nhds
  filter_upwards [window, self_mem_nhdsWithin,
    (((gt_mem_nhds inverseWindow_positive) : {ε : ℝ≥0 | ε < inverseWindow} ∈ 𝓝 0).mono (fun _ he => he.le)).filter_mono nhdsWithin_le_nhds] with ε hε hp hw
  intro sf f hf z he hz
  have hdivide : h.alpha < ‖z‖ / R := (lt_div_iff₀ hR).mpr ((mul_comm h.alpha R).trans_lt (hrα.trans_lt hz))
  let cutoff := Classical.choose (exists_between hdivide)
  have hcutoff := (Classical.choose_spec (exists_between hdivide)).1
  have hcutz := (Classical.choose_spec (exists_between hdivide)).2
  have facts := PhysicalManifoldCommonCoreComparison.common_core_facts m rows n law noise hnoise
    j R inputs hgenerator K uniformConstant uniformBound hVK hK ε (hF ε) wc hwc hwc0
    hR hwcR hweight sf hKclosed hV hwSupport σ hpositive globalPhysical includeReg include_view
    qt denseTest aFull haFull smoothFull a smoothRestriction h compactj hε
    (J ε hp hw) (measurableJ ε hp hw) (MJ ε hp hw) (boundJ ε hp hw) (changeVariables ε hp hw) cutoff hcutoff ultra classical
  have hscaled : R * cutoff < ‖z‖ :=
    (mul_comm R cutoff).trans_lt ((lt_div_iff₀ hR).mp hcutz)
  have result := eigenvector_from_facts (H := m.StrongSpace) (Z := Reg →L[ℂ] ℂ) (Y := K)
    ((R : ℂ) • inputs.operator ε)
    (RestrictedNoise.chain (law ε) (fun p : M × Noise => m.maps (noise ε p.2) p.1)
      (hF ε) K hK wc hwc R hR hwcR) sf R (R * cutoff) a
    (SupportedRegularPairing.embedding σ (physicalRealization V K m.regularCore)) facts f hf z he hscaled
  let v := Classical.choose result
  refine ⟨v, (Classical.choose_spec result).1, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val (Classical.choose_spec result).2

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldSubordinateComparison
