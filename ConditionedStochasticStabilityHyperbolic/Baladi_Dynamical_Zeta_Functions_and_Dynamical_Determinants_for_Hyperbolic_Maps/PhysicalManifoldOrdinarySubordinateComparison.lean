module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldSubordinateComparison
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualInverseAdjointSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.InverseRegularNoiseContinuity
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
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldOrdinarySubordinateComparison
open LeanShared DyadicCompletion FiniteRegularTransferRealization
open SmoothSupportedManifoldCore KellerLiverani1999

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
    (testView : Test →ₗ[ℂ] (M → ℂ)) (testView_injective : Function.Injective testView)
    (physical_eq : ∀ v x, globalPhysical v x = testView v x.val)
    (H : ℝ≥0 → Noise → M → M) (weight : ℝ≥0 → M × Noise → ℝ)
    (inverseWindow : ℝ≥0) (inverseWindow_positive : 0 < inverseWindow)
    (inverseOrdinary : ∀ ε, 0 < ε → ε ≤ inverseWindow → InverseRegularTransfer.OrdinarySources testView (H ε) (weight ε))
    (inverse_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : Noise × M => H ε z.1 z.2))
    (inverse_weight_joint : ∀ ε, 0 < ε → ε ≤ inverseWindow → Continuous (fun z : Noise × M => weight ε (z.2, z.1)))
    (test_core_continuous : ∀ c, Continuous (testView (qt c)))
    (inverseExponent : ℝ) (inverseExponent_positive : 0 < inverseExponent)
    (inverseInterpolationConstant : ℝ≥0 → TestCore → Noise → ℝ)
    (inverseInterpolation : ∀ ε (hp : 0 < ε) (hw : ε ≤ inverseWindow) c a₀ a e, 0 ≤ e →
      (∀ x, ‖testView ((inverseOrdinary ε hp hw).operator testView_injective a (qt c)) x -
        testView ((inverseOrdinary ε hp hw).operator testView_injective a₀ (qt c)) x‖ ≤ e) →
      dist ((inverseOrdinary ε hp hw).operator testView_injective a (qt c))
        ((inverseOrdinary ε hp hw).operator testView_injective a₀ (qt c)) ≤
          inverseInterpolationConstant ε c a₀ * e ^ inverseExponent)
    (jacobian : ∀ ε, 0 < ε → ε ≤ inverseWindow → ∀ z (f : K →ᵇ ℂ) v,
      (∫ x, ActualCutoffAdjoint.raw K
        (fun y : M × Noise => m.maps (noise ε y.2) y.1) wc z f x * testView v x.val ∂σ) =
        ∫ x, f x * ((weight ε (x.val, z) : ℂ) * testView v (H ε z x.val)) ∂σ)
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
  let J := fun ε hp hw => (inverseOrdinary ε hp hw).operator testView_injective
  have coreMeasurable (ε) (hp : 0 < ε) (hw : ε ≤ inverseWindow) (c : TestCore) : AEStronglyMeasurable
      (fun z => J ε hp hw z (qt c)) (law ε) :=
    (InverseRegularTransfer.continuous_operator_core testView_injective (inverseOrdinary ε hp hw)
      qt (inverse_joint ε hp hw) (inverse_weight_joint ε hp hw) test_core_continuous
      inverseExponent inverseExponent_positive (inverseInterpolationConstant ε)
      (inverseInterpolation ε hp hw) c).aestronglyMeasurable
  have measurableJ (ε) (hp : 0 < ε) (hw : ε ≤ inverseWindow) := InverseRegularTransfer.operator_aestronglyMeasurable testView_injective
    (inverseOrdinary ε hp hw) (law ε) qt denseTest (coreMeasurable ε hp hw)
  have changeVariables (ε) (hp : 0 < ε) (hw : ε ≤ inverseWindow) := InverseRegularTransfer.changeVariables_of_jacobian testView_injective
    (inverseOrdinary ε hp hw) K (fun z : M × Noise => m.maps (noise ε z.2) z.1) wc σ
    globalPhysical physical_eq (jacobian ε hp hw)
  exact PhysicalManifoldSubordinateComparison.eventually_individual_eigencomparison m rows n
    law noise hnoise j R inputs hgenerator K uniformConstant uniformBound hVK hK hF wc hwc hwc0
    hR hwcR hweight hKclosed hV hwSupport σ hpositive globalPhysical includeReg include_view
    qt denseTest aFull haFull smoothFull a smoothRestriction essential injectivej compactj
    inverseWindow inverseWindow_positive J measurableJ (fun ε hp hw => (inverseOrdinary ε hp hw).bound)
    (fun ε hp hw => (inverseOrdinary ε hp hw).operator_norm_le testView_injective) changeVariables ultra classical

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldOrdinarySubordinateComparison
