module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.LayerNoiseClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldOriginalSubordinateComparison
public import LeanShared.Analysis.CommonAmbientGlobalTests
public import LeanShared.Analysis.DualNormedSpaceParent

/-! Ordinary cited anisotropic facts over the actual supported/full little
Hölder spaces. All regular realizations, dense cores, test inclusions and
physical compatibility identities are constructed, not source fields. -/

public noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 100000
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalLayerUniversalEigenFactory
open LeanShared DyadicCompletion SmoothSupportedManifoldCore

universe uM
variable {M : Type uM} {E U AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)

abbrev Regular (V : Set M) := PhysicalHolderClassicalSources.Regular u holder V
abbrev FullTest := PhysicalHolderClassicalSources.FullTest u holder


variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Regular u holder V) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (σ : Measure K) [IsFiniteMeasure σ]


open KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
variable [MetricSpace Ω]


-- Keep the actual all-z output inferred from the already checked source
-- application; only declaration style is exempted, not kernel checking.
set_option linter.defProp false in
def eventual_original_eigenvectors
    (rows : PhysicalManifoldRowSources.Data m) (n : PhysicalManifoldNoiseSources.Data m)
    {Noise W : Type*} [TopologicalSpace Noise] [CompactSpace Noise] [MeasurableSpace Noise]
    [OpensMeasurableSpace Noise] [SecondCountableTopology Noise]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (law : ℝ≥0 → Measure Noise) [∀ ε, IsProbabilityMeasure (law ε)]
    (noise : ℝ≥0 → Noise → Ω) (hnoise : ∀ ε, Continuous (noise ε))
    (j : m.StrongSpace →L[ℂ] W) (R : ℝ)
    (inputs : ActualAnnealedInputs law (fun _ => inferInstance) j R)
    (hgenerator : ∀ ε z, inputs.generator ε z = m.generator (noise ε z))
    (T : M ≃ₜ M) (G B : Set M) (hK : IsCompact K)
    (hF : ∀ ε, Measurable (fun z : M × Noise => m.maps (noise ε z.2) z.1))
    (w : K → ℝ) (hw : Continuous w) (wc : K → ℝ) (hwc : Measurable wc)
    (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (hweight : ∀ x : K, m.weight x.val = wc x)
    (common : PhysicalHolderClassicalSources.Data u holder m K σ)
    (ordinary : LayerNoiseClassicalSources.Data T V K G B hK law
      (fun ε (z : M × Noise) => m.maps (noise ε z.2) z.1) hF
      w hw wc hwc R hR hwR hwcR σ
      (fullView u holder) (fullView_injective u holder) (fullCore u holder))
    (essential : EssentialRadiusContract (E := m.StrongSpace) (W := W))
    (injectivej : Function.Injective j) (compactj : IsCompactOperator j)
    (classical : ∀ {Z : Type uM} [NormedAddCommGroup Z] [NormedSpace ℂ Z],
      CommonAmbientClassicalComparison.ClassicalContract (A := m.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K m.regularCore))
      (Z := Z) (Reg := Regular u holder V) (W := W)) :=
  let window : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ ordinary.smoothingWindow :=
    ((gt_mem_nhds ordinary.smoothingWindow_positive).mono (fun _ he => he.le)).filter_mono nhdsWithin_le_nhds
  let cutoffSF : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel
      (RestrictedNoise.chain (law ε) (fun z : M × Noise => m.maps (noise ε z.2) z.1)
        (hF ε) K hK.measurableSet wc hwc R hR hwcR) := by
    filter_upwards [self_mem_nhdsWithin, window] with ε hε hwnd
    exact ordinary.cutoffSF ε hε hwnd
  PhysicalManifoldOriginalSubordinateComparison.eventually_individual_eigencomparison
    m rows n law noise hnoise j R inputs hgenerator K
    (common.coreData u holder m K σ).uniformConstant (common.coreData u holder m K σ).uniformBound
    ordinary.live_subset hK.measurableSet hF wc hwc ordinary.cutoff_nonnegative hR hwcR hweight
    hK.isClosed ordinary.live_open ordinary.cutoff_support σ ordinary.reference_positive
    (globalPhysical u holder K) (includeReg u holder) (common.include_view u holder m K σ)
    (fullCore u holder) (fullCore_dense u holder) common.fullEmbedding common.fullEmbedding_injective
    (common.smoothFull u holder m K σ) (common.coreData u holder m K σ).embedding
    (common.smoothRestriction u holder m K σ) essential injectivej compactj
    (fullView u holder) (fullView_injective u holder) (physical_eq u holder K)
    ordinary.inverseMap ordinary.inverseWeight ordinary.inverseWindow ordinary.inverseWindow_positive ordinary.inverseRegular ordinary.inverse_joint
    ordinary.inverse_weight_joint ordinary.smooth_continuous ordinary.inverseExponent
    ordinary.inverseExponent_positive ordinary.inverseInterpolationConstant ordinary.inverse_interpolation
    ordinary.jacobian T B ordinary.retained_open ordinary.core_retained
    (ordinary.retained_live.trans ordinary.live_subset) ordinary.no_return
    w hw.measurable hwR (fun x hx => (ordinary.weight_agreement x hx).symm)
    ordinary.close cutoffSF ordinary.ultra (@classical (FullTest u holder →L[ℂ] ℂ) ContinuousLinearMap.toNormedAddCommGroup
      DualNormedSpaceParent.normedSpace)

end ConditionedStochasticStabilityHyperbolic.PhysicalLayerUniversalEigenFactory
