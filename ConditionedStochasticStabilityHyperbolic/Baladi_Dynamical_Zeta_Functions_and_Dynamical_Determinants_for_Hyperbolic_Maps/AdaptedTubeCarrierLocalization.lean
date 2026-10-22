module
public import LeanShared.Dynamics.HyperbolicAdaptedOriginalModelTubes
public import LeanShared.Dynamics.HyperbolicAdaptedActualModelEquivalence
public import LeanShared.Dynamics.HyperbolicAdaptedNormalizedTubePartition
public import LeanShared.Geometry.LinearRechartedIdentity
public import LeanShared.Geometry.LinearRechartedAtlas
public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Geometry.FiniteSmoothCapturePartition

/-! The physical carrier's chart data on the adapted normalized tubes. The
genuine Euclidean model charts are the normalized tube charts themselves
(not merely charts equal to them), and the localization cutoffs are the
literal tube partition functions. Hence every local support set coincides,
by definition, with the sets used by the chart-pair two-norm bound. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeCarrierLocalization
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V₀ : Set M} {base : BasicData (E := E) T Λ V₀}
  {system : PatchSystem base} (atlas : ChartAtlas system)

/-- The linearly recharted Euclidean-model manifold structure. -/
abbrev charts : ChartedSpace system.EuclideanModel M :=
  LinearRechartedManifold.charts (M := M) atlas.originalModelEquiv

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem tubeChart_mem (j : atlas.NormalizedTubeIndex) :
    letI := charts atlas;
    atlas.normalizedTubeChart j ∈ maximalAtlas (𝓘(ℝ,system.EuclideanModel)) ∞ M := by
  let := charts atlas
  rw [← atlas.originalTubeChart_chartImage atlas.originalModelEquiv j]
  exact LinearRechartedManifold.chartImage_mem_maximal atlas.originalModelEquiv
    (atlas.originalTubeChart atlas.originalModelEquiv j)
    (atlas.originalTubeChart_mem_maximal atlas.originalModelEquiv j)

variable {radius : ℝ} {tubes : Finset atlas.NormalizedTubeIndex}
  (d : FiniteSmoothCapturePartition.Data (E := E) Λ
    (fun i : tubes => atlas.normalizedTube radius i.val))

/-- Localization on the normalized tube charts with the literal tube cutoffs. -/
def localization :
    letI := charts atlas;
    ConstructedManifoldLocalization.Data (fun j => atlas.normalizedTubeChart j) d.capture := by
  letI := charts atlas
  classical
  refine { indices := tubes
           cutoff := fun i x => (d.beta i x : ℂ)
           smooth := fun i => (Complex.ofRealCLM.contMDiff.comp (d.smooth i)).comp
             (LinearRechartedManifold.identity_backward (M := M) atlas.originalModelEquiv)
           support := ?_
           compact := fun i => HasCompactSupport.of_compactSpace _
           partition := ?_ }
  · intro i x hx
    exact (d.support i ((tsupport_comp_subset Complex.ofReal_zero (d.beta i)) hx)).1
  · intro x hx
    have actual := congrArg (fun r : ℝ => (r : ℂ)) (d.one x hx)
    simpa only [Complex.ofReal_sum, Complex.ofReal_one] using actual

omit [FiniteDimensional ℝ E] in
theorem localization_indices :
    letI := charts atlas; (localization atlas d).indices = tubes := rfl

omit [FiniteDimensional ℝ E] in
theorem localization_cutoff (i : tubes) (x : M) :
    letI := charts atlas; (localization atlas d).cutoff i x = (d.beta i x : ℂ) := rfl

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeCarrierLocalization
