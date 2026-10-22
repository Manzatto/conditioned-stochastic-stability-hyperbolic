module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanProjection
public import LeanShared.Geometry.CenteredTangentJacobianComparison
public import LeanShared.Analysis.ConjugateProjectionRanks

/-! The normalized field is the literal encoding of the constructed native
projection, including its continuity, idempotence and actual kernel plane. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem PatchSystem.normalizedProjection_continuousOn (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) : ContinuousOn (system.normalizedProjection c x)
      (b.hyperbolic.normedAdaptedProjection.collar ∩ (chartAt E c.val).source) := by
  let p := b.hyperbolic.normedAdaptedProjection
  let e := trivializationAt E (TangentSpace (𝓘(ℝ,E))) c.val
  have raw := BundleEndomorphismCoordinates.continuousOn_coordinates
    (TangentSpace (𝓘(ℝ,E))) e p.projection p.collar p.continuous_action
  have actual : ContinuousOn
      (BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E))) e p.projection)
      (p.collar ∩ (chartAt E c.val).source) := by
    simpa only [e,TangentChartTrivialization.baseSet] using raw
  exact continuousOn_const.clm_comp (actual.clm_comp continuousOn_const)

theorem PatchSystem.normalizedProjection_encoding (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) (y : M) (inside : y∈(chartAt E c.val).source)
    (v : TangentSpace (𝓘(ℝ,E)) y) :
    let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val.val x.property.2
      (system.euclideanReferenceFrame c x)
    let A := CenteredTangentJacobianComparison.encoding (chartAt E c.val)
      (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) y inside L
    A (b.hyperbolic.normedAdaptedProjection.projection y v) = system.normalizedProjection c x y (A v) := by
  dsimp only
  let e := trivializationAt E (TangentSpace (𝓘(ℝ,E))) c.val
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val.val x.property.2
    (system.euclideanReferenceFrame c x)
  let A := CenteredTangentJacobianComparison.encoding (chartAt E c.val)
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) y inside L
  have base : y∈e.baseSet := by rw [TangentChartTrivialization.baseSet]; exact inside
  have encoded (w : TangentSpace (𝓘(ℝ,E)) y) : A w=L.symm (e.continuousLinearMapAt ℝ y w) := by
    rw [TangentChartTrivialization.forward inside]
    rfl
  change A (b.hyperbolic.normedAdaptedProjection.projection y v) = system.normalizedProjection c x y (A v)
  rw [encoded,encoded]
  change L.symm (e.continuousLinearMapAt ℝ y (b.hyperbolic.normedAdaptedProjection.projection y v)) =
    L.symm (e.continuousLinearMapAt ℝ y (b.hyperbolic.normedAdaptedProjection.projection y
      (e.symmL ℝ y (L (L.symm (e.continuousLinearMapAt ℝ y v))))))
  rw [L.apply_symm_apply,e.symmL_continuousLinearMapAt base]

theorem PatchSystem.normalizedProjection_idempotent (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) (y : M) (inside : y∈(chartAt E c.val).source)
    (collar : y∈b.hyperbolic.normedAdaptedProjection.collar) :
    ∀ v, system.normalizedProjection c x y (system.normalizedProjection c x y v) =
      system.normalizedProjection c x y v := by
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val.val x.property.2
    (system.euclideanReferenceFrame c x)
  let A := CenteredTangentJacobianComparison.encoding (chartAt E c.val)
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) y inside L
  apply ConjugateProjectionRanks.idempotent A _ _ (system.normalizedProjection_encoding c x y inside)
  intro v
  exact congrArg (fun Q : TangentSpace (𝓘(ℝ,E)) y →L[ℝ] TangentSpace (𝓘(ℝ,E)) y => Q v)
    (b.hyperbolic.normedAdaptedProjection.idempotent y collar).eq

theorem PatchSystem.normalizedProjection_ker (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) (y : M) (inside : y∈(chartAt E c.val).source) :
    let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val.val x.property.2
      (system.euclideanReferenceFrame c x)
    let A := CenteredTangentJacobianComparison.encoding (chartAt E c.val)
      (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) y inside L
    (system.normalizedProjection c x y).ker =
      (b.hyperbolic.normedAdaptedProjection.unstable y).map A.toLinearMap := by
  exact ConjugateProjectionRanks.ker_eq_map _ _ _ (system.normalizedProjection_encoding c x y inside)

theorem PatchSystem.normalizedProjection_range (system : PatchSystem b) (c : Λ)
    (x : system.frameDomain c) (y : M) (inside : y∈(chartAt E c.val).source) :
    let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val.val x.property.2
      (system.euclideanReferenceFrame c x)
    let A := CenteredTangentJacobianComparison.encoding (chartAt E c.val)
      (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) y inside L
    (system.normalizedProjection c x y).range =
      (b.hyperbolic.normedAdaptedProjection.stable y).map A.toLinearMap := by
  exact ConjugateProjectionRanks.range_eq_map _ _ _ (system.normalizedProjection_encoding c x y inside)

end LeanShared.HyperbolicAdaptedPatchSystem
