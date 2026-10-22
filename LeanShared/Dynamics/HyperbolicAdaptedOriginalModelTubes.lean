module
public import LeanShared.Dynamics.HyperbolicAdaptedNormalizedTubePartition
public import LeanShared.Geometry.NormalizedFrameChartPullback

/-! The actual normalized Euclidean adapted charts have genuine original
model pullbacks. Their chart images are exactly the already chosen
normalized charts, with the same source and physical tube supports. -/
@[expose] public noncomputable section
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Topology
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

def ChartAtlas.originalTubeChart (atlas : ChartAtlas system) (e : E ≃L[ℝ] system.EuclideanModel)
    (i : atlas.NormalizedTubeIndex) : OpenPartialHomeomorph M E :=
  ContinuousCenteredFrameCharts.normalizedChart i.val.1.val i.val.2.val
    (atlas.inside i.val.1 i.property.2).2
    (e.trans (system.euclideanReferenceFrame i.val.1
      ⟨i.val.2,atlas.inside i.val.1 i.property.2⟩))

theorem ChartAtlas.originalTubeChart_mem_maximal (atlas : ChartAtlas system)
    (e : E ≃L[ℝ] system.EuclideanModel) (i : atlas.NormalizedTubeIndex) :
    atlas.originalTubeChart e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M :=
  AffineNormalizedChartAtlas.mem_maximal (chartAt E i.val.1.val)
    (chart_mem_maximalAtlas i.val.1.val)
    (ContinuousCenteredFrameCharts.chartFrame i.val.1.val i.val.2.val
      (atlas.inside i.val.1 i.property.2).2
      (e.trans (system.euclideanReferenceFrame i.val.1
        ⟨i.val.2,atlas.inside i.val.1 i.property.2⟩))) ((chartAt E i.val.1.val) i.val.2.val)

theorem ChartAtlas.originalTubeChart_chartImage (atlas : ChartAtlas system)
    (e : E ≃L[ℝ] system.EuclideanModel) (i : atlas.NormalizedTubeIndex) :
    LinearRechartedManifold.chartImage e (atlas.originalTubeChart e i) =
      atlas.normalizedTubeChart i :=
  ContinuousCenteredFrameCharts.normalizedChart_chartImage e i.val.1.val i.val.2.val
    (atlas.inside i.val.1 i.property.2).2
    (system.euclideanReferenceFrame i.val.1 ⟨i.val.2,atlas.inside i.val.1 i.property.2⟩)

theorem ChartAtlas.originalTubeChart_source (atlas : ChartAtlas system)
    (e : E ≃L[ℝ] system.EuclideanModel) (i : atlas.NormalizedTubeIndex) :
    (atlas.originalTubeChart e i).source = (atlas.normalizedTubeChart i).source := rfl

theorem ChartAtlas.originalTubeChart_apply (atlas : ChartAtlas system)
    (e : E ≃L[ℝ] system.EuclideanModel) (i : atlas.NormalizedTubeIndex) (m : M) :
    e (atlas.originalTubeChart e i m) = atlas.normalizedTubeChart i m :=
  congrArg (fun c : OpenPartialHomeomorph M system.EuclideanModel => c m)
    (atlas.originalTubeChart_chartImage e i)

theorem ChartAtlas.originalTubeChart_symm (atlas : ChartAtlas system)
    (e : E ≃L[ℝ] system.EuclideanModel) (i : atlas.NormalizedTubeIndex) (z : system.EuclideanModel) :
    (atlas.originalTubeChart e i).symm (e.symm z) = (atlas.normalizedTubeChart i).symm z :=
  congrArg (fun c : OpenPartialHomeomorph M system.EuclideanModel => c.symm z)
    (atlas.originalTubeChart_chartImage e i)

theorem ChartAtlas.normalizedTube_original_model (atlas : ChartAtlas system)
    (e : E ≃L[ℝ] system.EuclideanModel) (radius : ℝ) (i : atlas.NormalizedTubeIndex) :
    atlas.normalizedTube radius i = (atlas.originalTubeChart e i).source ∩
      (atlas.originalTubeChart e i) ⁻¹' (e ⁻¹' ball 0 radius) := by
  ext m
  change (m ∈ (atlas.normalizedTubeChart i).source ∧ atlas.normalizedTubeChart i m ∈ ball 0 radius) ↔
    (m ∈ (atlas.originalTubeChart e i).source ∧ e (atlas.originalTubeChart e i m) ∈ ball 0 radius)
  rw [atlas.originalTubeChart_source e i,atlas.originalTubeChart_apply e i m]

end LeanShared.HyperbolicAdaptedPatchSystem
