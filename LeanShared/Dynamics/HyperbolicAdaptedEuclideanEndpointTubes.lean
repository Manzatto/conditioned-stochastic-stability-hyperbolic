module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanFrameBounds
public import LeanShared.Geometry.CompactNormalizedChartTube
public import LeanShared.Geometry.CenteredCompactChartEncodingBounds
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
import Mathlib.Tactic.Linarith

/-! Common actual chart-frame bounds in the same Euclidean adapted model. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.euclidean_endpoint_tubes {system : PatchSystem b} (atlas : ChartAtlas system) :
    ∃ radius > 0, ∃ C > 0, ∃ K : Λ → Set M,
      (∀ c, IsCompact (K c) ∧ K c ⊆ (chartAt E c.val).source) ∧
      ∀ c ∈ atlas.centers, ∀ x (hx : x ∈ atlas.patch c),
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x,atlas.inside c hx⟩)
      ∀ z, ‖z‖ ≤ radius →
        (chartAt E c.val) x.val+L z ∈ (chartAt E c.val).target ∧
        (chartAt E c.val).symm ((chartAt E c.val) x.val+L z) ∈ K c ∧
        let m := (chartAt E c.val).symm ((chartAt E c.val) x.val+L z)
        ∃ hm : m ∈ (chartAt E c.val).source,
          ‖(CenteredTangentJacobianComparison.encoding (chartAt E c.val)
            (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) m hm L).toContinuousLinearMap‖ ≤ C ∧
          ‖(CenteredTangentJacobianComparison.encoding (chartAt E c.val)
            (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c.val)) m hm L).symm.toContinuousLinearMap‖ ≤ C := by
  classical
  let ambient (c : Λ) : Set M := Subtype.val '' atlas.patch c
  have compactAmbient (c : Λ) : IsCompact (ambient c) := (atlas.compact c).image continuous_subtype_val
  have ambientInside (c : Λ) : ambient c ⊆ (chartAt E c.val).source := by
    rintro _ ⟨x,hx,rfl⟩
    exact (atlas.inside c hx).2
  have positiveB : 0 < 2*atlas.bound := by linarith [atlas.one_le_bound]
  have tubes (c : Λ) := CompactNormalizedChartTube.exists_tube (P := system.EuclideanModel)
    (chartAt E c.val) (ambient c) (compactAmbient c) (ambientInside c) (2*atlas.bound) positiveB.le
  choose radii positiveRadii K compactK insideK tube using tubes
  obtain ⟨radius,positiveRadius,common⟩ := CompactUniformCenteredCharts.common_positive atlas.centers radii
    (fun c _ => positiveRadii c)
  obtain ⟨C,positiveC,bounds⟩ := CenteredTangentJacobianComparison.exists_finite_encoding_bounds
    (P := system.EuclideanModel) atlas.centers (fun c => chartAt E c.val)
    (fun c _ => chart_mem_maximalAtlas c.val) K (fun c _ => compactK c) (fun c _ => insideK c) positiveB
  refine ⟨radius,positiveRadius,C,positiveC,K,fun c => ⟨compactK c,insideK c⟩,?_⟩
  intro c hc x hx
  dsimp only
  intro z small
  let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
    (system.euclideanReferenceFrame c ⟨x,atlas.inside c hx⟩)
  have frameBounds := atlas.euclidean_frame_bounds c hc x hx
  have actual := tube c x.val ⟨x,hx,rfl⟩ L.toContinuousLinearMap frameBounds.1 z
    (small.trans (common c hc))
  refine ⟨actual.1,actual.2,insideK c actual.2,?_⟩
  exact bounds c hc _ actual.2 L frameBounds.1 frameBounds.2

end LeanShared.HyperbolicAdaptedPatchSystem
