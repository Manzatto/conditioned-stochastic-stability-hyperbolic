module

public import LeanShared.Geometry.CoherentCenteredCoordinateBounds
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! One ambient neighborhood radius lies in the selected chart source
at every point of the actual finite coherent chart cover.  This requires
no continuity of the pointwise chart or frame selections.
-/

public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

theorem exists_chart_source_radius
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {H : M → M} {K : Set M} {B δ : ℝ}
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ) :
    ∃ ρ > 0, ∀ (x : K) (y : M), dist x.val y < ρ → y ∈ (chart d x).source := by
  have neighborhoods (i : K) := CompactNearDiagonalContinuity.exists_radius
    (d.patch i) (chartAt E i.val).source (d.compact i) (chartAt E i.val).open_source
    (d.source i) (chartAt E i.val) (chartAt E i.val).continuousOn 1 zero_lt_one
  choose radii positive estimates using neighborhoods
  obtain ⟨ρ, positiveρ, common⟩ := CompactUniformCenteredCharts.common_positive d.centers radii
    (fun i _ => positive i)
  refine ⟨ρ, positiveρ, fun x y close => ?_⟩
  exact (estimates (index d x) x.val (interior_subset (index_spec d x).2) y
    (close.trans_le (common (index d x) (index_spec d x).1))).1

end LeanShared.CoherentCenteredCoordinateMaps
