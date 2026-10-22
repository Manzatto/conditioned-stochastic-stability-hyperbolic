module
public import LeanShared.Geometry.ContinuousCenteredFrameCharts
public import LeanShared.Geometry.CenteredAtlasCoordinates
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Genuine smooth centered charts and the literal coordinate derivative of
the actual map. The frame at each center is fixed during differentiation. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ContinuousCenteredFrameCharts
variable {E P Q M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem normalizedChart_smooth (center p : M) (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) p) :
    ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, P)) ∞
      (normalizedChart center p inside A) (normalizedChart center p inside A).source := by
  let L := chartFrame center p inside A
  have normalize : ContDiff ℝ ∞ (fun v : E => L.symm (v - (chartAt E center) p)) :=
    L.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  change ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, P)) ∞
    (fun y => L.symm ((chartAt E center) y - (chartAt E center) p)) (chartAt E center).source
  exact normalize.contMDiff.comp_contMDiffOn (contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := center))

theorem normalizedChart_symm_smooth (center p : M) (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) p) :
    ContMDiffOn (𝓘(ℝ, P)) (𝓘(ℝ, E)) ∞
      (normalizedChart center p inside A).symm (normalizedChart center p inside A).target := by
  let L := chartFrame center p inside A
  have affine : ContDiff ℝ ∞ (fun z : P => (chartAt E center) p + L z) :=
    contDiff_const.add L.contDiff
  change ContMDiffOn (𝓘(ℝ, P)) (𝓘(ℝ, E)) ∞
    (fun z => (chartAt E center).symm ((chartAt E center) p + L z)) _
  exact (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := center)).comp affine.contMDiff.contMDiffOn
    (fun _ h => h)

theorem coordinate_hasFDerivAt (H : M → M) (p c d : M)
    (source : p ∈ (chartAt E c).source) (target : H p ∈ (chartAt E d).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) p)
    (B : Q ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (H p))
    (smooth : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) H p) :
    HasFDerivAt (fun z => normalizedChart d (H p) target B
        (H ((normalizedChart c p source A).symm z)))
      (B.symm.toContinuousLinearMap.comp ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H p).comp
        A.toContinuousLinearMap)) 0 :=
  CenteredAtlasCoordinates.hasFDerivAt_centered H p (chartAt E c) (chartAt E d)
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas c))
    (CompactRiemannianChartBounds.chart_differentiable _ (chart_mem_maximalAtlas d))
    source target A B smooth

end LeanShared.ContinuousCenteredFrameCharts
