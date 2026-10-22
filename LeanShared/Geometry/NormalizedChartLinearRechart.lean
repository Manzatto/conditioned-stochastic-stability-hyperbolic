module
public import LeanShared.Geometry.AffineNormalizedChartAtlas
public import LeanShared.Geometry.ContinuousCenteredFrameCharts
public import LeanShared.Geometry.LinearRechartedAtlas

/-! Actual normalized charts are charts of the genuine linearly recharted
manifold, by pulling their frames back to the original coordinate model. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.NormalizedChartLinearRechart
variable {E P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace M]

 theorem affine_chartImage (e : E ≃L[ℝ] P) (c : OpenPartialHomeomorph M E)
    (L : P ≃L[ℝ] E) (a : E) :
    LinearRechartedManifold.chartImage e
      (c.transHomeomorph (CoherentCenteredCoordinateMaps.affineNormalize (e.trans L) a)) =
      c.transHomeomorph (CoherentCenteredCoordinateMaps.affineNormalize L a) := by
  apply OpenPartialHomeomorph.ext
  · intro x
    change e (e.symm (L.symm (c x-a))) = L.symm (c x-a)
    exact e.apply_symm_apply _
  · intro z
    change c.symm (a + L (e (e.symm z))) = c.symm (a + L z)
    rw [e.apply_symm_apply]
  · ext x
    simp only [LinearRechartedManifold.chartImage, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    rfl

variable [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem affine_mem_maximal (e : E ≃L[ℝ] P) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (L : P ≃L[ℝ] E) (a : E) :
    letI := LinearRechartedManifold.charts (M := M) e;
      c.transHomeomorph (CoherentCenteredCoordinateMaps.affineNormalize L a) ∈
        maximalAtlas (𝓘(ℝ,P)) ∞ M := by
  have hh := LinearRechartedManifold.chartImage_mem_maximal e _
    (AffineNormalizedChartAtlas.mem_maximal c hc (e.trans L) a)
  rw [affine_chartImage] at hh
  exact hh

end LeanShared.NormalizedChartLinearRechart
