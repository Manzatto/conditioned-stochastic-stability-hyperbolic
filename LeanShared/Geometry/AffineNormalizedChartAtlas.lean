module
public import LeanShared.Geometry.CoherentCenteredChartEquivalence
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Affine normalization within the actual original coordinate model gives
a genuine maximal chart. The statement keeps both models equal explicitly. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.AffineNormalizedChartAtlas
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem mem_maximal (c : OpenPartialHomeomorph M E)
    (member : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (L : E ≃L[ℝ] E) (a : E) :
    c.transHomeomorph (CoherentCenteredCoordinateMaps.affineNormalize L a) ∈
      maximalAtlas (𝓘(ℝ,E)) ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (fun x => L.symm (c x-a)) c.source
    exact (L.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff.comp_contMDiffOn
      (contMDiffOn_of_mem_maximalAtlas member)
  · change ContMDiffOn (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞
      (c.symm ∘ (fun z : E => a+L z))
      (c.transHomeomorph (CoherentCenteredCoordinateMaps.affineNormalize L a)).target
    apply (contMDiffOn_symm_of_mem_maximalAtlas member).comp
      (contDiff_const.add L.contDiff).contMDiff.contMDiffOn
    intro z hz
    exact hz

end LeanShared.AffineNormalizedChartAtlas
