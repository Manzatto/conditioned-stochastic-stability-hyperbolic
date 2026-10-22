module
public import LeanShared.Geometry.SmoothChartJacobianDensity
public import LeanShared.Geometry.FiniteSmoothReferenceLocalDensity

/-! The constructed finite smooth reference has positive smooth local densities,
and smooth reciprocal densities, in every maximal smooth chart. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set IsManifold
open scoped Manifold ContDiff

theorem Data.localDensity_contDiffOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) : ContDiffOn ℝ ∞ (d.localDensity c) c.target := by
  apply ContDiffOn.sum
  intro x _
  exact CoordinateJacobianDensity.contDiffOn (chartAt E x) c (chart_mem_maximalAtlas x) hc
    (d.density x) (d.smooth x) (d.compact_support x) (d.support x)

theorem Data.localDensity_inverse_contDiffOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    ContDiffOn ℝ ∞ (fun y => (d.localDensity c y)⁻¹) c.target :=
  (d.localDensity_contDiffOn c hc).inv (fun y hy => (d.localDensity_positive c hc y hy).ne')

end LeanShared.FiniteSmoothReferenceCharts
