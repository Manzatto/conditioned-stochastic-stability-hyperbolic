module
public import LeanShared.Geometry.ParametricChartJacobianDensity
public import LeanShared.Geometry.FiniteSmoothReferencePushforwardDensity

/-! The actual finite reference measure's transported density depends
continuously on a joint C1 control/state inverse map. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set IsManifold
open scoped Topology Manifold ContDiff

@[expose] def Data.parametricDensity
    {A E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (d : Data (E := E) (M := M)) (Φ : A × M → M)
    (c : OpenPartialHomeomorph M E) (q : A × E) : ℝ :=
  ∑ i ∈ d.index, ParametricChartJacobianDensity.density (chartAt E i) c (d.density i) Φ q

theorem Data.parametricDensity_continuousOn
    {A E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (Φ : A × M → M)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (O : Set A) (openO : IsOpen O)
    (joint : ContMDiffOn ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 Φ (O ×ˢ univ)) :
    ContinuousOn (d.parametricDensity Φ c) (O ×ˢ c.target) := by
  apply continuousOn_finsetSum
  intro i _
  exact ParametricChartJacobianDensity.continuousOn (chartAt E i) c
    (chart_mem_maximalAtlas i) hc (d.density i) (d.smooth i).continuous
    (d.compact_support i) (d.support i) Φ O openO joint

set_option maxHeartbeats 800000 in
theorem Data.parametricDensity_eq_pushforward
    {A E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (d : Data (E := E) (M := M)) (Φ : A × M → M)
    (H : M ≃ₜ M) (a : A) (inverse : ∀ x, Φ (a,x) = H.symm x)
    (c : OpenPartialHomeomorph M E) (y : E) :
    d.parametricDensity Φ c (a,y) = d.pushforwardDensity H c y := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  simp only [ParametricChartJacobianDensity.density, CoordinateJacobianDensity.density,
    Data.transportedChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
    Homeomorph.transOpenPartialHomeomorph_source,
    mem_inter_iff, mem_preimage, OpenPartialHomeomorph.coe_trans_symm,
    Homeomorph.transOpenPartialHomeomorph_apply, Function.comp_def, inverse]

end LeanShared.FiniteSmoothReferenceCharts
