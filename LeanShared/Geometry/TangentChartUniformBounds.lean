module

public import LeanShared.Geometry.TangentChartTrivialization

/-! Actual native tangent-chart inverse and compact two-sided norm bounds.
The chart trivialization is identified with the normalized differentiable
chart, including the supplied continuous Riemannian fiber norms. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.TangentChartTrivialization
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem inverse (center x : M) (hx : x ∈ (chartAt E center).source) :
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) center).symmL ℝ x =
      ((CompactRiemannianChartBounds.chart_differentiable (chartAt E center)
        (chart_mem_maximalAtlas center)).mfderiv hx).symm.toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chartAt E center) x)).symm.toContinuousLinearMap := by
  let e := trivializationAt E (TangentSpace (𝓘(ℝ,E))) center
  have member : x ∈ e.baseSet := by simpa only [e, baseSet] using hx
  ext v
  apply (e.continuousLinearEquivAt ℝ x member).injective
  rw [e.coe_continuousLinearEquivAt_eq member]
  rw [e.continuousLinearMapAt_symmL member]
  rw [show e.continuousLinearMapAt ℝ x = _ from forward hx]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  change v = (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chartAt E center) x))
    ((CompactRiemannianChartBounds.chart_differentiable (chartAt E center)
      (chart_mem_maximalAtlas center)).mfderiv hx
      (((CompactRiemannianChartBounds.chart_differentiable (chartAt E center)
        (chart_mem_maximalAtlas center)).mfderiv hx).symm
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chartAt E center) x)).symm v)))
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem exists_bounds (center : M) (K : Set M) (compact : IsCompact K)
    (inside : K ⊆ (chartAt E center).source) :
    ∃ C > 0, ∀ x ∈ K,
      ‖(trivializationAt E (TangentSpace (𝓘(ℝ,E))) center).continuousLinearMapAt ℝ x‖ ≤ C ∧
      ‖(trivializationAt E (TangentSpace (𝓘(ℝ,E))) center).symmL ℝ x‖ ≤ C := by
  obtain ⟨A, positiveA, first⟩ := CompactRiemannianChartBounds.forward (chartAt E center)
    (chart_mem_maximalAtlas center) K compact inside
  obtain ⟨B, positiveB, second⟩ := CompactRiemannianChartBounds.inverse (chartAt E center)
    (chart_mem_maximalAtlas center) K compact inside
  refine ⟨max A B, positiveA.trans_le (le_max_left _ _), fun x hx => ?_⟩
  constructor
  · rw [forward (inside hx)]
    exact (first x hx).trans (le_max_left _ _)
  · rw [inverse center x (inside hx)]
    exact (second x hx).trans (le_max_right _ _)

end LeanShared.TangentChartTrivialization
