module
public import LeanShared.Geometry.CoherentCenteredCoordinateMaps
public import LeanShared.Geometry.CompactRiemannianChartBounds
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-! The normalized coordinate maps of a generated coherent finite cover
have uniformly bounded actual linear parts and inverses. No continuity of
the selected frames or of the pointwise chart selection is required. -/
public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle BigOperators

set_option maxHeartbeats 1600000 in
theorem exists_uniform_linear_bound
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {H : M → M} {K : Set M} {B δ : ℝ}
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ)
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B)
    (bounds : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B ∧
      ‖(frame x).symm.toContinuousLinearMap‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : K,
      ‖(linear d frame x).toContinuousLinearMap‖ ≤ C ∧
      ‖(linear d frame x).symm.toContinuousLinearMap‖ ≤ C := by
  have forward (i : K) := CompactRiemannianChartBounds.forward
    (chartAt E i.val) (chart_mem_maximalAtlas i.val) (d.patch i) (d.compact i) (d.source i)
  have backward (i : K) := CompactRiemannianChartBounds.inverse
    (chartAt E i.val) (chart_mem_maximalAtlas i.val) (d.patch i) (d.compact i) (d.source i)
  choose Cs positiveCs boundCs using forward
  choose Ct positiveCt boundCt using backward
  let S := ∑ i ∈ d.centers, (Cs i + Ct i)
  have nonnegativeS : 0 ≤ S := Finset.sum_nonneg (fun i _ => add_nonneg (positiveCs i).le (positiveCt i).le)
  have each (i : K) (hi : i ∈ d.centers) : Cs i ≤ S ∧ Ct i ≤ S := by
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ d.centers) => add_nonneg (positiveCs j).le (positiveCt j).le) hi
    exact ⟨(le_add_of_nonneg_right (positiveCt i).le).trans h,
      (le_add_of_nonneg_left (positiveCs i).le).trans h⟩
  refine ⟨1 + B * S, by positivity, fun x => ?_⟩
  have member := (index_spec d x).1
  have hx := interior_subset (index_spec d x).2
  have sourceEq : (linear d frame x).toContinuousLinearMap =
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chart d x) x.val)).toContinuousLinearMap.comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (chart d x) x.val)).comp
          (frame x).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have inverseEq : (linear d frame x).symm.toContinuousLinearMap =
      (frame x).symm.toContinuousLinearMap.comp
        (((CompactRiemannianChartBounds.chart_differentiable (chart d x)
          (chart_mem d x)).mfderiv (inside d x)).symm.toContinuousLinearMap.comp
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chart d x) x.val)).symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  constructor
  · rw [sourceEq]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (boundCs (index d x) x.val hx) (bounds x).1 (norm_nonneg _) (positiveCs _).le)).trans
        (by nlinarith [(each (index d x) member).1])
  · rw [inverseEq]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (bounds x).2 (boundCt (index d x) x.val hx) (norm_nonneg _) positiveB.le)).trans
        (by nlinarith [(each (index d x) member).2])

end LeanShared.CoherentCenteredCoordinateMaps
