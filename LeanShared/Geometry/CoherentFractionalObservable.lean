module

public import LeanShared.Geometry.CoherentCenteredCoordinateMaps
public import LeanShared.Geometry.FractionalCompactChartIncrement
import all LeanShared.Geometry.CompactUniformCenteredCharts
import Mathlib.Tactic.GCongr

/-! A genuinely fractional-regular observable has one uniform Hölder
increment estimate in the actual finite coherent coordinates. Pointwise
frames need no continuity; their norm bounds suffice. -/
public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle BigOperators

set_option maxHeartbeats 2000000 in
theorem exists_holder_increment
    {E M P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {H : M → M} {K : Set M} {B δ : ℝ}
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ)
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B) (frameBound : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B)
    (f : M → F) (a : ℝ) (positiveA : 0 < a) (smallA : a < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := F) a f) :
    ∃ r > 0, ∃ C ≥ 0, ∀ x : K, ∀ v : P, ‖v‖ ≤ r →
      ‖f (decode d frame x v) - f x.val‖ ≤ C * ‖v‖ ^ a := by
  classical
  have localEstimates (i : K) := regular.compact_chart_increment positiveA smallA
    (chartAt E i.val) (chart_mem_maximalAtlas i.val) (d.patch i) (d.compact i) (d.source i)
  choose radii positiveR constants nonnegativeC localBound using localEstimates
  have chartEstimates (i : K) := CompactRiemannianChartBounds.forward (chartAt E i.val)
    (chart_mem_maximalAtlas i.val) (d.patch i) (d.compact i) (d.source i)
  choose chartConstants positiveChart chartBound using chartEstimates
  obtain ⟨r, positiveRadius, radiusBound⟩ := CompactUniformCenteredCharts.common_positive
    d.centers (fun i => radii i / (chartConstants i * B))
    (fun i _ => div_pos (positiveR i) (mul_pos (positiveChart i) positiveB))
  let C := ∑ i ∈ d.centers, constants i * (chartConstants i * B) ^ a
  have nonnegative : ∀ i, 0 ≤ constants i * (chartConstants i * B) ^ a :=
    fun i => mul_nonneg (nonnegativeC i) (Real.rpow_nonneg (mul_nonneg (positiveChart i).le positiveB.le) _)
  refine ⟨r, positiveRadius, C, Finset.sum_nonneg (fun i _ => nonnegative i), ?_⟩
  intro x v hv
  let i := index d x
  have member : i ∈ d.centers := (index_spec d x).1
  have inside : x.val ∈ d.patch i := interior_subset (index_spec d x).2
  have linear_eq : (linear d frame x).toContinuousLinearMap =
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chartAt E i.val) x.val)).toContinuousLinearMap.comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (chartAt E i.val) x.val)).comp
          (frame x).toContinuousLinearMap := by ext w; rfl
  have linearBound : ‖(linear d frame x).toContinuousLinearMap‖ ≤ chartConstants i * B := by
    rw [linear_eq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (chartBound i x.val inside) (frameBound x) (norm_nonneg _) (positiveChart i).le)
  have valueBound : ‖linear d frame x v‖ ≤ (chartConstants i * B) * ‖v‖ :=
    ((linear d frame x).toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right linearBound (norm_nonneg _))
  have small : ‖linear d frame x v‖ ≤ radii i := by
    have scaled := mul_le_mul_of_nonneg_left
      (hv.trans (radiusBound i member)) (mul_pos (positiveChart i) positiveB).le
    have cancellation : (chartConstants i * B) * (radii i / (chartConstants i * B)) = radii i :=
      mul_div_cancel₀ _ (ne_of_gt (mul_pos (positiveChart i) positiveB))
    exact valueBound.trans (scaled.trans_eq cancellation)
  have estimate := localBound i x.val inside (linear d frame x v) small
  change ‖f (decode d frame x v) - f x.val‖ ≤ _ at estimate
  have coefficient : constants i * (chartConstants i * B) ^ a ≤ C :=
    Finset.single_le_sum (fun j _ => nonnegative j) member
  calc
    _ ≤ constants i * ‖linear d frame x v‖ ^ a := estimate
    _ ≤ constants i * ((chartConstants i * B) * ‖v‖) ^ a :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) valueBound positiveA.le) (nonnegativeC i)
    _ = (constants i * (chartConstants i * B) ^ a) * ‖v‖ ^ a := by
      rw [Real.mul_rpow (mul_nonneg (positiveChart i).le positiveB.le) (norm_nonneg _)]
      ring
    _ ≤ C * ‖v‖ ^ a := mul_le_mul_of_nonneg_right coefficient (Real.rpow_nonneg (norm_nonneg _) _)

end LeanShared.CoherentCenteredCoordinateMaps
