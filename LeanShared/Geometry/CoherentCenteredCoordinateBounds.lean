module

public import LeanShared.Geometry.CoherentCenteredLinearBounds
public import LeanShared.Topology.CompactNearDiagonalContinuity
import all LeanShared.Geometry.CompactUniformCenteredCharts
import Mathlib.Tactic.FieldSimp

/-! Actual manifold points uniformly close to reference points are in the
selected coherent chart and have small normalized coordinates. -/
public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem exists_ambient_radius
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {H : M → M} {K : Set M} {B δ : ℝ}
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ)
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B) (bound : ∀ x, ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (r : ℝ) (positive : 0 < r) :
    ∃ η > 0, ∀ (x : K) (y : M), dist x.val y < η →
      y ∈ (chart d x).source ∧ ‖coordinate d frame x y‖ < r := by
  classical
  have inverseBounds (i : K) := CompactRiemannianChartBounds.inverse (chartAt E i.val)
    (chart_mem_maximalAtlas i.val) (d.patch i) (d.compact i) (d.source i)
  choose C positiveC boundC using inverseBounds
  have neighborhoods (i : K) := CompactNearDiagonalContinuity.exists_radius
    (d.patch i) (chartAt E i.val).source (d.compact i) (chartAt E i.val).open_source
    (d.source i) (chartAt E i.val) (chartAt E i.val).continuousOn
    (r / (B * C i)) (div_pos positive (mul_pos positiveB (positiveC i)))
  choose radii positiveR nearby using neighborhoods
  obtain ⟨η, positiveη, common⟩ := CompactUniformCenteredCharts.common_positive
    d.centers radii (fun i _ => positiveR i)
  refine ⟨η, positiveη, fun x y hxy => ?_⟩
  let i := index d x
  have member := (index_spec d x).1
  have memberPatch : x.val ∈ d.patch i := interior_subset (index_spec d x).2
  have close := nearby i x.val memberPatch y (hxy.trans_le (common i member))
  refine ⟨close.1, ?_⟩
  have inverse_eq : (linear d frame x).symm.toContinuousLinearMap =
      (frame x).symm.toContinuousLinearMap.comp
        (((CompactRiemannianChartBounds.chart_differentiable (chartAt E i.val)
          (chart_mem_maximalAtlas i.val)).mfderiv (d.source i memberPatch)).symm.toContinuousLinearMap.comp
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chartAt E i.val) x.val)).symm.toContinuousLinearMap) := by
    ext v
    rfl
  have inverse_bound : ‖(linear d frame x).symm.toContinuousLinearMap‖ ≤ B * C i := by
    rw [inverse_eq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (bound x) (boundC i x.val memberPatch) (norm_nonneg _) positiveB.le)
  have difference : ‖(chart d x) y - (chart d x) x.val‖ < r / (B * C i) := by
    change ‖(chartAt E i.val) y - (chartAt E i.val) x.val‖ < _
    rw [← dist_eq_norm, dist_comm]
    exact close.2
  calc
    ‖coordinate d frame x y‖ ≤ ‖(linear d frame x).symm.toContinuousLinearMap‖ *
        ‖(chart d x) y - (chart d x) x.val‖ :=
      (linear d frame x).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ (B * C i) * ‖(chart d x) y - (chart d x) x.val‖ :=
      mul_le_mul_of_nonneg_right inverse_bound (norm_nonneg _)
    _ < (B * C i) * (r / (B * C i)) :=
      mul_lt_mul_of_pos_left difference (mul_pos positiveB (positiveC i))
    _ = r := by field_simp [ne_of_gt positiveB, ne_of_gt (positiveC i)]


set_option maxHeartbeats 1600000 in
theorem exists_coordinate_radius
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
      ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ x : K, ∀ y : M, dist y x.val < radius →
      y ∈ (chart d x).source ∧ ‖coordinate d frame x y‖ < ε := by
  obtain ⟨C, positiveC, linearBounds⟩ := exists_uniform_linear_bound d frame positiveB bounds
  have witnesses (i : K) := CompactNearDiagonalContinuity.exists_radius
    (d.patch i) (chartAt E i.val).source (d.compact i)
    (chartAt E i.val).open_source (d.source i)
    (chartAt E i.val) (chartAt E i.val).continuousOn (ε / C) (div_pos positiveε positiveC)
  choose radii positiveRadii estimates using witnesses
  obtain ⟨radius, positiveRadius, common⟩ := CompactUniformCenteredCharts.common_positive
    d.centers radii (fun i _ => positiveRadii i)
  refine ⟨radius, positiveRadius, fun x y close => ?_⟩
  let i := index d x
  have member : i ∈ d.centers := (index_spec d x).1
  have patch : x.val ∈ d.patch i := interior_subset (index_spec d x).2
  have near : dist x.val y < radii i := by
    rw [dist_comm]
    exact close.trans_le (common i member)
  have facts := estimates i x.val patch y near
  refine ⟨facts.1, ?_⟩
  have difference : ‖chart d x y - chart d x x.val‖ < ε / C := by
    simpa only [chart, i, dist_eq_norm, norm_sub_rev] using facts.2
  calc
    ‖coordinate d frame x y‖ ≤ ‖(linear d frame x).symm.toContinuousLinearMap‖ *
        ‖chart d x y - chart d x x.val‖ :=
      (linear d frame x).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ C * ‖chart d x y - chart d x x.val‖ :=
      mul_le_mul_of_nonneg_right (linearBounds x).2 (norm_nonneg _)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left difference positiveC
    _ = ε := by field_simp

end LeanShared.CoherentCenteredCoordinateMaps
