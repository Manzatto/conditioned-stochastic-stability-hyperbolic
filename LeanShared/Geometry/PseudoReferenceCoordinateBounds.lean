module
public import LeanShared.Geometry.PseudoReferenceCoordinateMaps
public import LeanShared.Geometry.PseudoReferenceCompactPatches
public import LeanShared.Topology.CompactNearDiagonalContinuity
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import Mathlib.Tactic.FieldSimp

/-! Ambient closeness implies uniformly small normalized coordinates in the
single coherently selected chart. Bounds are derived from compact chart
inverse differentials and actual frame bounds, without continuity of the
pointwise frame or chart selection. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem exists_ambient_radius
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {B : ℝ}
    {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
    (d : HyperbolicBasicSet.PseudoReferenceGeometry h)
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B) (bound : ∀ x, ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (r : ℝ) (positive : 0 < r) :
    ∃ η > 0, ∀ (x : Λ) (y : M), dist x.val y < η →
      y ∈ (chart d x).source ∧ ‖coordinate d frame x y‖ < r := by
  classical
  have inverseBounds (i : Λ) := CompactRiemannianChartBounds.inverse (chartAt E i.val)
    (chart_mem_maximalAtlas i.val) (ambientPatch d i) (compact_ambientPatch d i) (ambientPatch_source d i)
  choose C positiveC boundC using inverseBounds
  have neighborhoods (i : Λ) := CompactNearDiagonalContinuity.exists_radius
    (ambientPatch d i) (chartAt E i.val).source (compact_ambientPatch d i) (chartAt E i.val).open_source
    (ambientPatch_source d i) (chartAt E i.val) (chartAt E i.val).continuousOn
    (r / (B * C i)) (div_pos positive (mul_pos positiveB (positiveC i)))
  choose radii positiveR nearby using neighborhoods
  obtain ⟨η, positiveη, common⟩ := CompactUniformCenteredCharts.common_positive
    d.centers radii (fun i _ => positiveR i)
  refine ⟨η, positiveη, fun x y hxy => ?_⟩
  let i := d.index x
  have member := d.index_mem x
  have memberPatch : x.val ∈ ambientPatch d i := selected_ambientPatch d x
  have close := nearby i x.val memberPatch y (hxy.trans_le (common i member))
  refine ⟨close.1, ?_⟩
  have inverse_eq : (linear d frame x).symm.toContinuousLinearMap =
      (frame x).symm.toContinuousLinearMap.comp
        (((CompactRiemannianChartBounds.chart_differentiable (chartAt E i.val)
          (chart_mem_maximalAtlas i.val)).mfderiv (ambientPatch_source d i memberPatch)).symm.toContinuousLinearMap.comp
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

end LeanShared.PseudoReferenceCoordinateMaps
