module
public import LeanShared.Geometry.PseudoReferenceLinearBounds
public import LeanShared.Geometry.PseudoReferenceCompactPatches
public import LeanShared.Topology.CompactNearDiagonalContinuity
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import Mathlib.Tactic.FieldSimp

/-! Uniformly small produced coordinates decode close to the actual reference
point. The proof uses finite actual inverse charts on compact patches and
proved linear bounds, without continuity of frame/chart selections. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem exists_decode_radius
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} {B : ℝ}
    {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
    (d : HyperbolicBasicSet.PseudoReferenceGeometry h)
    (frame : ∀ x : Λ, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B)
    (bounds : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B ∧
      ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ x : Λ, ∀ z : P, ‖z‖ ≤ radius →
      chart d x x.val + linear d frame x z ∈ (chart d x).target ∧
      dist (decode d frame x z) x.val < ε := by
  obtain ⟨C,positiveC,linearBounds⟩ := exists_uniform_linear_bound d frame positiveB bounds
  have witnesses (i : Λ) := CompactNearDiagonalContinuity.exists_radius
    (chartAt E i.val '' ambientPatch d i) (chartAt E i.val).target
    ((compact_ambientPatch d i).image_of_continuousOn ((chartAt E i.val).continuousOn.mono (ambientPatch_source d i)))
    (chartAt E i.val).open_target
    (by rintro _ ⟨x,hx,rfl⟩; exact (chartAt E i.val).map_source (ambientPatch_source d i hx))
    (chartAt E i.val).symm (chartAt E i.val).symm.continuousOn ε positiveε
  choose radii positiveRadii estimates using witnesses
  obtain ⟨radius,positiveRadius,common⟩ := CompactUniformCenteredCharts.common_positive
    d.centers (fun i => radii i / (2 * C)) (fun i _ => div_pos (positiveRadii i) (by positivity))
  refine ⟨radius,positiveRadius,fun x z hz => ?_⟩
  let i := d.index x
  have member : i ∈ d.centers := d.index_mem x
  have insidePatch : x.val ∈ ambientPatch d i := selected_ambientPatch d x
  have displacement : dist (chart d x x.val + linear d frame x z) (chart d x x.val) ≤ radii i / 2 := by
    rw [dist_eq_norm,add_sub_cancel_left]
    calc
      ‖linear d frame x z‖ ≤ ‖(linear d frame x).toContinuousLinearMap‖ * ‖z‖ :=
        (linear d frame x).toContinuousLinearMap.le_opNorm z
      _ ≤ C * (radii i / (2 * C)) := mul_le_mul (linearBounds x).1 (hz.trans (common i member))
        (norm_nonneg z) positiveC.le
      _ = radii i / 2 := by field_simp
  have near : dist (chartAt E i.val x.val) (chart d x x.val + linear d frame x z) < radii i := by
    change dist (chart d x x.val) (chart d x x.val + linear d frame x z) < radii i
    rw [dist_comm]
    exact displacement.trans_lt (half_lt_self (positiveRadii i))
  have facts := estimates i (chartAt E i.val x.val) (mem_image_of_mem _ insidePatch)
    (chart d x x.val + linear d frame x z) near
  have centerEq : (chartAt E i.val).symm (chartAt E i.val x.val) = x.val :=
    (chartAt E i.val).left_inv (ambientPatch_source d i insidePatch)
  rw [centerEq] at facts
  have distance := facts.2
  change dist x.val (decode d frame x z) < ε at distance
  exact ⟨facts.1, by simpa only [dist_comm] using distance⟩

end LeanShared.PseudoReferenceCoordinateMaps
