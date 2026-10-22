module
public import LeanShared.Geometry.PseudoReferenceLinearBounds
public import LeanShared.Geometry.PseudoReferenceCompactPatches
public import LeanShared.Topology.CompactNearDiagonalContinuity
public import Mathlib.Tactic.FieldSimp

/-! Arbitrarily small pseudo-reference forcing follows from actual chart
continuity on the retained compact patches. The tolerance is chosen after
the normalization bounds, independently of the contraction radius. -/
public noncomputable section
namespace LeanShared.PseudoReferenceCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
open CenteredManifoldCoordinates
variable {E M P:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
  {T:M≃ₜM} {Λ:Set M} {h:HyperbolicBasicSet.HyperbolicData (E:=E) T Λ}
  (d:HyperbolicBasicSet.PseudoReferenceGeometry h)

theorem exists_forcing_window
    (frame:∀x:Λ,P≃L[ℝ]TangentSpace (𝓘(ℝ,E)) x.val)
    {B:ℝ} (positiveB:0<B)
    (bounds:∀x,‖(frame x).toContinuousLinearMap‖≤B ∧ ‖(frame x).symm.toContinuousLinearMap‖≤B)
    (H:M→M) (τ:ℝ) (positiveτ:0<τ) :
    ∃η:ℝ,0<η ∧ ∀x y:Λ,dist (H x.val) y.val<η→
      H x.val∈(chart d y).source ∧
      ‖centered (linear d frame x) (linear d frame y)
        ((chart d x) x.val) ((chart d y) y.val)
        (fun z=>(chart d y) (H ((chart d x).symm z))) 0‖≤τ := by
  classical
  obtain ⟨C,positiveC,linearBounds⟩:=exists_uniform_linear_bound d frame positiveB bounds
  have radii (i:Λ):∃η:ℝ,0<η ∧ ∀x∈ambientPatch d i,∀y,dist x y<η→
      y∈(chartAt E i.val).source ∧
      dist (chartAt E i.val x) (chartAt E i.val y)<τ/(2*C):=
    CompactNearDiagonalContinuity.exists_radius (ambientPatch d i) (chartAt E i.val).source
      (compact_ambientPatch d i) (chartAt E i.val).open_source (ambientPatch_source d i)
      (chartAt E i.val) (chartAt E i.val).continuousOn (τ/(2*C)) (by positivity)
  choose radius positiveRadius radiusProperty using radii
  have finiteMinimum (J:Finset Λ):∃η:ℝ,0<η ∧ ∀i∈J,η≤radius i:=by
    induction J using Finset.induction_on with
    | empty=>exact ⟨1,zero_lt_one,by simp⟩
    | @insert i J _ ih=>
      obtain ⟨η,hη,small⟩:=ih
      refine ⟨min (radius i) η,lt_min (positiveRadius i) hη,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (small j hj)
  obtain ⟨η,positiveη,small⟩:=finiteMinimum d.centers
  refine ⟨η,positiveη,fun x y close=>?_⟩
  have near:dist y.val (H x.val)<radius (d.index y):=
    (show dist y.val (H x.val)<η from by simpa only [dist_comm] using close).trans_le (small (d.index y) (d.index_mem y))
  obtain ⟨valid,error⟩:=radiusProperty (d.index y) y.val (selected_ambientPatch d y) (H x.val) near
  refine ⟨valid,?_⟩
  change ‖(linear d frame y).symm
    ((chart d y) (H ((chart d x).symm ((chart d x) x.val+linear d frame x 0)))-
      (chart d y) y.val)‖≤τ
  rw [_root_.map_zero,add_zero,(chart d x).left_inv (inside d x)]
  have difference:‖(chart d y) (H x.val)-(chart d y) y.val‖<τ/(2*C):=by
    simpa only [chart,dist_eq_norm,norm_sub_rev] using error
  apply le_of_lt
  calc
    _ ≤ ‖(linear d frame y).symm.toContinuousLinearMap‖*
        ‖(chart d y) (H x.val)-(chart d y) y.val‖:=
      (linear d frame y).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ C*‖(chart d y) (H x.val)-(chart d y) y.val‖:=
      mul_le_mul_of_nonneg_right (linearBounds y).2 (norm_nonneg _)
    _ < C*(τ/(2*C)):=mul_lt_mul_of_pos_left difference positiveC
    _ = τ/2:=by field_simp [positiveC.ne']
    _ ≤ τ:=by linarith
end LeanShared.PseudoReferenceCoordinateMaps
