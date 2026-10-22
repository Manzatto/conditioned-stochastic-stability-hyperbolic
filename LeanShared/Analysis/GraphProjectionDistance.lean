module
public import LeanShared.Geometry.BoundedProjectionGraph
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Actual finite-dimensional graph slope controls the distance between the
true orthogonal projections. Both directed distances are derived internally. -/
public noncomputable section
namespace LeanShared.GraphProjectionDistance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem bound (U W : Submodule ℝ E)
    (dimension : Module.finrank ℝ W=Module.finrank ℝ U)
    {L : ℝ} (nonnegative : 0 ≤ L)
    (slope : ∀ w : W, ‖Uᗮ.orthogonalProjectionOnto (w : E)‖ ≤
      L*‖U.orthogonalProjectionOnto (w : E)‖) :
    ‖U.starProjection-W.starProjection‖ ≤ 2*L := by
  obtain ⟨D,hD,range⟩ := BoundedProjectionGraph.exists_graph U W dimension nonnegative slope
  let P := U.starProjection
  let R := W.starProjection
  let I := ContinuousLinearMap.id ℝ E
  have selfP : P.adjoint=P := by
    change (U.subtypeL.comp U.orthogonalProjectionOnto).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, U.adjoint_orthogonalProjectionOnto, U.adjoint_subtypeL]
    rfl
  have selfR : R.adjoint=R := by
    change (W.subtypeL.comp W.orthogonalProjectionOnto).adjoint = _
    rw [ContinuousLinearMap.adjoint_comp, W.adjoint_orthogonalProjectionOnto, W.adjoint_subtypeL]
    rfl
  have first : ‖(I-P).comp R‖ ≤ L := by
    apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
    intro v
    have estimate := slope ⟨R v, W.starProjection_apply_mem v⟩
    have small := U.norm_starProjection_apply_le (R v)
    have smallR := W.norm_starProjection_apply_le v
    change ‖R v-P (R v)‖ ≤ L*‖v‖
    have same : ‖R v-P (R v)‖=‖Uᗮ.orthogonalProjectionOnto (R v)‖ := by
      rw [← Submodule.norm_coe, ← Uᗮ.starProjection_apply, U.starProjection_orthogonal]
      rfl
    rw [same]
    exact estimate.trans (mul_le_mul_of_nonneg_left (small.trans smallR) nonnegative)
  have second : ‖(I-R).comp P‖ ≤ L := by
    apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
    intro v
    let u : U := U.orthogonalProjectionOnto v
    let w := IntrinsicGraphJacobian.graphDifferential U D u
    have member : w ∈ W := by
      rw [← range]
      exact ⟨u,rfl⟩
    have fixed : R w=w := W.starProjection_eq_self_iff.mpr member
    have same : P v-R (P v)=(I-R) (P v-w) := by
      simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub, fixed, I]
      abel
    have contraction (z : E) : ‖(I-R) z‖ ≤ ‖z‖ := by
      have identity : I-R=Wᗮ.starProjection := W.starProjection_orthogonal.symm
      rw [identity]
      exact Wᗮ.norm_starProjection_apply_le z
    change ‖P v-R (P v)‖ ≤ L*‖v‖
    rw [same]
    have difference : P v-w=-(D u : E) := by
      change (u : E)-((u : E)+(D u : E))=_
      abel
    calc
      _ ≤ ‖P v-w‖ := contraction _
      _ = ‖D u‖ := by rw [difference, norm_neg, Submodule.norm_coe]
      _ ≤ L*‖u‖ := (D.le_opNorm u).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
      _ ≤ L*‖v‖ := mul_le_mul_of_nonneg_left (U.norm_orthogonalProjectionOnto_apply_le v) nonnegative
  have other : ‖P.comp (I-R)‖ ≤ L := by
    have identity : ((I-R).comp P).adjoint=P.comp (I-R) := by
      rw [ContinuousLinearMap.adjoint_comp, selfP, map_sub, ContinuousLinearMap.adjoint_id, selfR]
    rw [← identity, ContinuousLinearMap.adjoint.norm_map]
    exact second
  have identity : P-R=P.comp (I-R)-(I-P).comp R := by
    ext v
    simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub, ContinuousLinearMap.id_apply, I]
    abel
  change ‖P-R‖ ≤ 2*L
  rw [identity]
  exact (norm_sub_le _ _).trans (by linarith)
end LeanShared.GraphProjectionDistance
