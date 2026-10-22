module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! A small complementary coordinate gives an actual orthogonal graph slope,
even when the original stable/unstable splitting is oblique. -/
public section
namespace LeanShared.OrthogonalSlopeFromDecomposition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem bound (V : Submodule ℝ E) (u w : E) (member : w ∈ V)
    (η : ℝ) (nonnegative : 0 ≤ η) (small : η < 1)
    (error : ‖u‖ ≤ η*‖w‖) :
    ‖Vᗮ.orthogonalProjectionOnto (u+w)‖ ≤
      (η/(1-η))*‖V.orthogonalProjectionOnto (u+w)‖ := by
  have fixed : V.starProjection w=w := V.starProjection_eq_self_iff.mpr member
  have transverse : ‖Vᗮ.orthogonalProjectionOnto (u+w)‖ ≤ ‖u‖ := by
    have zero : Vᗮ.starProjection w=0 := by rw [V.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply, fixed, sub_self]
    have fact := Vᗮ.norm_starProjection_apply_le u
    change ‖Vᗮ.starProjection (u+w)‖ ≤ ‖u‖
    simpa only [map_add, zero, add_zero] using fact
  have longitudinal : ‖w‖ ≤ ‖V.orthogonalProjectionOnto (u+w)‖+‖u‖ := by
    have identity : w=V.starProjection (u+w)-V.starProjection u := by rw [map_add,fixed]; abel
    calc
      _ = ‖V.starProjection (u+w)-V.starProjection u‖ := congrArg norm identity
      _ ≤ ‖V.starProjection (u+w)‖+‖V.starProjection u‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl (V.norm_starProjection_apply_le u)
  have denominator : 0 < 1-η := sub_pos.mpr small
  have estimate : ‖u‖ ≤ (η/(1-η))*‖V.orthogonalProjectionOnto (u+w)‖ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ denominator).mpr
    nlinarith
  exact transverse.trans estimate

theorem one_eighth (V : Submodule ℝ E) (u w : E) (member : w ∈ V)
    (error : ‖u‖ ≤ (1/16:ℝ)*‖w‖) :
    ‖Vᗮ.orthogonalProjectionOnto (u+w)‖ ≤
      (1/8:ℝ)*‖V.orthogonalProjectionOnto (u+w)‖ := by
  have estimate := bound V u w member (1/16) (by norm_num) (by norm_num) error
  rw [show ((1/16:ℝ)/(1-1/16))=1/15 by norm_num] at estimate
  exact estimate.trans (mul_le_mul_of_nonneg_right (show (1/15:ℝ)≤1/8 by norm_num) (norm_nonneg _))
end LeanShared.OrthogonalSlopeFromDecomposition
