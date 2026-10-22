module
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! The positive definite inner product induced by an actual injective
finite-dimensional differential has bounded unit ball for the original
fiber topology. This supplies the topology condition in a reference metric. -/
public noncomputable section
namespace LeanShared.ImmersionPullbackInner
open Set
variable {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[expose] def form (A : H →L[ℝ] F) : H →L[ℝ] H →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompR H (innerSL ℝ)).flip A).comp A

omit [FiniteDimensional ℝ H] in
@[simp] theorem form_apply (A : H →L[ℝ] F) (v w : H) :
    form A v w = inner ℝ (A v) (A w) := rfl

omit [FiniteDimensional ℝ H] in
theorem symm (A : H →L[ℝ] F) (v w : H) : form A v w = form A w v := real_inner_comm _ _

omit [FiniteDimensional ℝ H] in
theorem positive (A : H →L[ℝ] F) (injective : Function.Injective A) (v : H) (hv : v ≠ 0) :
    0 < form A v v := by
  rw [form_apply,real_inner_self_pos]
  exact fun zero => hv (injective (zero.trans A.map_zero.symm))

theorem unit_isVonNBounded (A : H →L[ℝ] F) (injective : Function.Injective A) :
    Bornology.IsVonNBounded ℝ {v : H | form A v v < 1} := by
  obtain ⟨K,_hK,anti⟩ := A.toLinearMap.injective_iff_antilipschitz.mp injective
  apply NormedSpace.isVonNBounded_of_isBounded
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨K,fun v hv => ?_⟩
  have square : ‖A v‖^2 < 1 := by simpa only [Set.mem_ofPred_eq,form_apply,real_inner_self_eq_norm_sq] using hv
  have small : ‖A v‖ ≤ 1 := by nlinarith [norm_nonneg (A v)]
  have bound : ‖v‖ ≤ K*‖A v‖ := by simpa only [dist_zero_right,map_zero,ContinuousLinearMap.coe_coe] using anti.le_mul_dist v 0
  exact bound.trans ((mul_le_mul_of_nonneg_left small K.coe_nonneg).trans_eq (mul_one _))

end LeanShared.ImmersionPullbackInner
