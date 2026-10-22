module

public import LeanShared.Analysis.NearIdentityEquivalenceBounds
public import Mathlib.Analysis.Normed.Ring.Units

/-! Construct an actual inverse for a normalized small perturbation, with
a quantitative inverse bound. -/
public noncomputable section
namespace LeanShared.PerturbedLinearEquivalence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_equivalence (A : E ≃L[ℝ] E) (B : E →L[ℝ] E) (δ : ℝ)
    (small : δ < 1) (close : ‖A.symm.toContinuousLinearMap.comp (B - A.toContinuousLinearMap)‖ ≤ δ) :
    ∃ C : E ≃L[ℝ] E, C.toContinuousLinearMap = B ∧
      ‖C.symm.toContinuousLinearMap‖ ≤ (1 / (1 - δ)) * ‖A.symm.toContinuousLinearMap‖ := by
  let D := A.symm.toContinuousLinearMap.comp (B - A.toContinuousLinearMap)
  have normSmall : ‖-D‖ < 1 := (norm_neg D).trans_lt (close.trans_lt small)
  let unit := Units.oneSub (-D) normSmall
  let R := ContinuousLinearEquiv.unitsEquiv ℝ E unit
  have same : R.toContinuousLinearMap = ContinuousLinearMap.id ℝ E + D := by
    ext x
    change (unit : E →L[ℝ] E) x = x + D x
    rw [show (unit : E →L[ℝ] E) = 1 - (-D) from Units.val_oneSub (-D) normSmall]
    simp only [sub_neg_eq_add, add_apply, one_apply_eq_self]
  have bound : ‖R.toContinuousLinearMap - ContinuousLinearMap.id ℝ E‖ ≤ δ := by
    rw [same, add_sub_cancel_left]
    exact close
  let C := R.trans A
  refine ⟨C, ?_, ?_⟩
  · ext x
    change A (R x) = B x
    have action := congrArg (fun F : E →L[ℝ] E => F x) same
    change R x = x + A.symm (B x - A x) at action
    rw [action, map_add, A.apply_symm_apply]
    exact add_sub_cancel _ _
  · change ‖R.symm.toContinuousLinearMap.comp A.symm.toContinuousLinearMap‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (NearIdentityEquivalenceBounds.inverse_norm_le R δ small bound)
        (norm_nonneg _))

/-- Preserve the small-perturbation bijectivity interface used by the actual
Whitney-noise differential construction. -/
theorem bijective (A : E ≃L[ℝ] E) (B : E →L[ℝ] E)
    (small : ‖A.symm.toContinuousLinearMap‖ * ‖B-A.toContinuousLinearMap‖<1) :
    Function.Bijective B := by
  obtain ⟨C,equal,_⟩ := exists_equivalence A B
    (‖A.symm.toContinuousLinearMap‖ * ‖B-A.toContinuousLinearMap‖) small
    (ContinuousLinearMap.opNorm_comp_le _ _)
  have same : (C:E→E)=(B:E→E) := congrArg DFunLike.coe equal
  exact same ▸ C.bijective

end LeanShared.PerturbedLinearEquivalence
