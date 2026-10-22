module

public import LeanShared.Analysis.RectangularJacobianBounds
public import LeanShared.Analysis.NearIdentityEquivalenceBounds
public import Mathlib.Analysis.Normed.Ring.Units

/-! Genuine determinant factors in periodic return denominators. The
unstable factor splits off its volume expansion exactly; norm-small
remaining factors have derived upper and reciprocal bounds. -/
public noncomputable section
namespace LeanShared.NormDetOneSub
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

theorem factor (A : U ≃L[ℝ] U) :
    (ContinuousLinearMap.id ℝ U - A.toContinuousLinearMap).toLinearMap.normDet =
      A.toLinearMap.normDet *
        (ContinuousLinearMap.id ℝ U - A.symm.toContinuousLinearMap).toLinearMap.normDet := by
  have identity : (ContinuousLinearMap.id ℝ U - A.toContinuousLinearMap).toLinearMap =
      (-A.toLinearMap).comp (ContinuousLinearMap.id ℝ U - A.symm.toContinuousLinearMap).toLinearMap := by
    ext v
    change v - A v = -(A (v - A.symm v))
    rw [map_sub, A.apply_symm_apply, neg_sub]
  rw [identity, LinearMap.normDet_comp_of_finrank_eq _ _ rfl, LinearMap.normDet_neg]

theorem upper (A : U →L[ℝ] U) {κ : ℝ} (bound : ‖A‖ ≤ κ) :
    (ContinuousLinearMap.id ℝ U - A).toLinearMap.normDet ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 + κ) := by
  have nonnegative : 0 ≤ κ := (norm_nonneg A).trans bound
  apply RectangularJacobianBounds.normDet_le (stdOrthonormalBasis ℝ U) _ (by positivity)
  intro i
  change ‖(stdOrthonormalBasis ℝ U) i - A ((stdOrthonormalBasis ℝ U) i)‖ ≤ _
  calc
    _ ≤ ‖(stdOrthonormalBasis ℝ U) i‖ + ‖A ((stdOrthonormalBasis ℝ U) i)‖ := norm_sub_le _ _
    _ ≤ 1 + κ := by
      rw [OrthonormalBasis.norm_eq_one]
      have estimate := A.le_opNorm ((stdOrthonormalBasis ℝ U) i)
      rw [OrthonormalBasis.norm_eq_one, mul_one] at estimate
      linarith

theorem reciprocal_bound (A : U →L[ℝ] U) {κ : ℝ} (small : κ < 1) (bound : ‖A‖ ≤ κ) :
    1 ≤ GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) *
      (ContinuousLinearMap.id ℝ U - A).toLinearMap.normDet := by
  let unit := Units.oneSub A (bound.trans_lt small)
  let R := ContinuousLinearEquiv.unitsEquiv ℝ U unit
  have same : R.toContinuousLinearMap = ContinuousLinearMap.id ℝ U - A := by
    ext v
    change (unit : U →L[ℝ] U) v = _
    rw [show (unit : U →L[ℝ] U) = 1 - A from Units.val_oneSub A (bound.trans_lt small)]
    rfl
  have close : ‖R.toContinuousLinearMap - ContinuousLinearMap.id ℝ U‖ ≤ κ := by
    rw [same, sub_sub_cancel_left]
    exact (norm_neg A).trans_le bound
  have inverse := NearIdentityEquivalenceBounds.inverse_norm_le R κ small close
  have inverseBound : R.symm.toLinearMap.normDet ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) (1 / (1 - κ)) := by
    apply RectangularJacobianBounds.normDet_le (stdOrthonormalBasis ℝ U)
      R.symm.toContinuousLinearMap (by positivity)
    intro i
    have estimate := R.symm.toContinuousLinearMap.le_opNorm ((stdOrthonormalBasis ℝ U) i)
    rw [OrthonormalBasis.norm_eq_one, mul_one] at estimate
    exact estimate.trans inverse
  have identity : R.symm.toLinearMap.comp R.toLinearMap = LinearMap.id := by
    ext v
    exact R.symm_apply_apply v
  have product : R.symm.toLinearMap.normDet * R.toLinearMap.normDet = 1 := by
    rw [← LinearMap.normDet_comp_of_finrank_eq _ _ rfl, identity, LinearMap.normDet_id]
  rw [← same]
  exact product.symm.trans_le (mul_le_mul_of_nonneg_right inverseBound (LinearMap.normDet_nonneg _))

end LeanShared.NormDetOneSub
