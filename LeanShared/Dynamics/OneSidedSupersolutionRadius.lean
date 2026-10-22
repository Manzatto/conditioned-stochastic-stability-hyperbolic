module

public import LeanShared.Dynamics.OneSidedAbelRadius

/-! An actual positive supersolution controls all literal transfer
coefficients and therefore proves a lower bound for their convergence
radius.  This is the order estimate used to derive Abel boundary blowup.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function PositiveContinuousOperatorNorm
open scoped NNReal ENNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

theorem weightedIterateOne_le_supersolution (ψ h : C(FuturePath R, ℝ)) (q : ℝ)
    (nonnegativeQ : 0 ≤ q) (majorant : ∀ a, 1 ≤ h a)
    (supersolution : ∀ a, weightedTransferOperator ψ h a ≤ q * h a)
    (m : ℕ) (a : FuturePath R) : weightedIterateOne ψ m a ≤ q ^ m * h a := by
  induction m generalizing a with
  | zero => change 1 ≤ q ^ 0 * h a; simpa only [pow_zero, one_mul] using majorant a
  | succ m induction =>
    rw [← weightedTransferOperator_iterateOne]
    calc
      _ ≤ weightedTransferOperator ψ (q ^ m • h) a :=
        monotone_apply _ (weightedTransferOperator_positive ψ) _ _
          (fun b => by change weightedIterateOne ψ m b ≤ q ^ m * h b; exact induction b) a
      _ = q ^ m * weightedTransferOperator ψ h a := by
        rw [map_smul]
        rfl
      _ ≤ q ^ m * (q * h a) := mul_le_mul_of_nonneg_left (supersolution a) (pow_nonneg nonnegativeQ m)
      _ = q ^ (m + 1) * h a := by rw [pow_succ]; ring

theorem weightedIterateOne_norm_le_supersolution (ψ h : C(FuturePath R, ℝ)) (q : ℝ)
    (nonnegativeQ : 0 ≤ q) (majorant : ∀ a, 1 ≤ h a)
    (supersolution : ∀ a, weightedTransferOperator ψ h a ≤ q * h a)
    (m : ℕ) : ‖weightedIterateOne ψ m‖ ≤ ‖h‖ * q ^ m := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (pow_nonneg nonnegativeQ m))).mpr
  intro a
  have positive : 0 ≤ weightedIterateOne ψ m a := weightedTransfer_iterate_one_nonnegative ψ m a
  rw [Real.norm_eq_abs, abs_of_nonneg positive]
  calc
    _ ≤ q ^ m * h a := weightedIterateOne_le_supersolution ψ h q nonnegativeQ majorant supersolution m a
    _ ≤ q ^ m * ‖h‖ := mul_le_mul_of_nonneg_left (ContinuousMap.apply_le_norm h a) (pow_nonneg nonnegativeQ m)
    _ = _ := mul_comm _ _

theorem abelRadius_lower_of_supersolution (ψ h : C(FuturePath R, ℝ)) (q : ℝ)
    (positiveQ : 0 < q) (majorant : ∀ a, 1 ≤ h a)
    (supersolution : ∀ a, weightedTransferOperator ψ h a ≤ q * h a) :
    (((Real.toNNReal q)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ abelRadius ψ := by
  apply (abelNormSeries ψ).le_radius_of_bound ‖h‖
  intro m
  simp only [abelNormSeries, FormalMultilinearSeries.ofScalars_norm, norm_norm, NNReal.coe_inv,
    Real.coe_toNNReal q positiveQ.le]
  calc
    _ ≤ (‖h‖ * q ^ m) * (q⁻¹) ^ m :=
      mul_le_mul_of_nonneg_right
        (weightedIterateOne_norm_le_supersolution ψ h q positiveQ.le majorant supersolution m)
        (pow_nonneg (inv_nonneg.mpr positiveQ.le) m)
    _ = ‖h‖ := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ positiveQ.ne', one_pow, mul_one]

end LeanShared.BilateralShadowingCoding
