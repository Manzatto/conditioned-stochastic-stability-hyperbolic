module

public import LeanShared.Dynamics.OneSidedUnitalTransferVariation
public import LeanShared.Dynamics.OneSidedTransferGrowth

/-! The actual unital weighted transfer is a uniform-norm contraction.
Its arbitrary iterates satisfy the sharp prefix Lasota estimate with
strong decay θ^n and a bounded weak term.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function PositiveContinuousOperatorNorm
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

theorem unitalWeightedTransfer_norm (ψ : C(FuturePath R, ℝ))
    (unital : weightedTransferOperator ψ 1 = 1) : ‖weightedTransferOperator ψ‖ = 1 := by
  rw [norm_eq_image_one _ (weightedTransferOperator_positive ψ), unital, norm_one]

theorem unitalWeightedTransfer_power_norm_le (ψ f : C(FuturePath R, ℝ))
    (unital : weightedTransferOperator ψ 1 = 1) (m : ℕ) :
    ‖((weightedTransferOperator ψ) ^ m) f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖(weightedTransferOperator ψ) ^ m‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖weightedTransferOperator ψ‖ ^ m * ‖f‖ :=
      mul_le_mul_of_nonneg_right (norm_pow_le (weightedTransferOperator ψ) m) (norm_nonneg f)
    _ = _ := by rw [unitalWeightedTransfer_norm ψ unital, one_pow, one_mul]

theorem unitalWeightedTransfer_power_variation (ψ f : C(FuturePath R, ℝ)) (θ Cψ Cf : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (variationψ : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (variationF : ∀ n a b, PrefixAgreement a b n → |f b - f a| ≤ Cf * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1)
    (m n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    |((weightedTransferOperator ψ) ^ m) f b - ((weightedTransferOperator ψ) ^ m) f a| ≤
      (θ ^ m * Cf + (θ * (Real.exp Cψ * Cψ) / (1 - θ)) * ‖f‖) * θ ^ n := by
  let D := Real.exp Cψ * Cψ
  let B := θ * D / (1 - θ)
  have nonnegativeD : 0 ≤ D := mul_nonneg (Real.exp_pos _).le nonnegativeψ
  have nonnegativeB : 0 ≤ B := div_nonneg (mul_nonneg nonnegativeθ nonnegativeD) (sub_pos.mpr smallθ).le
  have invariant : θ * B + θ * D = B := by
    dsimp only [B]
    field_simp [(sub_pos.mpr smallθ).ne']
    ring
  induction m generalizing n a b with
  | zero =>
    change |f b - f a| ≤ (1 * Cf + B * ‖f‖) * θ ^ n
    exact (variationF n a b same).trans (mul_le_mul_of_nonneg_right
      (by simpa only [one_mul] using le_add_of_nonneg_right (mul_nonneg nonnegativeB (norm_nonneg f)))
      (pow_nonneg nonnegativeθ n))
  | succ m induction =>
    let g := ((weightedTransferOperator ψ) ^ m) f
    have bound := unitalWeightedTransfer_variation ψ g θ Cψ (θ ^ m * Cf + B * ‖f‖)
      nonnegativeθ smallθ.le nonnegativeψ variationψ (fun n a b matching => induction n a b matching)
      unital n a b same
    rw [pow_succ']
    change |weightedTransfer ψ g b - weightedTransfer ψ g a| ≤ _
    apply bound.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg nonnegativeθ n)
    have contraction : ‖g‖ ≤ ‖f‖ := unitalWeightedTransfer_power_norm_le ψ f unital m
    have weakBound := mul_le_mul_of_nonneg_left contraction (mul_nonneg nonnegativeθ nonnegativeD)
    change θ * (θ ^ m * Cf + B * ‖f‖) + θ * D * ‖g‖ ≤ θ ^ (m + 1) * Cf + B * ‖f‖
    calc
      _ ≤ θ * (θ ^ m * Cf + B * ‖f‖) + θ * D * ‖f‖ := add_le_add le_rfl weakBound
      _ = θ ^ (m + 1) * Cf + (θ * B + θ * D) * ‖f‖ := by rw [pow_succ]; ring
      _ = _ := by rw [invariant]

end LeanShared.BilateralShadowingCoding
