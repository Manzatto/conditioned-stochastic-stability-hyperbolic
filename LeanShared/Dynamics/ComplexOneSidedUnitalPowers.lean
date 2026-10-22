module

public import LeanShared.Dynamics.ComplexOneSidedRealImag

/-! Actual complex transfer powers obey uniform physical bounds and
the sharp all-power prefix estimate, by exact real/imaginary compatibility.
The harmless factor two is independent of the iterate length.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

theorem complexUnitalTransfer_power_norm_le (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ))
    (unital : weightedTransferOperator ψ 1 = 1) (m : ℕ) :
    ‖((complexWeightedTransferOperator ψ) ^ m) f‖ ≤ 2 * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro a
  let z := ((complexWeightedTransferOperator ψ) ^ m) f a
  have realIdentity := congrArg (fun g : C(FuturePath R, ℝ) => g a) (complexWeightedTransfer_power_real ψ f m)
  have imagIdentity := congrArg (fun g : C(FuturePath R, ℝ) => g a) (complexWeightedTransfer_power_imag ψ f m)
  change z.re = ((weightedTransferOperator ψ) ^ m) (complexFunctionReal f) a at realIdentity
  change z.im = ((weightedTransferOperator ψ) ^ m) (complexFunctionImag f) a at imagIdentity
  have realBound : |z.re| ≤ ‖f‖ := by
    rw [realIdentity]
    exact (ContinuousMap.norm_coe_le_norm _ _).trans
      ((unitalWeightedTransfer_power_norm_le ψ (complexFunctionReal f) unital m).trans (complexFunctionReal_norm_le f))
  have imagBound : |z.im| ≤ ‖f‖ := by
    rw [imagIdentity]
    exact (ContinuousMap.norm_coe_le_norm _ _).trans
      ((unitalWeightedTransfer_power_norm_le ψ (complexFunctionImag f) unital m).trans (complexFunctionImag_norm_le f))
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

theorem complexUnitalTransfer_power_variation (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ))
    (θ Cψ Cf : ℝ) (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (observable : ∀ n a b, PrefixAgreement a b n → ‖f b - f a‖ ≤ Cf * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1)
    (m n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    ‖((complexWeightedTransferOperator ψ) ^ m) f b - ((complexWeightedTransferOperator ψ) ^ m) f a‖ ≤
      (2 * θ ^ m * Cf + (2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ))) * ‖f‖) * θ ^ n := by
  let B := θ * (Real.exp Cψ * Cψ) / (1 - θ)
  have nonnegativeB : 0 ≤ B := div_nonneg (mul_nonneg nonnegativeθ (mul_nonneg (Real.exp_pos _).le nonnegativeψ))
    (sub_pos.mpr smallθ).le
  have realVariation : ∀ k x y, PrefixAgreement x y k →
      |complexFunctionReal f y - complexFunctionReal f x| ≤ Cf * θ ^ k :=
    fun k x y matching => (complexFunctionReal_increment f x y).trans (observable k x y matching)
  have imagVariation : ∀ k x y, PrefixAgreement x y k →
      |complexFunctionImag f y - complexFunctionImag f x| ≤ Cf * θ ^ k :=
    fun k x y matching => (complexFunctionImag_increment f x y).trans (observable k x y matching)
  have realBound := unitalWeightedTransfer_power_variation ψ (complexFunctionReal f) θ Cψ Cf
    nonnegativeθ smallθ nonnegativeψ potential realVariation unital m n a b same
  have imagBound := unitalWeightedTransfer_power_variation ψ (complexFunctionImag f) θ Cψ Cf
    nonnegativeθ smallθ nonnegativeψ potential imagVariation unital m n a b same
  have coefficientReal : (θ ^ m * Cf + B * ‖complexFunctionReal f‖) * θ ^ n ≤
      (θ ^ m * Cf + B * ‖f‖) * θ ^ n :=
    mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (complexFunctionReal_norm_le f) nonnegativeB)) (pow_nonneg nonnegativeθ n)
  have coefficientImag : (θ ^ m * Cf + B * ‖complexFunctionImag f‖) * θ ^ n ≤
      (θ ^ m * Cf + B * ‖f‖) * θ ^ n :=
    mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (complexFunctionImag_norm_le f) nonnegativeB)) (pow_nonneg nonnegativeθ n)
  let z := ((complexWeightedTransferOperator ψ) ^ m) f b - ((complexWeightedTransferOperator ψ) ^ m) f a
  have realIdentity : z.re = ((weightedTransferOperator ψ) ^ m) (complexFunctionReal f) b -
      ((weightedTransferOperator ψ) ^ m) (complexFunctionReal f) a := by
    change Complex.re (((complexWeightedTransferOperator ψ) ^ m) f b -
      ((complexWeightedTransferOperator ψ) ^ m) f a) = _
    rw [Complex.sub_re]
    have atB := congrArg (fun g : C(FuturePath R, ℝ) => g b) (complexWeightedTransfer_power_real ψ f m)
    have atA := congrArg (fun g : C(FuturePath R, ℝ) => g a) (complexWeightedTransfer_power_real ψ f m)
    exact congrArg₂ (· - ·) atB atA
  have imagIdentity : z.im = ((weightedTransferOperator ψ) ^ m) (complexFunctionImag f) b -
      ((weightedTransferOperator ψ) ^ m) (complexFunctionImag f) a := by
    change Complex.im (((complexWeightedTransferOperator ψ) ^ m) f b -
      ((complexWeightedTransferOperator ψ) ^ m) f a) = _
    rw [Complex.sub_im]
    have atB := congrArg (fun g : C(FuturePath R, ℝ) => g b) (complexWeightedTransfer_power_imag ψ f m)
    have atA := congrArg (fun g : C(FuturePath R, ℝ) => g a) (complexWeightedTransfer_power_imag ψ f m)
    exact congrArg₂ (· - ·) atB atA
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ (θ ^ m * Cf + B * ‖f‖) * θ ^ n + (θ ^ m * Cf + B * ‖f‖) * θ ^ n := by
      rw [realIdentity, imagIdentity]
      exact add_le_add (realBound.trans coefficientReal) (imagBound.trans coefficientImag)
    _ = _ := by ring

end LeanShared.BilateralShadowingCoding
