module

public import LeanShared.Dynamics.ComplexOneSidedWeightedTransfer
public import LeanShared.Dynamics.OneSidedUnitalTransferPowers

/-! Exact compatibility of the literal complex transfer powers with
their real and imaginary parts.  The pointwise component maps contract
the physical uniform norm and every prefix difference.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
  {R : A → A → Prop}

@[expose] def complexFunctionReal (f : C(FuturePath R, ℂ)) : C(FuturePath R, ℝ) :=
  ⟨fun a => (f a).re, Complex.continuous_re.comp f.continuous⟩

@[expose] def complexFunctionImag (f : C(FuturePath R, ℂ)) : C(FuturePath R, ℝ) :=
  ⟨fun a => (f a).im, Complex.continuous_im.comp f.continuous⟩

theorem complexFunctionReal_norm_le (f : C(FuturePath R, ℂ)) : ‖complexFunctionReal f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro a
  exact (Complex.abs_re_le_norm (f a)).trans (f.norm_coe_le_norm a)

theorem complexFunctionImag_norm_le (f : C(FuturePath R, ℂ)) : ‖complexFunctionImag f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro a
  exact (Complex.abs_im_le_norm (f a)).trans (f.norm_coe_le_norm a)

omit [DiscreteTopology A] [CompactSpace A] in
theorem complexFunctionReal_increment (f : C(FuturePath R, ℂ)) (a b : FuturePath R) :
    |complexFunctionReal f b - complexFunctionReal f a| ≤ ‖f b - f a‖ := by
  simpa only [complexFunctionReal, ContinuousMap.coe_mk, Complex.sub_re] using Complex.abs_re_le_norm (f b - f a)

omit [DiscreteTopology A] [CompactSpace A] in
theorem complexFunctionImag_increment (f : C(FuturePath R, ℂ)) (a b : FuturePath R) :
    |complexFunctionImag f b - complexFunctionImag f a| ≤ ‖f b - f a‖ := by
  simpa only [complexFunctionImag, ContinuousMap.coe_mk, Complex.sub_im] using Complex.abs_im_le_norm (f b - f a)

variable [Fintype A]

theorem complexWeightedTransfer_power_real (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ)) (m : ℕ) :
    complexFunctionReal (((complexWeightedTransferOperator ψ) ^ m) f) =
      ((weightedTransferOperator ψ) ^ m) (complexFunctionReal f) := by
  induction m with
  | zero => rfl
  | succ m induction =>
    rw [pow_succ', pow_succ']
    apply ContinuousMap.ext
    intro a
    change (complexWeightedTransfer ψ (((complexWeightedTransferOperator ψ) ^ m) f) a).re = _
    rw [complexWeightedTransfer_re]
    change weightedTransferOperator ψ (complexFunctionReal (((complexWeightedTransferOperator ψ) ^ m) f)) a = _
    rw [induction]
    rfl

theorem complexWeightedTransfer_power_imag (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ)) (m : ℕ) :
    complexFunctionImag (((complexWeightedTransferOperator ψ) ^ m) f) =
      ((weightedTransferOperator ψ) ^ m) (complexFunctionImag f) := by
  induction m with
  | zero => rfl
  | succ m induction =>
    rw [pow_succ', pow_succ']
    apply ContinuousMap.ext
    intro a
    change (complexWeightedTransfer ψ (((complexWeightedTransferOperator ψ) ^ m) f) a).im = _
    rw [complexWeightedTransfer_im]
    change weightedTransferOperator ψ (complexFunctionImag (((complexWeightedTransferOperator ψ) ^ m) f)) a = _
    rw [induction]
    rfl

end LeanShared.BilateralShadowingCoding
