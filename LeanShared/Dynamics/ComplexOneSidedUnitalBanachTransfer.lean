module

public import LeanShared.Dynamics.ComplexOneSidedUnitalPowers
public import LeanShared.Dynamics.ComplexOneSidedVariationBanach

/-! The literal unital complex weighted transfer acts boundedly on the
concrete complex prefix Banach space.  Faithful physical realization
retains exact operator powers, with no assumed spectral conclusion.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

theorem complexUnitalVariation_increment (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (v : complexVariationGraph R θ)
    (n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    ‖complexWeightedTransferOperator ψ (complexVariationPhysical θ v) b -
      complexWeightedTransferOperator ψ (complexVariationPhysical θ v) a‖ ≤
      (2 * (θ + θ * (Real.exp Cψ * Cψ) / (1 - θ)) * ‖v‖) * θ ^ n := by
  let B := θ * (Real.exp Cψ * Cψ) / (1 - θ)
  have nonnegativeB : 0 ≤ B := by dsimp only [B]; positivity
  have estimate := complexUnitalTransfer_power_variation ψ (complexVariationPhysical θ v) θ Cψ ‖v‖
    positiveθ.le smallθ nonnegativeψ potential (complexVariationPhysical_increment θ positiveθ.le v)
    unital 1 n a b same
  rw [pow_one, pow_one] at estimate
  apply estimate.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg positiveθ.le n)
  have physicalNorm := complexVariationPhysical_norm_le θ v
  have weakBound := mul_le_mul_of_nonneg_left physicalNorm (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nonnegativeB)
  change 2 * θ * ‖v‖ + (2 * B) * ‖complexVariationPhysical θ v‖ ≤ 2 * (θ + B) * ‖v‖
  nlinarith [weakBound]

@[expose] def complexUnitalVariationTransfer (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (v : complexVariationGraph R θ) : complexVariationGraph R θ :=
  complexVariationElement θ positiveθ (complexWeightedTransferOperator ψ (complexVariationPhysical θ v))
    (2 * (θ + θ * (Real.exp Cψ * Cψ) / (1 - θ)) * ‖v‖) (by positivity)
    (complexUnitalVariation_increment ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v)

theorem complexUnitalVariationTransfer_physical (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (v : complexVariationGraph R θ) :
    complexVariationPhysical θ (complexUnitalVariationTransfer ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v) =
      complexWeightedTransferOperator ψ (complexVariationPhysical θ v) := rfl

@[expose] def complexUnitalVariationLinear (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) : complexVariationGraph R θ →ₗ[ℂ] complexVariationGraph R θ where
  toFun := complexUnitalVariationTransfer ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
  map_add' v w := by
    apply complexVariationPhysical_injective θ positiveθ
    rw [map_add, complexUnitalVariationTransfer_physical, complexUnitalVariationTransfer_physical,
      complexUnitalVariationTransfer_physical, map_add, map_add]
  map_smul' c v := by
    apply complexVariationPhysical_injective θ positiveθ
    rw [map_smul, complexUnitalVariationTransfer_physical, complexUnitalVariationTransfer_physical,
      map_smul, map_smul]
    rfl

theorem complexUnitalVariationLinear_norm (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (v : complexVariationGraph R θ) :
    ‖complexUnitalVariationLinear ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v‖ ≤
      (2 + 2 * (θ + θ * (Real.exp Cψ * Cψ) / (1 - θ))) * ‖v‖ := by
  let K := 2 * (θ + θ * (Real.exp Cψ * Cψ) / (1 - θ))
  have nonnegativeK : 0 ≤ K := by dsimp only [K]; positivity
  have physicalNorm : ‖complexWeightedTransferOperator ψ (complexVariationPhysical θ v)‖ ≤ 2 * ‖v‖ := by
    have bound := complexUnitalTransfer_power_norm_le ψ (complexVariationPhysical θ v) unital 1
    rw [pow_one] at bound
    exact bound.trans (mul_le_mul_of_nonneg_left (complexVariationPhysical_norm_le θ v) (by norm_num))
  change ‖complexUnitalVariationTransfer ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v‖ ≤ _
  apply (complexVariationElement_norm_le θ positiveθ (complexWeightedTransferOperator ψ (complexVariationPhysical θ v))
    (K * ‖v‖) (by positivity)
    (complexUnitalVariation_increment ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v)).trans
  apply max_le
  · change ‖complexWeightedTransferOperator ψ (complexVariationPhysical θ v)‖ ≤ (2 + K) * ‖v‖
    exact physicalNorm.trans (by nlinarith [mul_nonneg nonnegativeK (norm_nonneg v)])
  · change K * ‖v‖ ≤ (2 + K) * ‖v‖
    nlinarith [norm_nonneg v]

@[expose] def complexUnitalVariationOperator (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) : complexVariationGraph R θ →L[ℂ] complexVariationGraph R θ :=
  (complexUnitalVariationLinear ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital).mkContinuous
    (2 + 2 * (θ + θ * (Real.exp Cψ * Cψ) / (1 - θ)))
    (complexUnitalVariationLinear_norm ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)

end LeanShared.BilateralShadowingCoding
