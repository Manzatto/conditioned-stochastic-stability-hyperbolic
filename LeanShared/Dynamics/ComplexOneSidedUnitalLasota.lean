module

public import LeanShared.Dynamics.ComplexOneSidedUnitalBanachTransfer
public import LeanShared.Dynamics.ComplexOneSidedCylinderApproximation

/-! The actual complex Banach transfer has the all-power two-norm
Lasota estimate with strong rate θ and weak rate one, as well as a
uniform bound on every actual Banach operator power.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
  {R : A → A → Prop}

local instance complexLasotaGraphNorm (θ : ℝ) : NormedAddCommGroup (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedAddCommGroup
local instance complexLasotaGraphSpace (θ : ℝ) : NormedSpace ℂ (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedSpace
local instance complexLasotaContinuousNorm : NormedAddCommGroup C(FuturePath R, ℂ) :=
  ContinuousMap.instNormedAddCommGroup
local instance complexLasotaContinuousSpace : NormedSpace ℂ C(FuturePath R, ℂ) :=
  ContinuousMap.normedSpace

theorem complexVariationGraph_norm_le_of_increment (θ : ℝ) (positiveθ : 0 < θ)
    (v : complexVariationGraph R θ) (C : ℝ) (nonnegativeC : 0 ≤ C)
    (bound : ∀ n a b, PrefixAgreement a b n →
      ‖complexVariationPhysical θ v b - complexVariationPhysical θ v a‖ ≤ C * θ ^ n) :
    ‖v‖ ≤ max ‖complexVariationPhysical θ v‖ C := by
  have identity : v = complexVariationElement θ positiveθ (complexVariationPhysical θ v) C nonnegativeC bound := by
    apply complexVariationPhysical_injective θ positiveθ
    rfl
  conv_lhs => rw [identity]
  exact complexVariationElement_norm_le θ positiveθ (complexVariationPhysical θ v) C nonnegativeC bound

variable [Fintype A] [Nonempty (FuturePath R)]

theorem complexUnitalVariation_power_physical (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (m : ℕ) (v : complexVariationGraph R θ) :
    complexVariationPhysical θ (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) ^ m) v) =
      ((complexWeightedTransferOperator ψ) ^ m) (complexVariationPhysical θ v) := by
  induction m with
  | zero => rfl
  | succ m induction =>
    rw [pow_succ', pow_succ']
    change complexVariationPhysical θ (complexUnitalVariationTransfer ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
      (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) ^ m) v)) =
      complexWeightedTransferOperator ψ (((complexWeightedTransferOperator ψ) ^ m) (complexVariationPhysical θ v))
    rw [complexUnitalVariationTransfer_physical, induction]

theorem complexUnitalVariation_lasota (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (m : ℕ) (v : complexVariationGraph R θ) :
    ‖((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) ^ m) v‖ ≤
      2 * θ ^ m * ‖v‖ + (2 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ))) * ‖complexVariationPhysical θ v‖ := by
  let B := θ * (Real.exp Cψ * Cψ) / (1 - θ)
  have nonnegativeB : 0 ≤ B := by dsimp only [B]; positivity
  let w := ((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) ^ m) v
  have physical : complexVariationPhysical θ w = ((complexWeightedTransferOperator ψ) ^ m) (complexVariationPhysical θ v) :=
    complexUnitalVariation_power_physical ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital m v
  have variation : ∀ n a b, PrefixAgreement a b n →
      ‖complexVariationPhysical θ w b - complexVariationPhysical θ w a‖ ≤
        (2 * θ ^ m * ‖v‖ + (2 * B) * ‖complexVariationPhysical θ v‖) * θ ^ n := by
    intro n a b same
    rw [physical]
    exact complexUnitalTransfer_power_variation ψ (complexVariationPhysical θ v) θ Cψ ‖v‖
      positiveθ.le smallθ nonnegativeψ potential (complexVariationPhysical_increment θ positiveθ.le v)
      unital m n a b same
  apply (complexVariationGraph_norm_le_of_increment θ positiveθ w
    (2 * θ ^ m * ‖v‖ + (2 * B) * ‖complexVariationPhysical θ v‖) (by positivity) variation).trans
  apply max_le
  · rw [physical]
    apply (complexUnitalTransfer_power_norm_le ψ (complexVariationPhysical θ v) unital m).trans
    change 2 * ‖complexVariationPhysical θ v‖ ≤ 2 * θ ^ m * ‖v‖ + (2 + 2 * B) * ‖complexVariationPhysical θ v‖
    nlinarith [mul_nonneg (pow_nonneg positiveθ.le m) (norm_nonneg v),
      mul_nonneg nonnegativeB (norm_nonneg (complexVariationPhysical θ v))]
  · change 2 * θ ^ m * ‖v‖ + (2 * B) * ‖complexVariationPhysical θ v‖ ≤
      2 * θ ^ m * ‖v‖ + (2 + 2 * B) * ‖complexVariationPhysical θ v‖
    nlinarith [norm_nonneg (complexVariationPhysical θ v)]

theorem complexUnitalVariation_power_norm_bound (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (m : ℕ) :
    ‖(complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) ^ m‖ ≤
      4 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ)) := by
  let B := θ * (Real.exp Cψ * Cψ) / (1 - θ)
  have nonnegativeB : 0 ≤ B := by dsimp only [B]; positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (complexUnitalVariation_lasota ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital m v).trans
  have physicalNorm := complexVariationPhysical_norm_le θ v
  have decay := pow_le_one₀ positiveθ.le smallθ.le (n := m)
  have first := mul_le_mul_of_nonneg_right decay (norm_nonneg v)
  have second := mul_le_mul_of_nonneg_left physicalNorm (by positivity : 0 ≤ 2 + 2 * B)
  change 2 * θ ^ m * ‖v‖ + (2 + 2 * B) * ‖complexVariationPhysical θ v‖ ≤ (4 + 2 * B) * ‖v‖
  nlinarith

end LeanShared.BilateralShadowingCoding
