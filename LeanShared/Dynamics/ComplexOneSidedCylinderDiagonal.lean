module

public import LeanShared.Dynamics.ComplexOneSidedCylinderIndicators
public import LeanShared.Dynamics.ComplexOneSidedExponentialConvergence

/-! The literal finite-cylinder diagonal sums of transfer powers
converge to one, with explicit cylinder-rank and strong-norm costs.
The leading coefficient one follows from the actual partition of unity.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

@[expose] def complexCylinderPowerDiagonal (ψ : C(FuturePath R, ℝ)) (m n : ℕ) : ℂ :=
  ∑ w : RealizedPrefix R m, ((complexWeightedTransferOperator ψ) ^ n)
    (complexCylinderIndicator m w) (prefixRepresentative m w)

local instance diagonalRuelleGraphNorm (θ : ℝ) : NormedAddCommGroup (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedAddCommGroup
local instance diagonalRuelleGraphSpace (θ : ℝ) : NormedSpace ℂ (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedSpace
local instance diagonalRuelleContinuousNorm : NormedAddCommGroup C(FuturePath R, ℂ) :=
  ContinuousMap.instNormedAddCommGroup
local instance diagonalRuelleContinuousSpace : NormedSpace ℂ C(FuturePath R, ℂ) :=
  ContinuousMap.normedSpace

theorem complexCylinderProjectorDiagonal_one (θ : ℝ) (positiveθ : 0 < θ) (smallθ : θ ≤ 1)
    (P : complexVariationGraph R θ →L[ℂ] complexVariationGraph R θ)
    (rangeLine : P.range = Submodule.span ℂ {complexConstantVariation (R := R) θ positiveθ 1})
    (idempotent : P * P = P) (m : ℕ) :
    (∑ w : RealizedPrefix R m, complexVariationPhysical θ
      (P (complexCylinderIndicatorVector θ positiveθ smallθ m w)) (prefixRepresentative m w)) = 1 := by
  have fixedOne : P (complexConstantVariation θ positiveθ 1) = complexConstantVariation θ positiveθ 1 := by
    have member : complexConstantVariation θ positiveθ 1 ∈ P.range := by
      rw [rangeLine]
      exact Submodule.subset_span (mem_singleton _)
    obtain ⟨v, preimage⟩ := member
    have identity := congrArg (fun Q : complexVariationGraph R θ →L[ℂ] complexVariationGraph R θ => Q v) idempotent
    change P (P v) = P v at identity
    have preimage' : P v = complexConstantVariation θ positiveθ 1 := preimage
    rw [preimage'] at identity
    exact identity
  obtain ⟨a⟩ := ‹Nonempty (FuturePath R)›
  have constant (w : RealizedPrefix R m) :
      complexVariationPhysical θ (P (complexCylinderIndicatorVector θ positiveθ smallθ m w))
        (prefixRepresentative m w) =
      complexVariationPhysical θ (P (complexCylinderIndicatorVector θ positiveθ smallθ m w)) a := by
    have member : P (complexCylinderIndicatorVector θ positiveθ smallθ m w) ∈ P.range := ⟨_, rfl⟩
    rw [rangeLine] at member
    obtain ⟨c, identity⟩ := Submodule.mem_span_singleton.mp member
    rw [← identity, map_smul, complexConstantVariation_physical]
    rfl
  have imageSum : (∑ w : RealizedPrefix R m, P (complexCylinderIndicatorVector θ positiveθ smallθ m w)) =
      complexConstantVariation θ positiveθ 1 := by
    rw [← map_sum, complexCylinderIndicatorVectors_sum_one, fixedOne]
  have physicalSum := congrArg (complexVariationPhysical θ) imageSum
  rw [map_sum, complexConstantVariation_physical] at physicalSum
  calc
    _ = ∑ w : RealizedPrefix R m, complexVariationPhysical θ
        (P (complexCylinderIndicatorVector θ positiveθ smallθ m w)) a := Finset.sum_congr rfl (fun w _ => constant w)
    _ = (∑ w : RealizedPrefix R m, complexVariationPhysical θ
        (P (complexCylinderIndicatorVector θ positiveθ smallθ m w))) a := (ContinuousMap.sum_apply _ _ _).symm
    _ = 1 := by rw [physicalSum]; rfl

theorem complexCylinderPowerDiagonal_error (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1)
    (P : complexVariationGraph R θ →L[ℂ] complexVariationGraph R θ)
    (rangeLine : P.range = Submodule.span ℂ {complexConstantVariation (R := R) θ positiveθ 1})
    (idempotent : P * P = P) (m n : ℕ) :
    ‖complexCylinderPowerDiagonal ψ m n - 1‖ ≤
      (Fintype.card (RealizedPrefix R m) : ℝ) *
        ‖(complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) ^ n - P‖ *
          (2 * θ⁻¹ ^ m) := by
  let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
  have term (w : RealizedPrefix R m) :
      ‖((complexWeightedTransferOperator ψ) ^ n) (complexCylinderIndicator m w) (prefixRepresentative m w) -
        complexVariationPhysical θ (P (complexCylinderIndicatorVector θ positiveθ smallθ.le m w)) (prefixRepresentative m w)‖ ≤
        ‖T ^ n - P‖ * (2 * θ⁻¹ ^ m) := by
    let v := complexCylinderIndicatorVector θ positiveθ smallθ.le m w
    have identity : complexVariationPhysical θ ((T ^ n - P) v) =
        ((complexWeightedTransferOperator ψ) ^ n) (complexCylinderIndicator m w) - complexVariationPhysical θ (P v) := by
      rw [sub_apply, map_sub, complexUnitalVariation_power_physical,
        complexCylinderIndicatorVector_physical]
    calc
      _ = ‖complexVariationPhysical θ ((T ^ n - P) v) (prefixRepresentative m w)‖ := by rw [identity]; rfl
      _ ≤ ‖complexVariationPhysical θ ((T ^ n - P) v)‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖(T ^ n - P) v‖ := complexVariationPhysical_norm_le θ _
      _ ≤ ‖T ^ n - P‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖T ^ n - P‖ * (2 * θ⁻¹ ^ m) := mul_le_mul_of_nonneg_left
        (complexCylinderIndicatorVector_norm θ positiveθ smallθ.le m w) (norm_nonneg _)
  rw [← complexCylinderProjectorDiagonal_one θ positiveθ smallθ.le P rangeLine idempotent m]
  dsimp only [complexCylinderPowerDiagonal]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w : RealizedPrefix R m,
        ‖((complexWeightedTransferOperator ψ) ^ n) (complexCylinderIndicator m w) (prefixRepresentative m w) -
          complexVariationPhysical θ (P (complexCylinderIndicatorVector θ positiveθ smallθ.le m w)) (prefixRepresentative m w)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _w : RealizedPrefix R m, ‖T ^ n - P‖ * (2 * θ⁻¹ ^ m) := Finset.sum_le_sum (fun w _ => term w)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem actualRuelle_cylinder_diagonal_bound (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    ∃ τ C : ℝ, 0 < τ ∧ τ < 1 ∧ 0 < C ∧ ∀ m n : ℕ,
      ‖complexCylinderPowerDiagonal ψ m n - 1‖ ≤
        (Fintype.card (RealizedPrefix R m) : ℝ) * (2 * θ⁻¹ ^ m) * C * τ ^ n := by
  obtain ⟨ρ, τ, C, _, positiveτ, smallτ, positiveC, rangeLine, _, idempotent, _, _, bound⟩ :=
    actualRuelle_exponential_convergence ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital N connections nextConnections
  refine ⟨τ, C, positiveτ, smallτ, positiveC, ?_⟩
  intro m n
  apply (complexCylinderPowerDiagonal_error ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
    _ rangeLine idempotent m n).trans
  calc
    _ ≤ (Fintype.card (RealizedPrefix R m) : ℝ) * (C * τ ^ n) * (2 * θ⁻¹ ^ m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bound n) (by positivity)) (by positivity)
    _ = _ := by ring

end LeanShared.BilateralShadowingCoding
