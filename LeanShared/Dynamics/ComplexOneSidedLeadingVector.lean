module

public import LeanShared.Dynamics.ComplexOneSidedPeripheralSimplicity
public import LeanShared.Analysis.PowerBoundedFixedSemisimple

/-! The actual constant Banach eigenvector at one, and algebraic
semisimplicity of that eigenvalue from the proved uniform power bound.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
  {R : A → A → Prop}

@[expose] def complexConstantVariation (θ : ℝ) (positiveθ : 0 < θ) (c : ℂ) : complexVariationGraph R θ :=
  complexVariationElement θ positiveθ (ContinuousMap.const _ c) 0 le_rfl
    (fun _ _ _ _ => by simp only [ContinuousMap.const_apply, sub_self, norm_zero, zero_mul, le_refl])

omit [DiscreteTopology A] [CompactSpace A] in
theorem complexConstantVariation_physical (θ : ℝ) (positiveθ : 0 < θ) (c : ℂ) :
    complexVariationPhysical θ (complexConstantVariation (R := R) θ positiveθ c) = ContinuousMap.const _ c := rfl

variable [Fintype A]

theorem complexWeightedTransfer_one (ψ : C(FuturePath R, ℝ))
    (unital : weightedTransferOperator ψ 1 = 1) : complexWeightedTransferOperator ψ 1 = 1 := by
  classical
  apply ContinuousMap.ext
  intro a
  apply Complex.ext
  · change (complexWeightedTransfer ψ (fun _ => 1) a).re = 1
    rw [complexWeightedTransfer_re]
    have identity := congrArg (fun g : C(FuturePath R, ℝ) => g a) unital
    exact identity
  · change (complexWeightedTransfer ψ (fun _ => 1) a).im = 0
    rw [complexWeightedTransfer_im]
    simp only [Complex.one_im, weightedTransfer, mul_zero]
    apply Finset.sum_eq_zero
    intro j _
    by_cases edge : R j.val (a.val 0) <;>
      simp only [Set.indicator, mem_ofPred_eq, edge, ite_true, ite_false]

variable [Nonempty (FuturePath R)]

theorem complexUnitalVariation_constant_fixed (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (c : ℂ) :
    complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
      (complexConstantVariation θ positiveθ c) = complexConstantVariation θ positiveθ c := by
  apply complexVariationPhysical_injective θ positiveθ
  change complexVariationPhysical θ
    (complexUnitalVariationTransfer ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
      (complexConstantVariation θ positiveθ c)) = _
  rw [complexUnitalVariationTransfer_physical, complexConstantVariation_physical]
  have scalar : (ContinuousMap.const (FuturePath R) c : C(FuturePath R, ℂ)) = c • 1 := by
    apply ContinuousMap.ext
    intro a
    change c = c * 1
    exact (mul_one c).symm
  rw [scalar, map_smul, complexWeightedTransfer_one ψ unital]

theorem complexUnitalVariation_exists_fixed (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) :
    ∃ v : complexVariationGraph R θ, v ≠ 0 ∧
      complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v = v := by
  refine ⟨complexConstantVariation θ positiveθ 1, ?_, complexUnitalVariation_constant_fixed ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital 1⟩
  intro zero
  have identity := congrArg (complexVariationPhysical θ) zero
  rw [complexConstantVariation_physical, map_zero] at identity
  obtain ⟨a⟩ := ‹Nonempty (FuturePath R)›
  have impossible := congrArg (fun f : C(FuturePath R, ℂ) => f a) identity
  exact one_ne_zero impossible

theorem complexUnitalVariation_ker_fixed_square (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) :
    (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - 1) ^ 2).ker =
      ((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - 1).ker :=
  PowerBoundedFixedSemisimple.ker_fixed_square
    (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)
    (4 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ)))
    (complexUnitalVariation_power_norm_bound ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)

end LeanShared.BilateralShadowingCoding
