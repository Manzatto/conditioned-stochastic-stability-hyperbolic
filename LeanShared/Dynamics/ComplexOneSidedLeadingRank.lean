module

public import LeanShared.Dynamics.ComplexOneSidedLeadingVector

/-! The literal complex normalized Ruelle operator has a one-dimensional
fixed kernel.  Every generalized fixed kernel is the same line, by the
proved uniform power bound and the actual mixing graph classification.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

omit [DiscreteTopology A] [CompactSpace A] [Fintype A] [Nonempty (FuturePath R)] in
theorem complexConstantVariation_smul_one (θ : ℝ) (positiveθ : 0 < θ) (c : ℂ) :
    complexConstantVariation (R := R) θ positiveθ c = c • complexConstantVariation θ positiveθ 1 := by
  apply complexVariationPhysical_injective θ positiveθ
  rw [map_smul, complexConstantVariation_physical, complexConstantVariation_physical]
  apply ContinuousMap.ext
  intro a
  change c = c * 1
  exact (mul_one c).symm

omit [DiscreteTopology A] [CompactSpace A] [Fintype A] in
theorem complexConstantVariation_one_ne_zero (θ : ℝ) (positiveθ : 0 < θ) :
    complexConstantVariation (R := R) θ positiveθ 1 ≠ 0 := by
  intro zero
  have identity := congrArg (complexVariationPhysical θ) zero
  rw [complexConstantVariation_physical, map_zero] at identity
  obtain ⟨a⟩ := ‹Nonempty (FuturePath R)›
  have impossible := congrArg (fun f : C(FuturePath R, ℂ) => f a) identity
  exact one_ne_zero impossible

theorem complexUnitalVariation_fixed_classification (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1)
    (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j)
    (v : complexVariationGraph R θ)
    (fixed : complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v = v) :
    ∃ c : ℂ, v = c • complexConstantVariation θ positiveθ 1 := by
  by_cases zero : v = 0
  · exact ⟨0, by rw [zero, zero_smul]⟩
  · have eigen : complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v = (1 : ℂ) • v := by
      simpa only [one_smul] using fixed
    obtain ⟨_, c, constant⟩ := complexUnitalVariation_peripheral_simple ψ θ positiveθ smallθ Cψ nonnegativeψ
      potential unital v zero 1 (norm_one) eigen N connections nextConnections
    refine ⟨c, ?_⟩
    apply complexVariationPhysical_injective θ positiveθ
    rw [map_smul, complexConstantVariation_physical]
    apply ContinuousMap.ext
    intro a
    change complexVariationPhysical θ v a = c * 1
    simpa only [mul_one] using constant a

theorem complexUnitalVariation_fixed_kernel_line (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1)
    (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    ((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - 1).ker =
      Submodule.span ℂ {complexConstantVariation (R := R) θ positiveθ 1} := by
  apply le_antisymm
  · intro v member
    change complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v - v = 0 at member
    obtain ⟨c, identity⟩ := complexUnitalVariation_fixed_classification ψ θ positiveθ smallθ Cψ nonnegativeψ
      potential unital N connections nextConnections v (sub_eq_zero.mp member)
    rw [identity]
    exact Submodule.smul_mem _ c (Submodule.subset_span (mem_singleton _))
  · apply Submodule.span_le.mpr
    intro v member
    have identity : v = complexConstantVariation (R := R) θ positiveθ 1 := mem_singleton_iff.mp member
    subst v
    change complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
      (complexConstantVariation θ positiveθ 1) - complexConstantVariation θ positiveθ 1 = 0
    rw [complexUnitalVariation_constant_fixed, sub_self]

theorem complexUnitalVariation_generalized_fixed_rank (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1)
    (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) (n : ℕ) :
    Module.finrank ℂ ((((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - 1) ^ (n + 1)).ker) = 1 := by
  rw [PowerBoundedFixedSemisimple.ker_fixed_power
    (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)
    (4 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ)))
    (complexUnitalVariation_power_norm_bound ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) n]
  rw [complexUnitalVariation_fixed_kernel_line ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital N connections nextConnections]
  exact finrank_span_singleton (complexConstantVariation_one_ne_zero θ positiveθ)

end LeanShared.BilateralShadowingCoding
