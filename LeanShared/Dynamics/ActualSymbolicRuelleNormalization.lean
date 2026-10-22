module

public import LeanShared.Dynamics.NormalizedRuellePeriodicWeights
public import LeanShared.Dynamics.ComplexOneSidedSpectralGap

/-! An arbitrary actual exponentially varying one-sided potential on
the connected main graph produces the normalized weighted potential.
Neither a positive eigenfunction nor a unital transfer is an input.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

theorem exists_actual_normalized_ruelle_potential (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j) :
    0 < (abelRadiusReal ψ)⁻¹ ∧
      ∃ h : C(FuturePath R, ℝ), ‖h‖ = 1 ∧
        ∃ positiveH : (∀ a, 0 < h a),
          weightedTransferOperator ψ h = (abelRadiusReal ψ)⁻¹ • h ∧
          ∃ Cχ : ℝ, 0 ≤ Cχ ∧
            (∀ n a b, PrefixAgreement a b n →
              |normalizedPotential ψ h (abelRadiusReal ψ)⁻¹ positiveH b -
                normalizedPotential ψ h (abelRadiusReal ψ)⁻¹ positiveH a| ≤ Cχ * θ ^ n) ∧
            weightedTransferOperator (normalizedPotential ψ h (abelRadiusReal ψ)⁻¹ positiveH) 1 = 1 := by
  have positiveEigenvalue : 0 < (abelRadiusReal ψ)⁻¹ := inv_pos.mpr (abelRadiusReal_positive ψ)
  obtain ⟨h, normOne, positiveH, ratio, eigen⟩ := weightedTransfer_exists_positive_eigenfunction
    ψ θ Cψ positiveθ smallθ nonnegativeψ potential N connections
  let K := Cψ * θ / (1 - θ)
  have nonnegativeK : 0 ≤ K := div_nonneg (mul_nonneg nonnegativeψ positiveθ.le) (sub_pos.mpr smallθ).le
  let Cχ := Cψ + K + (2 * ‖eigenfunctionLog h positiveH‖ + K / θ)
  refine ⟨positiveEigenvalue, h, normOne, positiveH, eigen, Cχ, ?_, ?_, ?_⟩
  · dsimp only [Cχ]
    positivity
  · exact normalizedPotential_variation ψ h (abelRadiusReal ψ)⁻¹ θ Cψ K positiveH positiveθ
      nonnegativeK potential ratio
  · exact normalizedPotential_unital ψ h (abelRadiusReal ψ)⁻¹ positiveEigenvalue positiveH eigen

end LeanShared.BilateralShadowingCoding
