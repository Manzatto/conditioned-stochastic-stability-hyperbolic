module

public import LeanShared.Dynamics.OneSidedPeriodicExponentialAsymptotic
public import LeanShared.Dynamics.ActualSymbolicRuelleNormalization

/-! The positive eigenvalue and eigenfunction are produced from the
literal potential.  Its actual periodic weights have the resulting
eigenvalue to the n as leading term, with an exponentially small relative
remainder. -/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

omit [DiscreteTopology A] [CompactSpace A] [Nonempty (FuturePath R)] in
theorem normalizedPotential_periodic_sum (ψ h : C(FuturePath R, ℝ)) (ρ : ℝ)
    (positiveρ : 0 < ρ) (positiveH : ∀ a, 0 < h a) (n : ℕ) [NeZero n] :
    futurePeriodicWeightSum (normalizedPotential ψ h ρ positiveH) n =
      (ρ ^ n)⁻¹ * futurePeriodicWeightSum ψ n := by
  change (∑ p : PeriodicFuture (R := R) n, _) = (ρ ^ n)⁻¹ * (∑ p : PeriodicFuture (R := R) n, _)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => normalizedPotential_periodic_weight ψ h ρ positiveρ positiveH n p.val p.property)

theorem actual_periodic_relative_asymptotic (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    0 < (abelRadiusReal ψ)⁻¹ ∧ ∃ κ D : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < D ∧ ∀ n : ℕ,
      |(((abelRadiusReal ψ)⁻¹) ^ (n + 1))⁻¹ * futurePeriodicWeightSum ψ (n + 1) - 1| ≤
        D * κ ^ (n + 1) := by
  obtain ⟨positiveρ, h, _, positiveH, _, Cχ, nonnegativeχ, variationχ, unitalχ⟩ :=
    exists_actual_normalized_ruelle_potential ψ θ Cψ positiveθ smallθ nonnegativeψ potential N connections
  obtain ⟨κ, D, positiveκ, smallκ, positiveD, bound⟩ :=
    actualRuelle_periodic_exponential_asymptotic (normalizedPotential ψ h (abelRadiusReal ψ)⁻¹ positiveH)
      θ positiveθ smallθ Cχ nonnegativeχ variationχ unitalχ N connections nextConnections
  refine ⟨positiveρ, κ, D, positiveκ, smallκ, positiveD, ?_⟩
  intro n
  have result := bound n
  rw [normalizedPotential_periodic_sum ψ h (abelRadiusReal ψ)⁻¹ positiveρ positiveH] at result
  exact result

end LeanShared.BilateralShadowingCoding
