module

public import LeanShared.Dynamics.ActualBilateralWeightedZeta

/-! Actual bilateral periodic weights have the constructed Abel
eigenvalue as leading exponential, with a geometric relative error.
The original two-sided potential and its literal periodic points remain.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

theorem actual_bilateral_periodic_relative_asymptotic (φ : C(Path R, ℝ))
    (variation : HasExponentialVariations φ)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    0 < (abelRadiusReal (bilateralRuelleFuturePotential φ variation))⁻¹ ∧
      ∃ κ D : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < D ∧ ∀ n : ℕ,
        |(((abelRadiusReal (bilateralRuelleFuturePotential φ variation))⁻¹) ^ (n + 1))⁻¹ *
          bilateralPeriodicWeightSum φ (n + 1) - 1| ≤ D * κ ^ (n + 1) := by
  obtain ⟨θ, positiveθ, smallθ, Cψ, nonnegativeψ, potential⟩ :=
    oneSidedPotential_exponential φ φ.continuous variation
  obtain ⟨positiveρ, κ, D, positiveκ, smallκ, positiveD, bound⟩ :=
    actual_periodic_relative_asymptotic (bilateralRuelleFuturePotential φ variation) θ Cψ
      positiveθ smallθ nonnegativeψ potential N connections nextConnections
  refine ⟨positiveρ, κ, D, positiveκ, smallκ, positiveD, ?_⟩
  intro n
  have result := bound n
  change |(((abelRadiusReal (bilateralRuelleFuturePotential φ variation))⁻¹) ^ (n + 1))⁻¹ *
    futurePeriodicWeightSum (oneSidedPotential φ) (n + 1) - 1| ≤ D * κ ^ (n + 1) at result
  rw [← bilateralPeriodicWeightSum_eq_future φ variation] at result
  exact result

end LeanShared.BilateralShadowingCoding
