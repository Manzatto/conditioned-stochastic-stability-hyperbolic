module

public import LeanShared.Dynamics.ComplexOneSidedUnitalLasota
public import LeanShared.Analysis.CompactTwoNormMeromorphicResolvent

/-! Meromorphy and finite spectral Fitting decompositions for the literal
normalized symbolic Ruelle operator, derived from its actual compact
inclusion and proved arbitrary-power Lasota estimate.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

local instance ruelleResolventGraphNorm (θ : ℝ) : NormedAddCommGroup (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedAddCommGroup
local instance ruelleResolventGraphSpace (θ : ℝ) : NormedSpace ℂ (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedSpace
local instance ruelleResolventContinuousNorm : NormedAddCommGroup C(FuturePath R, ℂ) :=
  ContinuousMap.instNormedAddCommGroup
local instance ruelleResolventContinuousSpace : NormedSpace ℂ C(FuturePath R, ℂ) :=
  ContinuousMap.normedSpace

theorem actualRuelle_resolvent_meromorphicOn (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) :
    MeromorphicOn (resolvent (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital))
      {z : ℂ | θ < ‖z‖} := by
  apply CompactTwoNormMeromorphicResolvent.meromorphicOn
    (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)
    (complexVariationPhysical θ) (complexVariationPhysical_compact θ positiveθ smallθ)
    θ 1 2 (2 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ))) positiveθ.le zero_le_one
      (by norm_num) (by positivity)
  intro n v
  simpa only [one_pow, mul_one] using
    complexUnitalVariation_lasota ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital n v

theorem actualRuelle_finite_spectral_decomposition (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (z : ℂ) (outside : θ < ‖z‖) :
    ∃ n : ℕ,
      FiniteDimensional ℂ (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - z • 1) ^ n).ker ∧
      Submodule.IsTopCompl
        (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - z • 1) ^ n).ker
        (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - z • 1) ^ n).range ∧
      (∀ m : ℕ, (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - z • 1) ^ (n + m)).ker =
        (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - z • 1) ^ n).ker) ∧
      (∀ m : ℕ, (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - z • 1) ^ (n + m)).range =
        (((complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) - z • 1) ^ n).range) := by
  apply CompactTwoNormDecomposition.exists_decomposition
    (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)
    (complexVariationPhysical θ) (complexVariationPhysical_compact θ positiveθ smallθ)
    θ 1 2 (2 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ))) positiveθ.le zero_le_one
      (by norm_num) (by positivity) _ z outside
  intro n v
  simpa only [one_pow, mul_one] using
    complexUnitalVariation_lasota ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital n v

end LeanShared.BilateralShadowingCoding
