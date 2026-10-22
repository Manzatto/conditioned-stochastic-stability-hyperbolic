module

public import LeanShared.Dynamics.ComplexOneSidedRieszRank
public import LeanShared.Analysis.RieszComplementSpectrum

/-! Removing the literal rank-one Riesz projector puts the entire
remaining spectrum of the actual normalized symbolic transfer in a
strict subunit disk, including continuous and residual spectrum.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Metric RieszContourIdempotent
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

local instance reducedRuelleGraphNorm (θ : ℝ) : NormedAddCommGroup (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedAddCommGroup
local instance reducedRuelleGraphSpace (θ : ℝ) : NormedSpace ℂ (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedSpace

theorem actualRuelle_reduced_spectrum (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    ∃ ρ r : ℝ, 0 < ρ ∧ 0 < r ∧ r < 1 ∧
      let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
      let P := projector T 1 ρ
      P.range = Submodule.span ℂ {complexConstantVariation (R := R) θ positiveθ 1} ∧
      Module.finrank ℂ P.range = 1 ∧ P * P = P ∧ T * P = P ∧ P * T = P ∧
        ∀ z ∈ spectrum ℂ (T - P), ‖z‖ ≤ r := by
  let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
  obtain ⟨radius, positiveRadius, contours⟩ := actualRuelle_rank_one_contours ψ θ positiveθ smallθ Cψ nonnegativeψ
    potential unital N connections nextConnections
  let ρ := radius / 2
  have positiveρ : 0 < ρ := by dsimp only [ρ]; positivity
  have smallρ : ρ < radius := by dsimp only [ρ]; linarith
  obtain ⟨resolventSphere, rangeLine, rankOne, idempotent, right, left⟩ := contours ρ positiveρ smallρ
  obtain ⟨r, positiveR, smallR, bound⟩ := actualRuelle_spectral_gap ψ θ positiveθ smallθ Cψ nonnegativeψ
    potential unital N connections nextConnections
  refine ⟨ρ, r, positiveρ, positiveR, smallR, rangeLine, rankOne, idempotent, right, left, ?_⟩
  intro z spectral
  have inclusion := RieszComplementSpectrum.inclusion T 1 1 ρ positiveρ.le resolventSphere
    (mem_ball_self positiveρ) idempotent (by simpa only [one_smul] using right)
    (by simpa only [one_smul] using left) z
      (by simpa only [one_smul] using spectral)
  rcases inclusion with zero | ⟨originalSpectral, outside⟩
  · simpa only [zero, norm_zero] using positiveR.le
  · apply bound z originalSpectral
    intro equal
    rw [equal, dist_self] at outside
    exact not_le_of_gt positiveρ outside

end LeanShared.BilateralShadowingCoding
