module

public import LeanShared.Dynamics.ComplexOneSidedReducedSpectrum
public import LeanShared.Analysis.SpectralRadiusPowerBound
public import LeanShared.Analysis.FixedProjectionPowers

/-! Actual exponential norm convergence of normalized symbolic Ruelle
powers to their literal rank-one Riesz contour projector.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function RieszContourIdempotent
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

local instance convergentRuelleGraphNorm (θ : ℝ) : NormedAddCommGroup (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedAddCommGroup
local instance convergentRuelleGraphSpace (θ : ℝ) : NormedSpace ℂ (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedSpace

theorem actualRuelle_exponential_convergence (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    ∃ ρ τ C : ℝ, 0 < ρ ∧ 0 < τ ∧ τ < 1 ∧ 0 < C ∧
      let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
      let P := projector T 1 ρ
      P.range = Submodule.span ℂ {complexConstantVariation (R := R) θ positiveθ 1} ∧
      Module.finrank ℂ P.range = 1 ∧ P * P = P ∧ T * P = P ∧ P * T = P ∧
        ∀ n : ℕ, ‖T ^ n - P‖ ≤ C * τ ^ n := by
  let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
  obtain ⟨ρ, q, positiveρ, positiveQ, smallQ, rangeLine, rankOne, idempotent, right, left, spectrumBound⟩ :=
    actualRuelle_reduced_spectrum ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital N connections nextConnections
  let P := projector T 1 ρ
  let τ := (1 + q) / 2
  have positiveτ : 0 < τ := by dsimp only [τ]; linarith
  have smallτ : τ < 1 := by dsimp only [τ]; linarith
  have gap : q < τ := by dsimp only [τ]; linarith
  obtain ⟨C, positiveC, bound⟩ := SpectralRadiusPowerBound.exists_geometric_bound_of_spectrum
    (T - P) q τ positiveτ gap spectrumBound
  let D := C + ‖(1 : complexVariationGraph R θ →L[ℂ] complexVariationGraph R θ) - P‖
  have positiveD : 0 < D := lt_of_lt_of_le positiveC (le_add_of_nonneg_right (norm_nonneg _))
  refine ⟨ρ, τ, D, positiveρ, positiveτ, smallτ, positiveD, rangeLine, rankOne, idempotent, right, left, ?_⟩
  intro n
  cases n with
  | zero =>
    simp only [pow_zero, mul_one]
    change ‖1 - P‖ ≤ C + ‖1 - P‖
    exact le_add_of_nonneg_left positiveC.le
  | succ n =>
    rw [← FixedProjectionPowers.sub_projection_power T P idempotent right left n]
    exact (bound (n + 1)).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (norm_nonneg _)) (pow_nonneg positiveτ.le _))

end LeanShared.BilateralShadowingCoding
