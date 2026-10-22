module

public import LeanShared.Dynamics.ComplexOneSidedSpectralGap
public import LeanShared.Analysis.CompactTwoNormRieszRange
public import LeanShared.Analysis.RieszContourEigenvectors

/-! The literal Riesz contour of the actual normalized symbolic Ruelle
operator has precisely the constant line as its range.  Its rank,
idempotence and both invariant scalar projection laws are derived.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Metric RieszContourIdempotent
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

local instance ruelleRieszGraphNorm (θ : ℝ) : NormedAddCommGroup (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedAddCommGroup
local instance ruelleRieszGraphSpace (θ : ℝ) : NormedSpace ℂ (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedSpace
local instance ruelleRieszContinuousNorm : NormedAddCommGroup C(FuturePath R, ℂ) :=
  ContinuousMap.instNormedAddCommGroup
local instance ruelleRieszContinuousSpace : NormedSpace ℂ C(FuturePath R, ℂ) :=
  ContinuousMap.normedSpace

theorem actualRuelle_rank_one_contours (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r →
      let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
      let P := projector T 1 ρ
      sphere (1 : ℂ) ρ ⊆ resolventSet ℂ T ∧
      P.range = Submodule.span ℂ {complexConstantVariation (R := R) θ positiveθ 1} ∧
      Module.finrank ℂ P.range = 1 ∧ P * P = P ∧ T * P = P ∧ P * T = P := by
  let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
  obtain ⟨n, r, positiveR, _, kernels, contours⟩ :=
    CompactTwoNormRieszRange.exists_contours T (complexVariationPhysical θ)
      (complexVariationPhysical_compact θ positiveθ smallθ) θ 1 2
      (2 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ))) positiveθ.le zero_le_one
      (by norm_num) (by positivity)
      (fun m v => by simpa only [one_pow, mul_one] using
        complexUnitalVariation_lasota ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital m v)
      1 (by simpa only [norm_one] using smallθ)
  simp only [one_smul] at kernels contours
  have stableKernel : ((T - 1) ^ n).ker = (T - 1).ker := by
    have positiveKernel := PowerBoundedFixedSemisimple.ker_fixed_power T
      (4 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ)))
      (complexUnitalVariation_power_norm_bound ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) n
    have stable := kernels 1
    exact stable.symm.trans positiveKernel
  have line := complexUnitalVariation_fixed_kernel_line ψ θ positiveθ smallθ Cψ nonnegativeψ
    potential unital N connections nextConnections
  refine ⟨r, positiveR, ?_⟩
  intro ρ positiveρ smallρ
  let P := projector T 1 ρ
  obtain ⟨resolventSphere, rangeIdentity⟩ := contours ρ positiveρ smallρ
  have rangeLine : P.range = Submodule.span ℂ {complexConstantVariation (R := R) θ positiveθ 1} := by
    change (projector T 1 ρ).range = _
    rw [rangeIdentity]
    simpa only [one_smul] using stableKernel.trans line
  have fixedRange (v : complexVariationGraph R θ) : T (P v) = P v := by
    have member : P v ∈ P.range := ⟨v, rfl⟩
    rw [rangeIdentity] at member
    have fixedMember : P v ∈ (T - 1).ker := by
      simpa only [one_smul] using (stableKernel ▸ member)
    change T (P v) - P v = 0 at fixedMember
    exact sub_eq_zero.mp fixedMember
  have right : T * P = P := by
    apply ContinuousLinearMap.ext
    exact fixedRange
  have left : P * T = P :=
    (projector_commutes T 1 ρ positiveρ.le resolventSphere).symm.trans right
  have idempotent : P * P = P := by
    apply ContinuousLinearMap.ext
    intro v
    exact projector_eigenvector T 1 1 ρ positiveρ resolventSphere
      (mem_ball_self positiveρ) (P v) (by simpa only [one_smul] using fixedRange v)
  refine ⟨resolventSphere, rangeLine, ?_, idempotent, right, left⟩
  rw [rangeLine]
  exact finrank_span_singleton (complexConstantVariation_one_ne_zero θ positiveθ)

end LeanShared.BilateralShadowingCoding
