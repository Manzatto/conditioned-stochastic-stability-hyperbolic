module

public import LeanShared.Dynamics.ComplexOneSidedRuelleResolvent
public import LeanShared.Dynamics.ComplexOneSidedLeadingRank
public import LeanShared.Analysis.PowerBoundedEigenvalueBound
public import LeanShared.Analysis.CompactTwoNormDiscreteSpectrum
public import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual normalized symbolic transfer has a genuine spectral gap:
every spectral value other than one lies in a strictly smaller disk.
The proof uses the actual Fredholm alternative, finite outer spectrum,
uniform powers, and the literal mixing-graph peripheral classification.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

local instance ruelleGapGraphNorm (θ : ℝ) : NormedAddCommGroup (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedAddCommGroup
local instance ruelleGapGraphSpace (θ : ℝ) : NormedSpace ℂ (complexVariationGraph R θ) :=
  (complexVariationGraph R θ).normedSpace
local instance ruelleGapContinuousNorm : NormedAddCommGroup C(FuturePath R, ℂ) :=
  ContinuousMap.instNormedAddCommGroup
local instance ruelleGapContinuousSpace : NormedSpace ℂ C(FuturePath R, ℂ) :=
  ContinuousMap.normedSpace

theorem actualRuelle_outer_spectral_eigenvector (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (z : ℂ)
    (spectral : z ∈ spectrum ℂ (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital))
    (outside : θ < ‖z‖) :
    ∃ v : complexVariationGraph R θ, v ≠ 0 ∧
      complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v = z • v := by
  let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
  by_contra! noVector
  have injective : Injective (T - z • 1 : complexVariationGraph R θ →L[ℂ] complexVariationGraph R θ) := by
    intro v w equal
    by_contra different
    have nonzero : v - w ≠ 0 := sub_ne_zero.mpr different
    have zero : (T - z • 1) (v - w) = 0 := by rw [map_sub, equal, sub_self]
    have eigen : T (v - w) = z • (v - w) := by
      change T (v - w) - z • (v - w) = 0 at zero
      exact sub_eq_zero.mp zero
    exact noVector (v - w) nonzero eigen
  have surjective : Surjective (T - z • 1 : complexVariationGraph R θ →L[ℂ] complexVariationGraph R θ) := by
    apply CompactTwoNormFredholm.surjective_of_twoNorm T (complexVariationPhysical θ)
      (complexVariationPhysical_compact θ positiveθ smallθ) θ 1 2
      (2 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ))) positiveθ.le zero_le_one
      (by norm_num) (by positivity) _ z outside injective
    intro n v
    simpa only [one_pow, mul_one] using
      complexUnitalVariation_lasota ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital n v
  have unit : IsUnit (T - z • 1) := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨injective, surjective⟩
  apply spectral
  change IsUnit (z • (1 : complexVariationGraph R θ →L[ℂ] complexVariationGraph R θ) - T)
  simpa only [neg_sub] using unit.neg

theorem actualRuelle_spectral_norm_le_one (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (z : ℂ)
    (spectral : z ∈ spectrum ℂ (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)) :
    ‖z‖ ≤ 1 := by
  by_cases inside : ‖z‖ ≤ θ
  · exact inside.trans smallθ.le
  · obtain ⟨v, nonzero, eigen⟩ := actualRuelle_outer_spectral_eigenvector ψ θ positiveθ smallθ Cψ nonnegativeψ
      potential unital z spectral (lt_of_not_ge inside)
    exact PowerBoundedEigenvalueBound.eigenvalue_norm_le_one
      (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)
      (4 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ)))
      (complexUnitalVariation_power_norm_bound ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) v nonzero z eigen

theorem actualRuelle_finite_outer_spectrum (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (q : ℝ) (outside : θ < q) :
    {z ∈ spectrum ℂ (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital) |
      q ≤ ‖z‖}.Finite := by
  apply CompactTwoNormDiscreteSpectrum.finite_outer_spectrum
    (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital)
    (complexVariationPhysical θ) (complexVariationPhysical_compact θ positiveθ smallθ)
    θ 1 2 (2 + 2 * (θ * (Real.exp Cψ * Cψ) / (1 - θ))) positiveθ.le zero_le_one
      (by norm_num) (by positivity) _ q outside
  intro n v
  simpa only [one_pow, mul_one] using
    complexUnitalVariation_lasota ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital n v

theorem actualRuelle_spectral_gap (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1) (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ z ∈ spectrum ℂ (complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital),
        z ≠ 1 → ‖z‖ ≤ r := by
  let T := complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital
  have strict (z : ℂ) (spectral : z ∈ spectrum ℂ T) (different : z ≠ 1) : ‖z‖ < 1 := by
    have bound := actualRuelle_spectral_norm_le_one ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital z spectral
    apply lt_of_le_of_ne bound
    intro equal
    obtain ⟨v, nonzero, eigen⟩ := actualRuelle_outer_spectral_eigenvector ψ θ positiveθ smallθ Cψ nonnegativeψ
      potential unital z spectral (by rw [equal]; exact smallθ)
    have identity := (complexUnitalVariation_peripheral_simple ψ θ positiveθ smallθ Cψ nonnegativeψ
      potential unital v nonzero z equal eigen N connections nextConnections).1
    exact different identity
  let q := (1 + θ) / 2
  have positiveQ : 0 < q := by dsimp only [q]; linarith
  have smallQ : q < 1 := by dsimp only [q]; linarith
  have outsideQ : θ < q := by dsimp only [q]; linarith
  let K := {z ∈ spectrum ℂ T | q ≤ ‖z‖} \ {1}
  have finiteK : K.Finite := (actualRuelle_finite_outer_spectrum ψ θ positiveθ smallθ Cψ nonnegativeψ
    potential unital q outsideQ).sdiff
  let B : Set ℝ := {q} ∪ (norm '' K)
  have finiteB : B.Finite := (finite_singleton q).union (finiteK.image norm)
  have nonemptyB : B.Nonempty := ⟨q, Or.inl (mem_singleton q)⟩
  have smallB : ∀ x ∈ B, x < 1 := by
    intro x member
    rcases member with member | ⟨z, member, rfl⟩
    · simpa only [mem_singleton_iff.mp member] using smallQ
    · exact strict z member.1.1 (by simpa only [mem_singleton_iff] using member.2)
  obtain ⟨r, memberR, maximal⟩ := finiteB.isCompact.exists_isMaxOn nonemptyB continuous_id.continuousOn
  have qBound : q ≤ r := maximal (Or.inl (mem_singleton q))
  refine ⟨r, positiveQ.trans_le qBound, smallB r memberR, ?_⟩
  intro z spectral different
  by_cases aboveQ : q ≤ ‖z‖
  · exact maximal (Or.inr ⟨z, ⟨⟨spectral, aboveQ⟩, by simpa only [mem_singleton_iff] using different⟩, rfl⟩)
  · exact (le_of_not_ge aboveQ).trans qBound

end LeanShared.BilateralShadowingCoding
