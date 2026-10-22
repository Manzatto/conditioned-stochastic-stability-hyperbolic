module

public import LeanShared.Dynamics.OneSidedGraphSplicing
public import LeanShared.Dynamics.OneSidedTransferBranchLower

/-! Actual fixed-length graph connections upgrade the constructed
nonnegative eigenfunction to strict positivity.  Zeros propagate through
literal prehistories; the retained prefix cone transfers positivity
within an initial-symbol cylinder.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

theorem eigenfunction_positive_of_connections (ψ h : C(FuturePath R, ℝ)) (eigenvalue θ K : ℝ)
    (normOne : ‖h‖ = 1) (nonnegative : ∀ a, 0 ≤ h a)
    (ratio : PrefixRatioBound h θ K) (eigen : weightedTransferOperator ψ h = eigenvalue • h)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N : ℤ) = j) :
    ∀ b : FuturePath R, 0 < h b := by
  have nonzero : h ≠ 0 := by intro zero; rw [zero, norm_zero] at normOne; norm_num at normOne
  obtain ⟨a, positiveA⟩ : ∃ a : FuturePath R, h a ≠ 0 := by
    by_contra absent
    apply nonzero
    apply ContinuousMap.ext
    intro a
    exact not_ne_iff.mp (not_exists.mp absent a)
  have positive : 0 < h a := lt_of_le_of_ne (nonnegative a) positiveA.symm
  intro b
  by_contra notPositive
  have zero : h b = 0 := le_antisymm (not_lt.mp notPositive) (nonnegative b)
  obtain ⟨p, first, last⟩ := connections (a.val 0) (b.val 0)
  let c := futureSplice p N b last
  have shifted : (futureShift : FuturePath R → FuturePath R)^[N] c = b := futureShift_splice p N b last
  have zeroC : h c = 0 := eigenfunction_zero_prehistory ψ h eigenvalue nonnegative eigen N c (by rw [shifted]; exact zero)
  have same : PrefixAgreement c a 0 := by
    intro k bound
    have zeroK : k = 0 := by omega
    subst k
    exact (futureSplice_word p N b last 0 (Nat.zero_le N)).trans first
  have estimate := ratio 0 c a same
  rw [zeroC, mul_zero] at estimate
  exact (not_le_of_gt positive) estimate

variable [Nonempty (FuturePath R)]

theorem weightedTransfer_exists_positive_eigenfunction (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (N : ℕ) (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N : ℤ) = j) :
    ∃ h : C(FuturePath R, ℝ), ‖h‖ = 1 ∧ (∀ a, 0 < h a) ∧
      PrefixRatioBound h θ (Cψ * θ / (1 - θ)) ∧
        weightedTransferOperator ψ h = (abelRadiusReal ψ)⁻¹ • h := by
  obtain ⟨h, normOne, nonnegative, ratio, eigen⟩ :=
    weightedTransfer_exists_nonnegative_eigenfunction ψ θ Cψ positiveθ smallθ nonnegativeψ potential
  exact ⟨h, normOne, eigenfunction_positive_of_connections ψ h (abelRadiusReal ψ)⁻¹ θ _
    normOne nonnegative ratio eigen N connections, ratio, eigen⟩

end LeanShared.BilateralShadowingCoding
