module

public import LeanShared.Dynamics.OneSidedNormalizedConeFamilies
public import LeanShared.Dynamics.OneSidedTransferLowerBound

/-! Literal positive finite Abel sums of the constructed transfer
iterates retain the invariant distortion cone.  Their normalized family
is relatively compact, uniformly in the nonnegative Abel parameter and
the truncation length.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
open scoped NNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

@[expose] def weightedAbelPartial (ψ : C(FuturePath R, ℝ)) (t : ℝ) (N : ℕ) : C(FuturePath R, ℝ) :=
  ∑ m ∈ Finset.range N, t ^ m • weightedIterateOne ψ m

omit [CompactSpace A] in
theorem weightedAbelPartial_succ (ψ : C(FuturePath R, ℝ)) (t : ℝ) (N : ℕ) :
    weightedAbelPartial ψ t (N + 1) = weightedAbelPartial ψ t N + t ^ N • weightedIterateOne ψ N :=
  Finset.sum_range_succ _ _

theorem weightedTransferOperator_iterateOne (ψ : C(FuturePath R, ℝ)) (m : ℕ) :
    weightedTransferOperator ψ (weightedIterateOne ψ m) = weightedIterateOne ψ (m + 1) := by
  apply ContinuousMap.ext
  intro a
  change weightedTransfer ψ ((weightedTransfer ψ)^[m] (fun _ => 1)) a =
    ((weightedTransfer ψ)^[m + 1] (fun _ => 1)) a
  rw [iterate_succ_apply']

theorem weightedAbelPartial_resolvent_identity (ψ : C(FuturePath R, ℝ)) (t : ℝ) (N : ℕ) :
    weightedAbelPartial ψ t N - t • weightedTransferOperator ψ (weightedAbelPartial ψ t N) =
      1 - t ^ N • weightedIterateOne ψ N := by
  induction N with
  | zero =>
    apply ContinuousMap.ext
    intro a
    simp only [weightedAbelPartial, Finset.range_zero, Finset.sum_empty, map_zero, smul_zero,
      pow_zero, one_smul, ContinuousMap.one_apply, ContinuousMap.sub_apply,
      weightedIterateOne, iterate_zero_apply, sub_self, ContinuousMap.zero_apply]
    change (0 : ℝ) = 1 - 1
    ring
  | succ N induction =>
    rw [weightedAbelPartial_succ, map_add, map_smul, smul_add, smul_smul,
      weightedTransferOperator_iterateOne, ← pow_succ']
    calc
      _ = (weightedAbelPartial ψ t N - t • weightedTransferOperator ψ (weightedAbelPartial ψ t N)) +
          t ^ N • weightedIterateOne ψ N - t ^ (N + 1) • weightedIterateOne ψ (N + 1) := by abel
      _ = _ := by rw [induction]; abel

omit [CompactSpace A] in
theorem weightedAbelPartial_nonnegative (ψ : C(FuturePath R, ℝ)) (t : ℝ) (nonnegative : 0 ≤ t)
    (N : ℕ) (a : FuturePath R) : 0 ≤ weightedAbelPartial ψ t N a := by
  simp only [weightedAbelPartial, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg (fun m _ => mul_nonneg (pow_nonneg nonnegative m)
    (weightedTransfer_iterate_one_nonnegative ψ m a))

omit [CompactSpace A] in
theorem weightedAbelPartial_ratio (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (t : ℝ) (nonnegative : 0 ≤ t) (N : ℕ) :
    PrefixRatioBound (weightedAbelPartial ψ t N) θ (Cψ * θ / (1 - θ)) := by
  intro n a b same
  simp only [weightedAbelPartial, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have estimate := weightedTransfer_iterate_one_ratio ψ θ Cψ positiveθ.le smallθ nonnegativeψ potential m n a b same
  have scaled := mul_le_mul_of_nonneg_left estimate (pow_nonneg nonnegative m)
  change t ^ m * weightedIterateOne ψ m b ≤
    t ^ m * (Real.exp (Cψ * θ / (1 - θ) * θ ^ n) * weightedIterateOne ψ m a) at scaled
  exact scaled.trans_eq (by ring)

theorem normalizedWeightedAbelPartials_relativelyCompact (ψ : C(FuturePath R, ℝ)) (θ Cψ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n) :
    IsCompact (closure (range (fun p : ℝ≥0 × ℕ =>
      ‖weightedAbelPartial ψ p.1 p.2‖⁻¹ • weightedAbelPartial ψ p.1 p.2))) := by
  exact normalizedConeFamily_relativelyCompact
    (fun p : ℝ≥0 × ℕ => weightedAbelPartial ψ p.1 p.2) θ (Cψ * θ / (1 - θ)) positiveθ smallθ
    (div_nonneg (mul_nonneg nonnegativeψ positiveθ.le) (sub_pos.mpr smallθ).le)
    (fun p => weightedAbelPartial_nonnegative ψ p.1 p.1.property p.2)
    (fun p => weightedAbelPartial_ratio ψ θ Cψ positiveθ smallθ nonnegativeψ potential p.1 p.1.property p.2)

end LeanShared.BilateralShadowingCoding
