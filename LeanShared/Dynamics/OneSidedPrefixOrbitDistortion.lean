module

public import LeanShared.Dynamics.OneSidedIteratedPrehistoryFormula
public import LeanShared.Dynamics.OneSidedUnitalTransferVariation

/-! Agreement through n+m gives exponentially small orbit-energy
distortion over n iterates, uniformly in n.  The full geometric sum is
retained, rather than introducing an artificial factor n.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

theorem futureShift_iterate_prefix (a b : FuturePath R) (radius k : ℕ) (bound : k ≤ radius)
    (same : PrefixAgreement a b radius) :
    PrefixAgreement ((futureShift : FuturePath R → FuturePath R)^[k] a)
      ((futureShift : FuturePath R → FuturePath R)^[k] b) (radius - k) := by
  intro j within
  rw [futureShift_iterate_val, futureShift_iterate_val]
  exact same (j + k) (by omega)

omit [TopologicalSpace A] in
theorem reverse_geometric_window_sum (θ : ℝ) (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (n m : ℕ) :
    (∑ k ∈ Finset.range n, θ ^ (n + m - k)) ≤ θ ^ (m + 1) / (1 - θ) := by
  have reflected : (∑ k ∈ Finset.range n, θ ^ (n + m - k)) =
      ∑ k ∈ Finset.range n, θ ^ ((m + 1) + k) := by
    calc
      _ = ∑ k ∈ Finset.range n, θ ^ ((m + 1) + (n - 1 - k)) := by
        apply Finset.sum_congr rfl
        intro k member
        have before := Finset.mem_range.mp member
        congr 1
        omega
      _ = _ := Finset.sum_range_reflect (fun k => θ ^ ((m + 1) + k)) n
  rw [reflected]
  simp_rw [pow_add]
  rw [← Finset.mul_sum]
  have geometric := (summable_geometric_of_lt_one nonnegativeθ smallθ).sum_le_tsum
    (Finset.range n) (fun k _ => pow_nonneg nonnegativeθ k)
  rw [(hasSum_geometric_of_lt_one nonnegativeθ smallθ).tsum_eq] at geometric
  simpa only [div_eq_mul_inv, pow_add] using mul_le_mul_of_nonneg_left geometric (pow_nonneg nonnegativeθ (m + 1))

theorem prefix_orbit_energy_distortion (ψ : FuturePath R → ℝ) (θ Cψ : ℝ)
    (nonnegativeθ : 0 ≤ θ) (smallθ : θ < 1) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ k a b, PrefixAgreement a b k → |ψ b - ψ a| ≤ Cψ * θ ^ k)
    (n m : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b (n + m)) :
    |orbitSum futureShift ψ n b - orbitSum futureShift ψ n a| ≤
      (Cψ * θ / (1 - θ)) * θ ^ m := by
  rw [orbitSum, orbitSum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range n, Cψ * θ ^ (n + m - k) := by
      apply Finset.sum_le_sum
      intro k member
      exact potential (n + m - k) _ _ (futureShift_iterate_prefix a b (n + m) k
        (by have before := Finset.mem_range.mp member; omega) same)
    _ = Cψ * (∑ k ∈ Finset.range n, θ ^ (n + m - k)) := (Finset.mul_sum _ _ _).symm
    _ ≤ Cψ * (θ ^ (m + 1) / (1 - θ)) := mul_le_mul_of_nonneg_left
      (reverse_geometric_window_sum θ nonnegativeθ smallθ n m) nonnegativeψ
    _ = _ := by rw [pow_succ]; ring

end LeanShared.BilateralShadowingCoding
