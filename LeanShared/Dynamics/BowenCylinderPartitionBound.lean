module
public import LeanShared.Dynamics.SeparatedOrbitMiddleSplitting
public import LeanShared.Dynamics.BowenPartitionSubmultiplication

/-! A literal weighted Bowen-cylinder upper bound. The prefix and suffix
spanning sets are constructed from compact expansivity, and the middle
energy is that of the prescribed actual orbit. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 2000000 in
theorem cylinder_partition_bound (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ε D : ℝ) (positiveε : 0 < ε)
    (bowen : ∀ h x y, (∀ j < h, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ h x - orbitSum T φ h y| ≤ D)
    (n k m : ℕ) (z : X) (s : Finset X)
    (separated : Separated T univ (n + k + m) (3 * ε) s) :
    (∑ x ∈ s.filter (fun x => ∀ j < k, dist (T^[n + j] x) (T^[j] z) < ε),
      ENNReal.ofReal (Real.exp (orbitSum T φ (n + k + m) x))) ≤
      ENNReal.ofReal (Real.exp (3 * D + orbitSum T φ k z)) *
        separatedPartitionSum T φ univ n ε * separatedPartitionSum T φ univ m ε := by
  classical
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positiveC expansive
  obtain ⟨p, count⟩ := counts ε positiveε
  obtain ⟨t, _, separatedT, spansT⟩ :=
    exists_separated_spanning T n ε positiveε (a ^ (n + p)) (count n)
  obtain ⟨u, _, separatedU, spansU⟩ :=
    exists_separated_spanning T m ε positiveε (a ^ (m + p)) (count m)
  choose centerA memberA traceA using spansT
  choose centerB memberB traceB using spansU
  let v := s.filter (fun x => ∀ j < k, dist (T^[n + j] x) (T^[j] z) < ε)
  have separatedV : Separated T univ (n + k + m) (3 * ε) v :=
    ⟨fun _ _ => mem_univ _, fun x hx y hy =>
      separated.2 x (Finset.mem_of_mem_filter x hx) y (Finset.mem_of_mem_filter y hy)⟩
  have split := weighted_middle_splitting T φ ε D positiveε n k m v t u z separatedV
    centerA (fun x => centerB (T^[n + k] x))
    (fun x _ => memberA x) (fun x _ => memberB _)
    (fun x _ => traceA x) (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x _ j hj => by
      rw [Nat.add_comm (n + k) j, Function.iterate_add_apply]
      exact traceB (T^[n + k] x) j hj) bowen
  have upper := ENNReal.ofReal_le_ofReal split
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _),
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _)
      (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _))),
    ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _)] at upper
  have first : (∑ y ∈ t, ENNReal.ofReal (Real.exp (orbitSum T φ n y))) ≤
      separatedPartitionSum T φ univ n ε := by
    unfold separatedPartitionSum
    exact le_iSup_of_le t (le_iSup_of_le separatedT le_rfl)
  have last : (∑ y ∈ u, ENNReal.ofReal (Real.exp (orbitSum T φ m y))) ≤
      separatedPartitionSum T φ univ m ε := by
    unfold separatedPartitionSum
    exact le_iSup_of_le u (le_iSup_of_le separatedU le_rfl)
  exact upper.trans (mul_le_mul' (mul_le_mul' le_rfl first) last)

end LeanShared.ThermodynamicDefinitions
