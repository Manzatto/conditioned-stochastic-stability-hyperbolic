module

public import LeanShared.Dynamics.SeparatedOrbitSplitting
public import LeanShared.Dynamics.BowenPartitionScaleComparison

/-! Actual separated spanning sets and Bowen energy estimates prove
submultiplicativity of the literal partition suprema. Compact expansivity
also removes the apparent scale mismatch with a uniform constant. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 2000000 in
theorem partition_split_scales (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ε D : ℝ) (positiveε : 0 < ε)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D) :
    ∀ n m : ℕ, separatedPartitionSum T φ univ (n + m) (3 * ε) ≤
      ENNReal.ofReal (Real.exp (2 * D)) * separatedPartitionSum T φ univ n ε *
        separatedPartitionSum T φ univ m ε := by
  classical
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positiveC expansive
  obtain ⟨p, count⟩ := counts ε positiveε
  intro n m
  obtain ⟨t, _, tSeparated, tSpans⟩ := exists_separated_spanning T n ε positiveε (a ^ (n + p)) (count n)
  obtain ⟨u, _, uSeparated, uSpans⟩ := exists_separated_spanning T m ε positiveε (a ^ (m + p)) (count m)
  choose centerA memberA traceA using tSpans
  choose centerB memberB traceB using uSpans
  have tUpper : (∑ y ∈ t, ENNReal.ofReal (Real.exp (orbitSum T φ n y))) ≤
      separatedPartitionSum T φ univ n ε := by
    unfold separatedPartitionSum
    exact le_iSup_of_le t (le_iSup_of_le tSeparated le_rfl)
  have uUpper : (∑ y ∈ u, ENNReal.ofReal (Real.exp (orbitSum T φ m y))) ≤
      separatedPartitionSum T φ univ m ε := by
    unfold separatedPartitionSum
    exact le_iSup_of_le u (le_iSup_of_le uSeparated le_rfl)
  unfold separatedPartitionSum
  refine iSup_le fun s => iSup_le fun hs => ?_
  have splitting := weighted_orbit_splitting T φ ε D positiveε n m s t u hs
    centerA (fun x => centerB (T^[n] x)) (fun x _ => memberA x)
    (fun x _ => memberB _) (fun x _ => traceA x) (fun x _ j hj => by
      rw [Nat.add_comm n j, Function.iterate_add_apply]
      exact traceB (T^[n] x) j hj) bowen
  have comparison := ENNReal.ofReal_le_ofReal splitting
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _),
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _))),
    ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _)] at comparison
  exact comparison.trans (mul_le_mul' (mul_le_mul' le_rfl tUpper) uUpper)

set_option maxHeartbeats 1600000 in
theorem partition_submultiplication (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ε D : ℝ) (positiveε : 0 < ε) (coarse : 6 * ε ≤ c)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 3 * ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D) :
    ∃ C > 0, ∀ n m : ℕ, separatedPartitionSum T φ univ (n + m) (3 * ε) ≤
      ENNReal.ofReal C * separatedPartitionSum T φ univ n (3 * ε) *
        separatedPartitionSum T φ univ m (3 * ε) := by
  obtain ⟨C, positive, comparison⟩ := partition_scale_comparison
    T c positiveC expansive φ (3 * ε) D (by positivity) (by linarith) bowen ε positiveε
  refine ⟨Real.exp (2 * D) * C ^ 2, mul_pos (Real.exp_pos _) (sq_pos_of_pos positive), ?_⟩
  intro n m
  have split := partition_split_scales T c positiveC expansive φ ε D positiveε
    (fun k x y near => bowen k x y (fun j hj => (near j hj).trans_le (by linarith))) n m
  calc
    _ ≤ ENNReal.ofReal (Real.exp (2 * D)) * separatedPartitionSum T φ univ n ε *
        separatedPartitionSum T φ univ m ε := split
    _ ≤ ENNReal.ofReal (Real.exp (2 * D)) *
        (ENNReal.ofReal C * separatedPartitionSum T φ univ n (3 * ε)) *
        (ENNReal.ofReal C * separatedPartitionSum T φ univ m (3 * ε)) :=
      mul_le_mul' (mul_le_mul' le_rfl (comparison n)) (comparison m)
    _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_pow positive.le]; ring

end LeanShared.ThermodynamicDefinitions
