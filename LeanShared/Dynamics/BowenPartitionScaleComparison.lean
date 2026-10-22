module

public import LeanShared.Dynamics.ExpansiveBowenScaleComparison

/-! Uniform weighted scale comparison for the literal separated partition
suprema. The comparison includes all finite separated sets, not a supplied
maximizing or spanning sequence. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 1600000 in
theorem partition_scale_comparison (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ρ D : ℝ) (positiveρ : 0 < ρ) (coarse : 2 * ρ ≤ c)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ρ) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ,
      separatedPartitionSum T φ univ n ε ≤
        ENNReal.ofReal C * separatedPartitionSum T φ univ n ρ := by
  classical
  obtain ⟨C, positive, comparison⟩ := separated_scale_comparison
    T c positiveC expansive φ ρ D positiveρ coarse bowen ε positiveε
  refine ⟨C, positive, fun n => ?_⟩
  obtain ⟨t, separated, dominates⟩ := comparison n
  have lower : (∑ y ∈ t, ENNReal.ofReal (Real.exp (orbitSum T φ n y))) ≤
      separatedPartitionSum T φ univ n ρ := by
    unfold separatedPartitionSum
    exact le_iSup_of_le t (le_iSup_of_le separated le_rfl)
  unfold separatedPartitionSum
  refine iSup_le fun s => iSup_le fun hs => ?_
  have compare := ENNReal.ofReal_le_ofReal (dominates s hs)
  rw [ENNReal.ofReal_mul positive.le,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)] at compare
  exact compare.trans (mul_le_mul' le_rfl lower)

end LeanShared.ThermodynamicDefinitions
