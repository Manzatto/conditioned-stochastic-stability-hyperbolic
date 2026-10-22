module

public import LeanShared.Dynamics.ProvedSpecificationPartitionUpper
public import LeanShared.Dynamics.SpecificationWeightedPartition

/-! Ordinary point specification, compact expansivity and Bowen distortion
force uniform partition normalization at the actual pressure. All weighted
finite-set gluing, scale comparisons and variational bounds are derived. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 2000000 in
theorem partition_upper_of_point_specification
    (T : X ≃ₜ X) (c₀ : ℝ) (positive₀ : 0 < c₀)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c₀ ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c₀) → x = y)
    (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε) (coarse : 6 * ε ≤ c₀)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 3 * ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ B > 0,
      ∀ n : ℕ, 0 < n → (separatedPartitionSum T φ univ n (3 * ε)).toReal ≤
        B * Real.exp ((n : ℝ) * P) := by
  obtain ⟨gap, positiveGap, tracing⟩ := specification ε positiveε
  let c := Real.exp (-(2 * D + (gap - 1 : ℕ) * ‖φ‖))
  have positiveC : 0 < c := Real.exp_pos _
  have gluing := pair_tracing_weighted_gluing T φ ε D positiveε gap positiveGap tracing
    (fun n x y close => bowen (n + 1) x y (fun j hj =>
      (close j (by omega)).trans_le (by linarith)))
  apply partition_upper_of_weighted_specification T c₀ positive₀ expansive φ (3 * ε) D
    (by positivity) (by linarith) bowen ε c positiveε positiveC (gap - 1)
  intro n positiveN m positiveM s t first second
  have firstIndex : n - 1 + 1 = n := by omega
  have secondIndex : m - 1 + 1 = m := by omega
  have totalIndex : n - 1 + gap + (m - 1) + 1 = n + m + (gap - 1) := by omega
  have result := gluing (n - 1) (m - 1) s t
    (by simpa only [firstIndex] using first) (by simpa only [secondIndex] using second)
  simpa only [firstIndex, secondIndex, totalIndex] using result

end LeanShared.ThermodynamicDefinitions
