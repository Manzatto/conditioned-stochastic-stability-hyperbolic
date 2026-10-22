module
public import LeanShared.Dynamics.PointSpecificationPartitionUpper
public import LeanShared.Dynamics.ProvedBowenPartitionLower

/-! Compact expansivity, point specification and Bowen distortion give
both partition normalization bounds at ONE actual pressure and ONE scale. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem partition_bounds_of_point_specification
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
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ A > 0, ∃ B > 0,
      ∀ n : ℕ, 0 < n →
        A * Real.exp ((n : ℝ) * P) ≤ (separatedPartitionSum T φ univ n (3 * ε)).toReal ∧
        (separatedPartitionSum T φ univ n (3 * ε)).toReal ≤ B * Real.exp ((n : ℝ) * P) := by
  obtain ⟨P, pressureP, B, positiveB, upper⟩ := partition_upper_of_point_specification
    T c₀ positive₀ expansive φ ε D positiveε coarse bowen specification
  obtain ⟨Q, pressureQ, A, positiveA, lower⟩ := partition_lower_at_pressure
    T c₀ positive₀ expansive φ ε D positiveε coarse bowen
  have same : Q = P := EReal.coe_injective (pressureQ.symm.trans pressureP)
  subst Q
  exact ⟨P, pressureP, A, positiveA, B, positiveB, fun n hn => ⟨lower n hn, upper n hn⟩⟩

end LeanShared.ThermodynamicDefinitions
