module

public import LeanShared.Dynamics.ProvedPressurePartitionEnvelope
public import LeanShared.Dynamics.SeparatedPartitionMultiplication
public import LeanShared.Dynamics.SpecificationPartitionNormalization
public import LeanShared.Dynamics.BowenPartitionScaleComparison

/-! Weighted specification yields a uniform exponential upper bound for
the literal separated partition sums at the ACTUAL pressure. Compact
expansivity, variational comparison and finite-supremum approximation are
proved internally; no pressure scalar or normalization source is assumed. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 2400000 in
theorem partition_upper_of_weighted_specification
    (T : X ≃ₜ X) (c₀ : ℝ) (positive₀ : 0 < c₀)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c₀ ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c₀) → x = y)
    (φ : X →ᵇ ℝ) (ρ D : ℝ) (positiveρ : 0 < ρ) (coarse : 2 * ρ ≤ c₀)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ρ) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (ε c : ℝ) (positiveε : 0 < ε) (positiveC : 0 < c) (gap : ℕ)
    (gluing : ∀ n, 0 < n → ∀ m, 0 < m → ∀ s t : Finset X,
      Separated T univ n ρ s → Separated T univ m ρ t →
      ∃ q : Finset X, Separated T univ (n + m + gap) ε q ∧
        c * (∑ x ∈ s, Real.exp (orbitSum T φ n x)) *
          (∑ y ∈ t, Real.exp (orbitSum T φ m y)) ≤
            ∑ z ∈ q, Real.exp (orbitSum T φ (n + m + gap) z)) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ B > 0,
      ∀ n : ℕ, 0 < n → (separatedPartitionSum T φ univ n ρ).toReal ≤
        B * Real.exp ((n : ℝ) * P) := by
  obtain ⟨C, positiveScale, comparison⟩ := partition_scale_comparison
    T c₀ positive₀ expansive φ ρ D positiveρ coarse bowen ε positiveε
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c₀ positive₀ expansive
  obtain ⟨p, count⟩ := counts ρ positiveρ
  have finite (n : ℕ) := partitionSum_positive_finite_of_count T φ n p a ρ (count n)
  let coefficient := c / (4 * C)
  have positiveCoefficient : 0 < coefficient := div_pos positiveC (mul_pos (by norm_num) positiveScale)
  have product := partition_multiplication_of_gluing T φ univ ρ ε c C positiveScale positiveC.le
    gap (fun n => (finite n).1) (fun n => (finite n).2) comparison gluing
  obtain ⟨P, pressureP, envelope⟩ := actual_pressure_log_envelope T c₀ positive₀ expansive φ
  have normalization := SpecificationPartitionNormalization.upper_bound
    (fun n => (separatedPartitionSum T φ univ n ρ).toReal)
    (fun n => ENNReal.toReal_pos (finite n).1 (finite n).2)
    coefficient positiveCoefficient gap P product (envelope ρ positiveρ)
  refine ⟨P, pressureP, Real.exp ((gap : ℝ) * P) / coefficient,
    div_pos (Real.exp_pos _) positiveCoefficient, ?_⟩
  intro n hn
  have bound := normalization n hn
  rw [Nat.cast_add, add_mul, Real.exp_add] at bound
  exact bound.trans_eq (by ring)

end LeanShared.ThermodynamicDefinitions
