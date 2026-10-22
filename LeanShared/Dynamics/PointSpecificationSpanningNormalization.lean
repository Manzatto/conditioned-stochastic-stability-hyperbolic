module
public import LeanShared.Dynamics.PointSpecificationPartitionBounds
public import LeanShared.Dynamics.WeightedSeparatedSpanning

/-! Actual maximal-cardinality separated spanning families have two-sided
uniform exponential weight at the actual pressure. Both pressure scales and
all finite spanning sets are constructed from the ordinary dynamical data. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 2400000 in
theorem normalized_spanning_families_of_point_specification
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
      ∀ N : ℕ, 0 < N → ∃ s : Finset X, s.Nonempty ∧ Separated T univ N ε s ∧
        (∀ x : X, ∃ y ∈ s, ∀ j < N, dist (T^[j] x) (T^[j] y) < ε) ∧
        A * Real.exp ((N : ℝ) * P) ≤ ∑ x ∈ s, Real.exp (orbitSum T φ N x) ∧
        (∑ x ∈ s, Real.exp (orbitSum T φ N x)) ≤ B * Real.exp ((N : ℝ) * P) := by
  classical
  obtain ⟨P, pressureP, A, positiveA, _, _, normalization⟩ :=
    partition_bounds_of_point_specification T c₀ positive₀ expansive φ ε D positiveε coarse bowen specification
  obtain ⟨Q, pressureQ, B, positiveB, upper⟩ := partition_upper_of_point_specification
    T c₀ positive₀ expansive φ (ε / 3) D (by positivity) (by linarith)
    (fun n x y close => bowen n x y (fun j hj => (close j hj).trans_le (by linarith))) specification
  have same : Q = P := EReal.coe_injective (pressureQ.symm.trans pressureP)
  subst Q
  have third : 3 * (ε / 3) = ε := by ring
  simp only [third] at upper
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c₀ positive₀ expansive
  obtain ⟨p, count⟩ := counts ε positiveε
  have finite (N : ℕ) := partitionSum_positive_finite_of_count T φ N p a ε (count N)
  refine ⟨P, pressureP, A / Real.exp D, div_pos positiveA (Real.exp_pos _), B, positiveB, ?_⟩
  intro N positiveN
  obtain ⟨s, nonempty, separated, spans⟩ := exists_separated_spanning T N ε positiveε
    (a ^ (N + p)) (count N)
  refine ⟨s, nonempty, separated, spans, ?_, ?_⟩
  · have cover := partition_le_spanning_weight T φ N ε D positiveε s spans
      (fun x y close => bowen N x y (fun j hj => (close j hj).trans_le (by linarith)))
    have coverReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top cover
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _)
      (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)))] at coverReal
    have total := (normalization N positiveN).1.trans coverReal
    calc
      _ = (A * Real.exp ((N : ℝ) * P)) / Real.exp D := by ring
      _ ≤ (Real.exp D * ∑ x ∈ s, Real.exp (orbitSum T φ N x)) / Real.exp D :=
        div_le_div_of_nonneg_right total (Real.exp_nonneg D)
      _ = _ := mul_div_cancel_left₀ _ (Real.exp_ne_zero D)
  · have below : (∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ N x))) ≤
        separatedPartitionSum T φ univ N ε := by
      unfold separatedPartitionSum
      exact le_iSup_of_le s (le_iSup_of_le separated le_rfl)
    have realBelow := ENNReal.toReal_mono (finite N).2 below
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)] at realBelow
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at realBelow
    exact realBelow.trans (upper N positiveN)

end LeanShared.ThermodynamicDefinitions
