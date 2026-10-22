module
public import LeanShared.Dynamics.PointSpecificationFiniteGibbsLower
public import LeanShared.Dynamics.PointSpecificationSpanningNormalization
public import LeanShared.Dynamics.FiniteGibbsCylinderNormalization

/-! ONE actual sequence of finite spanning Gibbs probabilities has both
uniform upper and lower interior-cylinder estimates. Every finite family,
pressure normalization and seam constant is constructed from compact
expansivity, point specification and Bowen distortion. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 3200000 in
theorem exists_spanning_gibbs_approximations
    (T : X ≃ₜ X) (c₀ : ℝ) (positive₀ : 0 < c₀)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c₀ ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c₀) → x = y)
    (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε) (coarse : 18 * ε ≤ c₀)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 9 * ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ gap : ℕ, 0 < gap ∧
      ∃ Hu > 0, ∃ Hl > 0, ∃ σ : ℕ → ProbabilityMeasure X,
        (∀ N k : ℕ, ∀ z : X, ∀ U : Set X, MeasurableSet U →
          (∀ x ∈ U, ∀ i < k, dist (T^[i] x) (T^[i] z) < ε / 3) →
          ∀ j < N + 1, 0 < j → j + k < N + 1 →
            (σ N : Measure X) ((T^[j]) ⁻¹' U) ≤
              ENNReal.ofReal (Hu * Real.exp (orbitSum T φ k z - (k : ℝ) * P))) ∧
        (∀ N k : ℕ, 0 < k → ∀ z : X, ∀ U : Set X, MeasurableSet U →
          (∀ x, (∀ i < k, dist (T^[i] x) (T^[i] z) < 4 * ε) → x ∈ U) →
          ∀ j < N + 1, gap ≤ j → j + k + gap < N + 1 →
            ENNReal.ofReal (Hl * Real.exp (orbitSum T φ k z - (k : ℝ) * P)) ≤
              (σ N : Measure X) ((T^[j]) ⁻¹' U)) := by
  classical
  obtain ⟨P, pressureP, A, positiveA, _, _, spanning⟩ :=
    normalized_spanning_families_of_point_specification T c₀ positive₀ expansive φ ε D positiveε
      (by linarith) (fun n x y close => bowen n x y (fun j hj => (close j hj).trans_le (by linarith))) specification
  choose s hs separated spans weightLower weightUpper using fun n : ℕ => spanning (n + 1) (by omega)
  let σ (n : ℕ) : ProbabilityMeasure X := by
    let : Nonempty (s n) := (hs n).to_subtype
    exact FiniteAtomicProbability.gibbs (fun x : s n => orbitSum T φ (n + 1) x.val) Subtype.val
  obtain ⟨Q, pressureQ, gap, positiveGap, Hl, positiveHl, lower⟩ :=
    normalized_finite_gibbs_lower_of_point_specification T c₀ positive₀ expansive φ ε D positiveε coarse bowen specification
  have sameQ : Q = P := EReal.coe_injective (pressureQ.symm.trans pressureP)
  subst Q
  obtain ⟨Q, pressureQ, B, positiveB, upper⟩ := partition_upper_of_point_specification
    T c₀ positive₀ expansive φ (ε / 9) D (by positivity) (by linarith)
      (fun n x y close => bowen n x y (fun j hj => by have near := close j hj; linarith)) specification
  have sameQ : Q = P := EReal.coe_injective (pressureQ.symm.trans pressureP)
  subst Q
  have third : 3 * (ε / 9) = ε / 3 := by ring
  simp only [third] at upper
  obtain ⟨alphabet, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c₀ positive₀ expansive
  obtain ⟨p, count⟩ := counts (ε / 3) (by positivity)
  have finite (n : ℕ) := partitionSum_positive_finite_of_count T φ n p alphabet (ε / 3) (count n)
  have prefixBound (n : ℕ) (hn : 0 < n) : separatedPartitionSum T φ univ n (ε / 3) ≤
      ENNReal.ofReal (B * Real.exp ((n : ℝ) * P)) := by
    rw [← ENNReal.ofReal_toReal (finite n).2]
    exact ENNReal.ofReal_le_ofReal (upper n hn)
  let Hu := Real.exp (3 * D) * B ^ 2 / A
  have positiveHu : 0 < Hu := div_pos (mul_pos (Real.exp_pos _) (sq_pos_of_pos positiveB)) positiveA
  refine ⟨P, pressureP, gap, positiveGap, Hu, positiveHu, Hl, positiveHl, σ, ?_, ?_⟩
  · intro N k z U measurable inside j hj positiveJ interior
    let m := N + 1 - (j + k)
    have positiveM : 0 < m := by dsimp [m]; omega
    have total : j + k + m = N + 1 := by dsimp [m]; omega
    let : Nonempty (s N) := (hs N).to_subtype
    have near : ∀ x ∈ (T^[j]) ⁻¹' U, ∀ i < k,
        dist (T^[j + i] x) (T^[i] z) < ε / 3 := by
      intro x hx i hi
      rw [Nat.add_comm j i, Function.iterate_add_apply]
      exact inside (T^[j] x) hx i hi
    have scale : 3 * (ε / 3) = ε := by ring
    have sep : Separated T univ (j + k + m) (3 * (ε / 3)) (s N) := by
      rw [scale, total]
      exact separated N
    have denominator : A * Real.exp (((j + k + m : ℕ) : ℝ) * P) ≤
        ∑ x ∈ s N, Real.exp (orbitSum T φ (j + k + m) x) := by
      rw [total]
      exact weightLower N
    have bound := finite_gibbs_normalized_cylinder T c₀ positive₀ expansive φ (ε / 3) D P A B
      (by positivity) positiveA positiveB.le
      (fun h x y close => bowen h x y (fun i hi => (close i hi).trans_le (by linarith)))
      j k m z (s N) (hs N) sep (prefixBound j positiveJ) (prefixBound m positiveM)
      denominator ((T^[j]) ⁻¹' U) (measurable.preimage (T.continuous.measurable.iterate j)) near
    rw [total] at bound
    exact bound
  · intro N k positiveK z U measurable contains j hj left right
    let n := j - gap
    let m := N + 1 - (j + k + gap)
    have first : n + gap = j := by dsimp [n]; omega
    have mid : k - 1 + 1 = k := by omega
    have total : n + gap + (k - 1) + gap + m + 1 = N + 1 := by dsimp [m]; omega
    let : Nonempty (s N) := (hs N).to_subtype
    have sep : Separated T univ (n + gap + (k - 1) + gap + m + 1) ε (s N) := by
      rw [total]
      exact separated N
    have span : ∀ x : X, ∃ y ∈ s N, ∀ i < n + gap + (k - 1) + gap + m + 1,
        dist (T^[i] x) (T^[i] y) < ε := by
      rw [total]
      exact spans N
    have member : ∀ x, (∀ i < k - 1 + 1, dist (T^[n + gap + i] x) (T^[i] z) < 4 * ε) →
        x ∈ (T^[j]) ⁻¹' U := by
      intro x close
      apply contains (T^[j] x)
      intro i hi
      have near := close i (by omega)
      rw [first, Nat.add_comm j i, Function.iterate_add_apply] at near
      exact near
    have bound := lower n (k - 1) m z (s N) (hs N) sep span ((T^[j]) ⁻¹' U)
      (measurable.preimage (T.continuous.measurable.iterate j)) member
    rw [total, mid] at bound
    exact bound

end LeanShared.ThermodynamicDefinitions
