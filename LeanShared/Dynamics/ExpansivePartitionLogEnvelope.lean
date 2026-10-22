module
public import LeanShared.Dynamics.ExpansivePartitionGrowth
public import LeanShared.Dynamics.SeparatedPartitionFiniteness
public import LeanShared.Analysis.EventuallyLinearEnvelope

/-! Actual entropy-energy maximality supplies a global additive logarithmic
partition envelope. The finite exceptional prefix and every partition sum
are handled internally, without a partition growth source. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 1600000 in
theorem partition_log_envelope
    (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (P : ℝ)
    (maximal : ∀ ν : ProbabilityMeasure X,
      MeasurePreserving T (ν : Measure X) (ν : Measure X) →
      (entropy T (ν : Measure X)).toReal + ∫ x, φ x ∂(ν : Measure X) ≤ P)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∀ η > 0, ∃ A : ℝ, ∀ n : ℕ,
      Real.log (separatedPartitionSum T φ univ n ε).toReal ≤ (n : ℝ) * (P + η) + A := by
  obtain ⟨a, _, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positive expansive
  obtain ⟨p, count⟩ := counts ε positiveε
  have finite (n : ℕ) := partitionSum_positive_finite_of_count T φ n p a ε (count n)
  apply EventuallyLinearEnvelope.exists_bound
  intro η positiveη
  have shifted : ∀ᶠ n : ℕ in atTop,
      Real.log (separatedPartitionSum T φ univ (n + 1) ε).toReal ≤ (n + 1 : ℝ) * (P + η) := by
    filter_upwards [eventual_partition_growth T c positive expansive φ P maximal ε η positiveε positiveη]
      with n bound
    have comparison := ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at comparison
    have logarithm := Real.log_le_log (ENNReal.toReal_pos (finite (n + 1)).1 (finite (n + 1)).2) comparison
    rwa [Real.log_exp] at logarithm
  obtain ⟨N, bound⟩ := eventually_atTop.mp shifted
  refine eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
  have estimate := bound (n - 1) (by omega)
  have index : n - 1 + 1 = n := by omega
  have castIndex : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast index
  simpa only [index, castIndex] using estimate

end LeanShared.ThermodynamicDefinitions
