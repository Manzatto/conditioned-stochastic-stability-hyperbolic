module

public import LeanShared.Dynamics.ExpansiveUniformGibbsBound

/-! Actual entropy-energy maximality bounds the full separated partition
supremum eventually, uniformly over all finite separated sets. The finite
Gibbs variational and compactness arguments are already proved internally. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem eventual_partition_growth
    (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (P : ℝ)
    (maximal : ∀ ν : ProbabilityMeasure X,
      MeasurePreserving T (ν : Measure X) (ν : Measure X) →
      (entropy T (ν : Measure X)).toReal + ∫ x, φ x ∂(ν : Measure X) ≤ P)
    (ε η : ℝ) (positiveε : 0 < ε) (positiveη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, separatedPartitionSum T φ univ (n + 1) ε ≤
      ENNReal.ofReal (Real.exp ((n + 1 : ℝ) * (P + η))) := by
  classical
  filter_upwards [eventual_uniform_separated_free_energy T c positive expansive φ P
    maximal ε η positiveε positiveη] with n bound
  unfold separatedPartitionSum
  refine iSup_le fun s => iSup_le fun hs => ?_
  by_cases nonempty : s.Nonempty
  · have energy := (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mp (bound s nonempty hs)
    have positiveSum : 0 < ∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x) :=
      Finset.sum_pos (fun x _ => Real.exp_pos _) nonempty
    have comparison := ENNReal.ofReal_le_ofReal ((Real.log_le_iff_le_exp positiveSum).mp energy)
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)] at comparison
    simpa only [mul_comm] using comparison
  · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty, Finset.sum_empty]
    exact bot_le

end LeanShared.ThermodynamicDefinitions
