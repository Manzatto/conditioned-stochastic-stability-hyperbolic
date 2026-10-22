module

public import LeanShared.Dynamics.DynamicalEntropyOffsetBlocks
public import LeanShared.Dynamics.CesaroEntropyConcavity
import Mathlib.Tactic.FieldSimp

/-! The actual Cesaro block entropy estimate used to construct invariant
variational candidates from non-invariant Gibbs orbit probabilities. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
namespace MeasurablePartition

omit [MetricSpace X] [BorelSpace X] in
theorem cesaro_entropy_block_estimate (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (μ : ProbabilityMeasure X)
    (m n : ℕ) (positive : 0 < m) (large : m ≤ n+1) :
    (m : ℝ)*dynamicalEntropy P T (μ : Measure X) (n+1) ≤
      (n+1 : ℝ)*dynamicalEntropy P T (LeanShared.CesaroProbability.measure T μ n) m +
      2*(m : ℝ)*m*Real.log (k : ℝ) := by
  have blocks := P.dynamicalEntropy_averaged_blocks_le T measurable (μ : Measure X) m (n+1) positive large
  have concavity := LeanShared.CesaroProbability.dynamicalEntropy_concavity P T μ n m
  have scaled := mul_le_mul_of_nonneg_left concavity (show (0 : ℝ) ≤ n+1 by positivity)
  rw [←mul_assoc,mul_inv_cancel₀ (show (n+1 : ℝ) ≠ 0 by positivity),one_mul] at scaled
  simp only [ProbabilityMeasure.toMeasure_map] at scaled
  have sum_eq := Fin.sum_univ_eq_sum_range
    (fun j => dynamicalEntropy P T ((μ : Measure X).map (T^[j])) m) (n+1)
  rw [sum_eq] at scaled
  exact blocks.trans (add_le_add scaled le_rfl)

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
