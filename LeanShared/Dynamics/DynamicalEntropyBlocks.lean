module

public import LeanShared.Dynamics.NonInvariantDynamicalEntropy
public import LeanShared.Dynamics.DynamicalEntropyBounds

/-! Actual block decomposition of finite dynamical entropy for an
arbitrary initial probability; no stationarity is assumed. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}
namespace MeasurablePartition

theorem dynamicalEntropy_multiples_le (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ]
    (m q : ℕ) :
    dynamicalEntropy P T μ (q*m) ≤
      ∑ j ∈ Finset.range q, dynamicalEntropy P T (μ.map (T^[j*m])) m := by
  induction q with
  | zero =>
    simpa only [zero_mul,Finset.sum_range_zero,Nat.cast_zero] using (P.dynamicalEntropy_bounds T measurable μ 0).2
  | succ q ih =>
    rw [Nat.succ_mul,Finset.sum_range_succ]
    exact (P.dynamicalEntropy_add_le T μ measurable (q*m) m).trans (add_le_add ih le_rfl)

/-- Only the final incomplete block costs r log k; every full block uses
the actual pushed-forward initial probability. -/
theorem dynamicalEntropy_blocks_le (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ]
    (m q r : ℕ) :
    dynamicalEntropy P T μ (q*m+r) ≤
      (∑ j ∈ Finset.range q, dynamicalEntropy P T (μ.map (T^[j*m])) m) +
      (r : ℝ)*Real.log (k : ℝ) :=
  (P.dynamicalEntropy_add_le T μ measurable (q*m) r).trans
    (add_le_add (P.dynamicalEntropy_multiples_le T measurable μ m q)
      (P.dynamicalEntropy_bounds T measurable (μ.map (T^[q*m])) r).2)

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
